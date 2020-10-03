#!/usr/bin/env python3
# encoding: utf-8

#---------|---------|---------|---------|---------|---------|---------|---------|
# Copyright (C) 2018 Raul Roda <raulroda@yahoo.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
#---------|---------|---------|---------|---------|---------|---------|---------|


#
# Este proyecto permite dibujar borneros partiende de un esquema del software QElectrotech.
# Los borneros dibujados se añaden a la sección xml del fichero .qet: 
#  <collection>
#    <category name="import">
#
#
# Se buscan todos los bornes en el esquema. Los bornes son elementos del tipo TERMINAL. 
# Además deben tener un 'label' de tipo X1:3. 
#
#
# Hay configuración que afecta a cada borne y otra que afecta a todo el bornero.
# Toda la configuración se guarda en el campo 'function' de cada elemento de QET.
# Ese campo es accesible desde <elementInformation name="function"> de cada borne. 
# La configuración se guarda como una cadena de texto, con unos TAGS que sirven
# para identificar cada uno de los parámetros.
#   Ejemplo:
#       <elementInformation name="function">
#           %p2%tSTANDARD%c%n%b
#       </elementInformation>    
# Todos los bornes de un mismo bornero, tiene la misma configuración arriba
# mencionada, de forma que si se borra un borne  quedará algun otro borne de ese
# bornero del que extraer la configuración
#
#
#
# La info leida para cada borne se almacen en la variable global 'data'.
# Esta variable tiene un key para cada bornero y luego una lista con la config
# de cada terminal. La variable 'data' tambien tendra una variable de tipo
# 'tk' que nos permitirá enlazar con el valor de los widgets del GUI
#   {
#       borne_id1: [ {term1}, {term2}, ... ]
#       borne_id2: [ {term1}, {term2}, ... ]
#       borne_id3: [ {term1}, {term2}, ... ]
#   }
# Para cada terminal hay configuración propia y configuración del bornero entero.
# En la siguiente lista se muestran las variables que enlazan con los TK widgets
# y  el TAG con el que se guarda cada valor en el XML del esquema. 
#   {
#     'uuid': From QET. identificador of the terminal in the QET xml file,
#     'block_name': From QET.terminal block that belong the terminal,
#     'terminal_name': From QET.
#     'terminal_xref': Calculated from QET,
#     'cable': From QET,
#
#     'terminal_pos %p': From Plugin. For sortering purposes,
#     'terminal_type %t': From Plugin. STANDARD, GROUND, FUSE. For representing purposes,
#     'hose %h': From Plugin. Name of the cable of the electric hose,
#     'conductor %n': From Plugin. Name of the electric hose,
#     'bridge %b: From Plugin. True/False for a bridge to next terminal
#     'num_reserve %r': Config for entire terminal block. Num of reserve terminals
#     'reserve_positions %z': Config for entire terminal block. Position for the
#           reserve terminals. Not used for now
#     'size %s': number of terminals per page
#   }
#
#
# Los borneros creados en el XML del esquema QET se nombran según TB_x##y.elmt
# donde:
#   x: es el nombre del bornero (X1, X34, -XL3,...)
#   y: es un número direfente para el mismo bornero que se he troceado para que
#      quepa en una página.



# PARA CREAR NUEVA COLUMNA EN LA TABLA
# - QETProject: documentar la clase
# - documentar en comentar init_ui
# - añadir nueva columna en GRID_CONFIG
# - definir la funcion callback si la columna permite clicks
# - Insertar tag para almacenar info en el elemento de QET: getElementMetadata
# - Modificar : get_list_of_used_terminals
# - Modificar: save_tb
# - Modificar last_trmnl en drawTerminalBlock. Añadir funciones de dibujo 
#   si la columa lo requiere
# - Modificar click_on_reorder si la columna afecta a la ordenacion



## Imports
import logging as log
import os
import re
import shutil
import sys
import tkinter as tk
from collections import OrderedDict
from functools import cmp_to_key
#~ import lxml.etree as etree  # python3-lxml
from operator import itemgetter as i
from tkinter import filedialog, messagebox, ttk

from src.qetproject import QETProject
from src.terminalblock import TerminalBlock




## Globals (allows access from callbacks events)
frmFoot = None  # the bottom widget of GUI to show info
qet_project = None  # class to manage QET_Projects
qet_file = ''  # full path of the QET file
qet_terminals = []  # list of terminals and its config
wdg_data = {}
selection = []  # stores checkboxes selected to dray terminal blocks


# CONSTANTS
VERSION = '1.1.7'
FECHA = 'September, 2020'
STRIP_LONG = 30
BG_COLOR = "#F0F0F0"  # background color 
txt = {
0:
"""
To change terminals order:
  - Left click on a number in POS. column to decrement
  - Right click on a number in POS. column to increment.
To edit BRIDGE and TYPE, just right click on the cell.
""", \
1: 
"""
Steps to follow.
  - In QET, optional: Choose Project> Clean Project.
  - In QET:  Close and reopen the project.
  - In QET: Start the plugin. Choose 'Start the terminal block creation plug-in' in the project menu.
  - In this plug-in: Edit the terminal blocks (described below).
  - In this plug-in: Press the 'CREATE TERMINAL BLOCKS' button.
  - In this plug-in: In the pop-up screen, choose the terminal blocks you want to create / update.
  - In this plug-in: Close 
  - In QET:  Close without saving project (very important) and reopen the project.
  - In QET: Under the 'COLLECTIONS' tree of the project, all the terminal blocks appear.

Considerations for creating a terminal block from a diagram.
  - This addon searches all the elements of type 'Terminal'.
  - Normally, the terminal elements appear in the filter of the QET collection by 'terminal block'.
  - Terminals must have a tag such as <terminal_block_name>: <terminal_name>. For example: -X1: 1, X34: +, X1: 23, Y3: R, ...
  - All terminals with the same <terminal_block_name> are grouped and displayed in a tab in this add-on.
  - In the add-on, for each terminal block, you can specify how many terminals fits per page and the number of reserve terminals.
  - The terminals are sorted by default, however the order can be modified.
  - You can also specify the hose and the conductor connected at the bottom of every terminal (columns 'HOSE' and 'CONDUCTOR').
  - There are 3 types of terminals that you can specify in the 'TYPE' column (standard, ground, fuse)
  - The 'BRIDGE' column indicates if there is a bridge from the current to the next terminal.

How to use:
  - To change the order of the terminals in the terminal block, just left-click or right-click
    on the corresponding number of 'POS.' column.
  - By right-clicking on the cells of the TYPE and HOSE columns, it will alternate betwenn all possible values.
  - For each block of terms:
    - You can specify how many terminals per page you will draw.
    - the number of reserve terminals that are drawn at the end.

          
Created by raulroda8@gmail.com ({})
""".format(FECHA)

}

GRID_CONFIG = [
    {'title': 'POS.', 'width': 8},
    {'title': 'TERM.', 'width': 10},
    {'title': 'XREF', 'width': 14},
    {'title': 'CABLE', 'width': 12},
    {'title': 'BRIDGE', 'width': 8},
    {'title': 'TYPE', 'width': 12},
    {'title': 'HOSE', 'width': 14},
    {'title': 'CONDUCTOR', 'width': 12}
]


class ScrollableFrame(ttk.Frame):
    def __init__(self, container, *args, **kwargs):
        super().__init__(container, *args, **kwargs)
        canvas = tk.Canvas(self)
        scrollbar = ttk.Scrollbar(
            self, orient="vertical", command=canvas.yview)
        self.scrollable_frame = ttk.Frame(canvas)

        self.scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(
                scrollregion=canvas.bbox("all")
            )
        )

        canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")

        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        

def createGUI(root):
    """Create the main window
    @param root: main window"""
    # define main window

            
def right_on_field(wdg_clicked, wdg_autofill):
    """establecemos el texto del campo auto-fill"""
    val = wdg_autofill['text']
   
    wdg_clicked.delete(0, "end")
    wdg_clicked.insert(0, val)
    if val.isdigit():
        wdg_autofill['text'] = str( int(wdg_autofill['text']) + 1)


def return_on_field(wdg_clicked, wdg_autofill):
    """actualizamos auto-fill tras edicion"""
    val = wdg_clicked.get()
    if val.isdigit():
        wdg_autofill['text'] = str( int(val) + 1)
    else:
        wdg_autofill['text'] = str(val)


def right_on_pos(event):
    """Increments the position by  5"""

    val = event.widget.get()
    if val.isdigit():
        event.widget.delete(0, "end")
        event.widget.insert(0, str(int(val) + 5))


def increment_on_pos(event):
    """ Increment One position the current row. 
    Since the values range from 10 to 10, the value increases by 15.
    Later calls the reorder function. """

    val = event.widget.get()
    new_pos = int(val) + 15

    event.widget.config(state='normal')
    event.widget.delete(0, "end")
    event.widget.insert(0, str(new_pos))
    event.widget.config(state='disabled')

    click_on_reorder(event)


def decrement_on_pos(event):
    """ Decrement One position the current row
    Changes the number in the POSITION columns and reorder """

    val = event.widget.get()
    if int(val) > 15:
        new_pos = int(val) - 15
        event.widget.config(state='normal')
        event.widget.delete(0, "end")
        event.widget.insert(0, str(new_pos))
        event.widget.config(state='disabled')

    click_on_reorder(event)


def right_on_bridge(event):

    loop = {'|': '', \
            '': '|'}
    val = event.widget.get()
    event.widget.delete(0, "end")
    event.widget.insert(0, loop[val])


def right_on_type(event):
    loop = {'STANDARD': 'GROUND', \
            'GROUND': 'FUSE', \
            'FUSE': 'STANDARD'}
    val = event.widget.get()

    event.widget.delete(0, "end")
    event.widget.insert(0, loop[val])


def num_reserve_changed(*args):
    """Prevision for future realtime reserve terminals editing"""
    pass


def click_on_create_tb(event):
    """ Shows a window to select what terminals to create"""

    global qet_terminals
    global selection

    
    # Array with blocks usand and TK variables
    selection = []
    blocks = list(OrderedDict.fromkeys([x['block_name'] for x in qet_terminals]))
    for block in blocks:
        selection.append( {'label':block, 'check':tk.BooleanVar()})

    # Generate choose window
    choose_window = tk.Toplevel()
    choose_window.wm_title("Choose...")
    
    tk.Label(choose_window, text="Choose terminal blocks to generate", \
                justify='left').grid(row=0, column=0, columnspan=5, padx=4, pady=4)
    
    # Create the array of textboxes
    r = 1
    c = 0
    for bk in selection:
        tk.Checkbutton(choose_window, text=bk['label'], variable=bk['check']).\
                grid(row=r, column=c, padx=4, pady=4)
        c+=1
        if c == 11: 
            r+=1
            c=0
    
    b1 = tk.Button(choose_window, text='ACCEPT')
    b1.grid(row=r+2, column=0, columnspan=2, padx=4, pady=4)
    b1.bind("<Button-1>", click_on_choose)


def backup_diagram():
    """ Backup the diagram WET file to a new filename adding a increment
    suffix"""

    # find new backup filename
    i = 1
    full_back_path = qet_file[:qet_file.rfind('.')] + '_' + str(i) + '.qet' 
    while os.path.isfile( full_back_path) or \
            os.path.isdir( full_back_path ) :
        i += 1
        full_back_path = qet_file[:qet_file.rfind('.')] + '_' + str(i) + '.qet' 
    
    # backup    
    shutil.copyfile(qet_file, full_back_path)
    return full_back_path


def click_on_choose(event):
    """Event ACCEPT button in the windows to choose wich terminal blocks.
    Inserts terminal block into XML structure for the selected blocks.
    Extracts data from gui to create a Terminal Block with the correct size.
    Saves project."""

    global wdg_data
    global qet_file
    global frmFoot
    global qet_project
    global selection

    ## close choose window
    event.widget.master.destroy()

    ## Loop selected blocks. Extract data from gui for a every terminal block
    tb_selected = [x['label'] for x in selection if x['check'].get() == True]
    if tb_selected:
        progress_label = tk.Label(frmFoot, font=('Helvetica', 12, 'bold '), fg='red',  \
                text='                GENERATING TERMINAL BLOCKS...               ')
        progress_label.grid(row=1, columnspan=8)
        full_back_path = backup_diagram()
        
        # sorting 
        click_on_reorder(event)  # this updates wdg_data if necessary
        data_from_ui = convert_from_control_var()

    ## generate splited terminal blocks
    for tb in tb_selected:  # selected

        full_tb = [x for x in data_from_ui if x['block_name'] == tb]

        # copy the parameters of the Terminal Block to every terminal of the block.
        # Is important i any terminal is deleted in the diagram
        for t in full_tb:
            t['num_reserve'] = full_tb[0]['num_reserve']
            t['reserve_positions'] = full_tb[0]['reserve_positions']
            t['size'] = full_tb[0]['size']

        # adding the reserve terminals at the end using the last existing one
        #uuidly.uuid1().urn[9:]
        num_reserve = int(full_tb[0]['num_reserve'])

        # new_terminal = subset.copy()  # if not links to the original
        new_terminal={}
        new_terminal['uuid'] = ''
        new_terminal['block_name'] = full_tb[-1]['block_name']
        new_terminal['terminal_name'] = 'res'
        new_terminal['terminal_xref'] = ''
        new_terminal['cable'] = ''
        new_terminal['terminal_pos'] = str(int(full_tb[-1]['terminal_pos']) + 10)
        new_terminal['terminal_type'] = 'STANDARD'
        new_terminal['hose'] = ''
        new_terminal['conductor'] = ''
        new_terminal['bridge'] = ''
        new_terminal['num_reserve'] = full_tb[-1]['num_reserve']
        new_terminal['reserve_positions'] = full_tb[-1]['reserve_positions']
        new_terminal['size'] = full_tb[-1]['size']
        full_tb = full_tb + num_reserve * [new_terminal]
  
        
        # calc num of Terminal Blocks to draw. If 0 force all.
        conf_split_size = int(full_tb[0]['size'])
        split_size = conf_split_size if conf_split_size > 0 else len(full_tb)
        
        # splitting and drawing
        segment = []  # a slice of the tb to fit on a page.
        num_of_segment = 1  # to naming the terminal block
        a_tb= full_tb.copy()  # a copy because popping from a_tb
        for _ in range(len(a_tb)):
            if len(a_tb):
                segment.append(a_tb.pop(0))  # incrementing tb segment
            if len(segment) == split_size:  # time to draw
                # Label numering only if more than one
                print("Drawing a segment of {}({}) block with {} terminals" \
                        .format(tb, num_of_segment, len(segment)))

                # creates XML element file
                a_block = TerminalBlock( "{}({})". \
                        format(tb, num_of_segment), segment)
                qet_project.insert_tb(\
                    "{}({})".format(tb, num_of_segment), \
                     a_block.drawTerminalBlock())
                segment =[]
                num_of_segment += 1
        
        # draw the last segment(if not full split size)
        # or the first (if there's only one)
        if len(segment):
            print("Drawing last segment of {}({}) block with {} terminals" \
                    .format(tb, num_of_segment, len(segment)))
            if split_size >= len(full_tb):  # No numbered label if only one
                tb_label = str(tb)
            else:
                tb_label = "{}({})".format(tb, num_of_segment)
            a_block = TerminalBlock( tb_label, segment )
            qet_project.insert_tb( tb_label, a_block.drawTerminalBlock() )
            
        # save plugin config into termials
        qet_project.update_termials(full_tb)

    # save and messaging
    if tb_selected:
        qet_project.save_tb(qet_file)
        messagebox.showinfo("QET", "Original diagram file saved as \n\n{}". \
            format(full_back_path))

    ## removing progres text
    progress_label.destroy()

    ## close choose window
    event.widget.master.destroy()

    
            
def click_on_reorder(event):
    """Re-sort data according the data edited by the user in the ui
    """    
    global wdg_data

    
    ## Converting to number, sorting  and converting to a widgets dicc
    data_from_ui = convert_from_control_var()
    data_sorted = sort_terminals(data_from_ui)

    # Put data again in entry widgets
    for row in range(len(data_sorted)):
        for key in data_sorted[row].keys():
            wdg_data[row][key].set(data_sorted[row][key])
            
  

def sort_terminals(data):
    """Terminals are sorter by: block_name, terminal_pos, cable, 
    cable_cond, terminal_name.
    After sorting, renumbers the terminal_pol cols.
    @param data: lista de diccionarios con los datos de los terminales.
    """
    ret = []
    
    # convert values to int
    data = convert_numerical(data)
    
    # sorting
    terms = list(OrderedDict.fromkeys([x['block_name'] for x in data])) # no dupl.
    for t in terms:
        tb = [x for x in data if x['block_name'] == t]
        tb_sorted = multikeysort(tb, \
                ['terminal_pos', 'hose', 'conductor', 'terminal_name'])

        # renumbering terminal pos. Every terminal block starts with 1.
        for i in range(len(tb_sorted)):
            tb_sorted[i]['terminal_pos'] = (i+1) * 10

        ret += tb_sorted
    
    return ret


def to_int(data):
    try: 
        int(data)
        return int(data)
    except ValueError:
        return data


def convert_numerical(data):
    """Convert string values to integers. This allows 'more intelligent'
    sorting. Discards + and - signs, because are used naming terminals
    """
    regex_digits = r'^(\d+)$'
    for ter in data:
        if re.search(regex_digits, ter['terminal_name']):
            ter['terminal_name'] = int(ter['terminal_name'])
        if re.search(regex_digits, ter['terminal_pos']):
            ter['terminal_pos'] = int(ter['terminal_pos'])
        if re.search(regex_digits, ter['hose']):
            ter['hose'] = int(ter['hose'])
        if re.search(regex_digits, ter['conductor']):
            ter['conductor'] = int(ter['conductor'])
    return data


def cmp(a, b):
    """Returns 0, 1(a>b) or  -1(a<b)
    """
    
    if type(a) == type(b):
        return (a > b) - (a < b)
    elif (type(a) is int) and (type(b) is str):
        return -1
    elif (type(b) is int) and (type(a) is str):
        return 1


def multikeysort(items, columns):
    """ Sort list of dict using diferent keys. From
    https://stackoverflow.com/questions/1143671/
    python-sorting-list-of-dictionaries-by-multiple-keys
    @param items: dict to sort
    @param colums: list with keys names of dict
    """
    comparers = [
        ((i(col[1:].strip()), -1) if col.startswith('-') else (i(col.strip()), 1))
        for col in columns
    ]
    def comparer(left, right):
        comparer_iter = (
            cmp(fn(left), fn(right)) * mult
            for fn, mult in comparers
        )
        return next((result for result in comparer_iter if result), 0)
    return sorted(items, key=cmp_to_key(comparer))


def drawTerminalRow(frmTable, tab_row, wdg_data_index):
    """ Generates the widgets of a terminal. There are a tab for
    every terminal block
    
    @param frmTable: the fathe frame that the widgets belongs
    @param tab_row: index correponding the the row number.
    @param wdg_data_index: index corresponding to the wdg_array to linking.

    @return: none. The widgets are inserted directly to the frame."""

    global GRID_CONFIG

    offset = 1  # row 0 is the head
 
    # POS column
    lbl = tk.Entry(frmTable, borderwidth=0, width=GRID_CONFIG[0]['width'],
                    justify='center', fg='red', bg=BG_COLOR,
                    textvariable=wdg_data[wdg_data_index]['terminal_pos'],
                    relief="solid")
    lbl.config(state='disabled')
    lbl.grid(row=tab_row+offset, column=0)
    lbl.bind("<Button-1>", decrement_on_pos)
    lbl.bind("<Button-3>", increment_on_pos)  # right click in Win & Lin. In Mac is middle button
    lbl.bind("<Button-2>", increment_on_pos)  # right click in Mac

    # TERMINAL NAME (ID) colum
    lbl = tk.Entry(frmTable, borderwidth=0, width=GRID_CONFIG[1]['width'],
                    justify='center',
                    textvariable=wdg_data[wdg_data_index]['terminal_name'],
                    relief="solid")
    lbl.config(state='disabled', disabledforeground='black',
                disabledbackground='gray70')
    lbl.grid(row=tab_row+offset, column=1)

    # TERMINAL XREF colum
    lbl = tk.Entry(frmTable, borderwidth=0, width=GRID_CONFIG[2]['width'],
                    justify='center',
                    textvariable=wdg_data[wdg_data_index]['terminal_xref'],
                    relief="solid")
    lbl.config(state='disabled', disabledforeground='black',
                disabledbackground='gray70')
    lbl.grid(row=tab_row+offset, column=2)

    # CABLE colum
    lbl = tk.Entry(frmTable, borderwidth=0, width=GRID_CONFIG[3]['width'],
                    justify='center',
                    textvariable=wdg_data[wdg_data_index]['cable'],
                    relief="solid")
    lbl.config(state='disabled', disabledforeground='black',
                disabledbackground='gray70')
    lbl.grid(row=tab_row+offset, column=3)

    # BRIDGE column
    lbl = tk.Entry(frmTable, borderwidth=0, width=GRID_CONFIG[4]['width'],
                    justify='center', fg='blue', bg=BG_COLOR,
                    textvariable=wdg_data[wdg_data_index]['bridge'],
                    relief="solid")
    lbl.grid(row=tab_row+offset, column=4)
    lbl.bind("<Button-3>", right_on_bridge)
    lbl.bind("<Button-2>", right_on_bridge)

    # TERMINAL TYPE column
    lbl = tk.Entry(frmTable, borderwidth=0, width=GRID_CONFIG[5]['width'],
                    justify='center', fg='blue', bg=BG_COLOR,
                    textvariable=wdg_data[wdg_data_index]['terminal_type'],
                    relief="solid")
    lbl.grid(row=tab_row+offset, column=5)
    lbl.bind("<Button-3>", right_on_type)
    lbl.bind("<Button-2>", right_on_type)

    # HOSE column
    lbl = tk.Entry(frmTable, borderwidth=0, width=GRID_CONFIG[6]['width'],
                    justify='center', fg='blue', bg=BG_COLOR,
                    textvariable=wdg_data[wdg_data_index]['hose'],
                    relief="solid")
    lbl.grid(row=tab_row+offset, column=6)

    # HOSE column
    lbl = tk.Entry(frmTable, borderwidth=0, width=GRID_CONFIG[7]['width'],
                    justify='center', fg='blue', bg=BG_COLOR,
                    textvariable=wdg_data[wdg_data_index]['conductor'],
                    relief="solid")
    lbl.grid(row=tab_row+offset, column=7)


def initUI(root):
    """Creates the UI
    param root: root frame
    param data: list of a dictionary for every terminal
      {uuid, block_name, terminal_name, terminal_pos, 
            terminal_xref, terminal_type, conductor_name,
            cable, cable_cond, bridge}
    """
    global frmFoot
    global wdg_data
    global qet_terminals

    ## config root window
    root.title("QET - Terminal block generator - v{}".format(VERSION))
    root.resizable(True, True)  # width, height
    # screen_height = str(root.winfo_screenheight() - 200)
    # root.geometry("800x" + screen_height)  # width, height
    root.resizable(True, True)  # width, height

    ## Form Header
    frmHeader = tk.Frame(root, borderwidth=1, relief='solid')
    tk.Label(frmHeader, text=txt[0], justify='left', fg='red') \
            .pack(side='left', padx=2, pady=2)

    b1 = tk.Button(frmHeader, text='CREATE TERMINAL BLOCKS')
    b1.pack(side='right')
    b1.bind("<Button-1>", click_on_create_tb)

    # b2 = tk.Button(frmHeader, text='SORT')
    # b2.pack(side='right')
    # b2.bind("<Button-1>", click_on_reorder)

    
    # TABS. Every tab has a frame with 2 frames inside (frmConfig and frmTable)
    tabs = ttk.Notebook(root)  # populates 'segment' field
    blocks = list(OrderedDict.fromkeys([x['block_name'] for x in qet_terminals])) 
    wdg_data_index = 0

    for block in blocks:
        
        ## Tab frame
        frmTab = tk.Frame(tabs)

        ## top config for every Terminal block tab
        frmConfig = tk.Frame(frmTab)
        frmConfig.pack(fill=tk.X, padx=10, pady=10)

        tk.Label(frmConfig, text='Number of reserve terminals:') \
                .grid(row=0, column=0, sticky=tk.W)
        lblReserve = tk.Entry(frmConfig, borderwidth=0, width = 6, \
                textvariable = wdg_data[wdg_data_index]['num_reserve'], \
                relief="solid")
        lblReserve.grid(row=0, column=1)
        lblReserve.bind("<FocusOut>" , num_reserve_changed)
        lblReserve.bind("<Return>" , num_reserve_changed)
        # wdg_data[wdg_data_index]['num_reserve'].trace("w", num_reserve_changed)

        tk.Label(frmConfig, text='Terminals per page:') \
                .grid(row=1, column=0, sticky=tk.W)
        tk.Entry(frmConfig, borderwidth=0, width = 6, \
                textvariable = wdg_data[wdg_data_index]['size'], \
                relief="solid") \
                .grid(row=1,column=1)


        ## table frame
        # frmTable = tk.Frame(frmTab)
        frmTable = ScrollableFrame(frmTab)
        frmTable.pack(fill=tk.BOTH, expand=1)


        # table column titles
        for column in range(len(GRID_CONFIG)):
            tk.Label(frmTable.scrollable_frame, text=GRID_CONFIG[column]['title'],
                    width = GRID_CONFIG[column]['width'], \
                    font=('Helvetica', 10, 'bold underline')) \
                    .grid(row=0, column=column)
        
        terminals = [x for x in qet_terminals if x['block_name'] == block]  # choose a terminal block

        # body: terminals rows
        for i in range(len(terminals)):
            drawTerminalRow(frmTable.scrollable_frame, i, wdg_data_index)
            wdg_data_index += 1
        tabs.add(frmTab, text=block)

    ## Help tab
    frmInfo = tk.Frame(tabs)
    tk.Label(frmInfo, text=txt[1], justify='left').pack(padx=8)
    tabs.add(frmInfo, text='Help')

    ## frame foot
    frmFoot = tk.Frame(root, borderwidth=1, relief='solid')
        
    ## Packing
    frmHeader.pack(anchor='n', fill='x', expand='True', pady=6, padx=6)
    tabs.pack(fill='x', expand=1,pady=6, padx=6)
    frmFoot.pack(anchor='s', fill='x', expand='True', pady=6, padx=6)

    ## Bottom Label recording save qet project before
    info_label = tk.Label(frmFoot, font=('Helvetica', 10, 'bold '), fg='red',  \
            text='Remember to SAVE the QET project before using this plug-in.')
    info_label.grid(row=1, columnspan=8)
    
    
def get_QET_path(wdg_root):
    """Returns the QET project file from command line or file dialog"""

    ## Get QET path from command line or show dialog to choose one.
    if len(sys.argv) == 1:  # first data is the prg name
        ftypes = [('QET', '*.qet'), ('All files', '*')]
        dlg = filedialog.Open(wdg_root, filetypes = ftypes)
        fl = dlg.show()

        if fl != '':
            return fl
    else:
        log.info('Using the argument passed: {}({})'.format(sys.argv, len(sys.argv)))
        return sys.argv[1]


def convert_to_control_var(data_array):
    """Converts an array of lists to a control variables array to easy
    access to/from UI widgets"""
    ret = []
    for r in range(len(data_array)):
        a_row = {}
        for key in data_array[r].keys():
            a_row[key] = tk.StringVar(value=data_array[r][key])
        ret.append(a_row)

    return ret
    
    
def convert_from_control_var():
    """Converts an array of lists of control variables to its values.
    @ param global wdg_data: global variable that hosts widgets data
    """
    global wdg_data
    
    ret = []
    for r in range(len(wdg_data)):
        a_row = {}
        for key in wdg_data[r].keys():
            a_row[key] = wdg_data[r][key].get()
        ret.append(a_row)
    return ret
    

def initialize_logger():
    logger = log.getLogger()
    logger.setLevel(log.DEBUG)
     
    # console
    handler = log.StreamHandler()
    handler.setLevel(log.DEBUG)
    formatter = log.Formatter( \
            '%(asctime)s %(levelname)-8s %(message)s [%(module)s.%(funcName)s:%(lineno)i]', '%H:%M:%S')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
 
    # error file
    #handler = log.FileHandler(os.path.join(output_dir, "error.log"),"a", encoding=None, delay="true")
    #handler.setLevel(log.ERROR)
    #formatter = log.Formatter("%(asctime)s %(levelname)-8s %(message)s [%(module)s.%(funcName)s:%(lineno)i]")    
    #handler.setFormatter(formatter) 
    #logger.addHandler(handler)
 
    # log file
    #handler = log.FileHandler(os.path.join(output_dir, "all.log"),"a")
    #handler.setLevel(log.INFO)
    #formatter = log.Formatter("%(asctime)s %(module)-12s %(levelname)-8s %(message)s")
    #handler.setFormatter(formatter)
    #logger.addHandler(handler)




def main():
    global qet_project
    global wdg_data  
    global qet_file
    global qet_terminals
    
    
    # Sistema de log
    initialize_logger()
    log.info ('** QElectrotech terminal block plug-in - v{} **'.format(VERSION))


    ## UI Root
    wdg_root = tk.Tk()
    
    ## Get QET path from command line or show dialog to choose one.
    qet_file = get_QET_path(wdg_root)
    
    
    ## QET Project
    qet_project = QETProject(qet_file)  # allows working with a QET XML file.
    qet_terminals = qet_project.get_list_of_used_terminals()
    qet_terminals = sort_terminals(qet_terminals)

    ## List of diccs. Keys: block_name, bridge, cable, cable_cond, conductor_name,
    ##   terminal_name, terminal_pos, terminal_type, terminal_xref, uuid.
    ## New reserve terminals will be add here with no 'uuid'
    wdg_data = convert_to_control_var(qet_terminals)
    
    ## UI
    initUI(wdg_root)
    
    ## main loop
    wdg_root.mainloop(  )


if __name__ == '__main__':
    main()
