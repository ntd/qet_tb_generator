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
# - Modificar print_tb para depuracion
# - Modificar click_on_reorder si la columna afecta a la ordenacion

## Imports
from collections import OrderedDict
from functools import cmp_to_key
#~ import lxml.etree as etree  # python3-lxml
from operator import itemgetter as i
import os
import re
import shutil
import sys
import tkinter as tk
from tkinter import filedialog 
from tkinter import messagebox
from tkinter import ttk
import uuid as uuidly
import xml.etree.ElementTree as etree  # python3-lxml


## Globals (allows access from callbacks events)
frmFoot = None  # Has the auto-fill info
qet_project = None  # class to manage QET_Projects
qet_file = ''  # full path of the QET file
data = None  # Has the terminals info of the project.
config = {}  # Has de config tab selections


# CONSTANTS
VERSION = '1.0.16'
DEBUG = False
STRIP_LONG = 30
txt = {
    0: "- Columns POS., TYPE, BRIDGE, CABLE and CABLE COND. are editable.\n- Right click to fast filling.", \
    1: "    If checkbox is selected, a backup of the original QET will be generated.", \
    2: '    If checkbox is not selected, a new QET file will be generated adding the extension "qet".', \
    3: 
"""
Steps to use.
  - In QET, save the project.
  - Start the plugin. Choose 'Launch the terminal block creation plugin' in the project menu.
  - Edit the terminal blocks (decribed below).
  - Press the button 'CREATE TERMINAL BLOCKS' of the Plugin and returns to QET.
  - Close the project discarding changes and reopen it.
  - Under the 'COLLECTIONS' tree of the project, appears all terminal blocks.

Considerations for creating a Terminal Block from a diagram.
  - This plug-in searches for all elements of type 'Terminal'. 
  - Normally the terminal elements appears in the QET collection filtering by 'terminal block'.
  - The terminals must have a label like <terminal_block_name>:<terminal_name>. For example: -X1:1, X34:+, X1:23, Y3:R,...
  - All the terminals with the same <terminal_block_name> are grouped and are showed into a tab in this plug-in.
  - If there are a lot of terminals, are splited into diferent terminal block (tabs) to fit in a diagram page.
  - The terminals are sorted by default, however the order can be altered writing a value into the 'POS.' column.
  - Also you can specify the cable and conductor that the terminal belongs (columns 'CABLE' and 'CABLE COND.').
  - There are 3 types of terminals you can specify in the 'TYPE' column.
  - The bridge column indicates a bridge from current to the next terminal.
        
How to use:
  - To edit a cell, <Left click> in that cell.
  - For faster filling, <Right click> in a cell, and auto-fills it with the value showed at the bottom of the colum.
  - Pressing <Return> after editing a cell, refreshs the auto-fill.
          
Created by raulroda@yahoo.com
"""
}


class QETProject:
    """This class works with the XML source file of a QET Project.
    The list of terminals has dicts like:
        {uuid, block_name, segment, terminal_name, terminal_pos, 
        terminal_xref, terminal_type, conductor_name, cable, cable_cond} 
    where:
      - uuid: identificador of the terminal in the QET xml file.
      - block_name: terminal block that belong the terminal.
      - segment: to fit in a page, a terminal block is splitted.
      - terminal_name: comes from the diagram
      - terminal_pos: position. Specified in the plugin. For sorterin purposes.
      - terminal_xref: location calculated of the element.
      - terminal_type: STANDARD, GROUND, FUSE. For representing purposes.
      - conductor_name: Name of the electric hose.
      - cable_cond: name of the cable of the electric hose.
      - bridge: True/False for a bridge to next terminal
    """

    # class attributes
    QET_COL_ROW_SIZE = 25  # pixels offset for elements coord
    DEBUG = False


    def __init__(self, project_file, fromPage='', \
            toPage = '', searchImplicitsConnections = False):
        """class initializer. Parses the QET XML file.
        @param project_file: file of the QET project
        @param folio_reference_type: how to calc XRefs when recover project info:
           'A' auto. Same xref as configured in the QET diagram project.
           'D' default (%f-%l%c) i.e. 15-F4
        @param fromPage: first page in range to be processed
        @param toPage: last page in range to be processed
        @param searchImplicitsConnections: True for search implicit connections in TB creation"""

        self._qet_tree = etree.parse(project_file)

        self.qet_project_file = project_file
        self.qet_project = self._qet_tree.getroot()
        
        # determine xref format to use or default

        self.folio_reference_type = self.qet_project.find('.//newdiagrams'). \
                find('report').attrib['label']

        # XML version
        self.xml_version = self.qet_project.attrib['version']

        # pageOffset for folio numbers
        self.pageOffset = int (self.qet_project.attrib
                ['folioSheetQuantity'])  # offset table of contents

        # general project info
        self._totalPages = len (self.qet_project.findall('.//diagram')) + \
                self.pageOffset

        # elements type of terminal
        self._terminalElements = self._getListOfElementsByType( 'terminal' )


    def _getListOfElementsByType(self, element_type):
        """Return a list of component in library(collection) that
        have 'link_type' as element_type parameter.

        @return [] list with el names of elements that
                   are terminal as 'like_type'"""

        ret = []  # return list

        for element in self.qet_project.find('collection').iter('element'):
            definition = element[0]
            if 'link_type' in definition.attrib:
                if definition.attrib['link_type'] == element_type:
                    ret.append(element.attrib['name'])

        return list(set(ret))  # remove duplicates


    def _getElementName (self, element):
        """Returns the name of a terminal element.
        The name comes from 'dynamic_text' section.
        If not exists, the name is specified in elementInformation/label or 
        elementInformation/formula. 
        return: name of terminal"""

        dt = element.find('dynamic_texts')
        if dt:
            for d in dt.findall('dynamic_elmt_text'):
                if d.attrib['text_from'] == 'ElementInfo':
                    return d.findtext('text')

        ## old version of QET XML diagram doesn't have dynamic text.
        label = formula = ''
        elinfos = element.find('elementInformations')
        if elinfos:
            for t in elinfos.findall('elementInformation'):
                if t.attrib['name'] == 'label':
                    label = t.text
                if t.attrib['name'] == 'formula':
                    formula = t.text
        
        if label == None:  # attrib returns None if empty.
            label = ''
        if formula == None:
            formula = ''

        return [label, formula][label == '']


    def _getElementMetadata (self, element):
        """Returns the metadata of the terminal element.
        All the info is Function field under 'elementInformation'
        return: {} keys: terminal_pos, terminal_type, cable, cable_conductor"""

        meta = ''
        ret = {'terminal_pos':'', 'terminal_type':'STANDARD', 'cable':'', 'cable_cond':'', 'bridge':''}
    
        ## Get meta string
        for t in element.find('elementInformations').findall('elementInformation'):
            if t.attrib['name'] == 'function':
                meta = t.text
        
        ## Getting data
        foo  = re.search('%p(\d+)(%|$)', meta)
        if foo:
            ret['terminal_pos'] = foo.group(1)

        foo  = re.search('%t([^%]*)(%|$)', meta)
        if foo:
            ret['terminal_type'] = foo.group(1)
    
        foo  = re.search('%c([^%]*)(%|$)', meta)
        if foo:
            ret['cable'] = foo.group(1)
        
        foo  = re.search('%n([^%]*)(%|$)', meta)
        if foo:
            ret['cable_cond'] = foo.group(1)
        
        foo  = re.search('%b([^%]*)(%|$)', meta)
        if foo:
            ret['bridge'] = foo.group(1)
        
        return ret


    def _isValidTerminal (self, element):
        """ An element is valid if type is 'terminal' and label is like 'X1:1'
        @param element:  element  (XML etree object)
        @return: True / False"""
        
        regex_name = '\w+:\W?\w+$'
        
        if re.search(':', self._getElementName(element)):
            if 'type' in element.attrib:  # elements must have a 'type'
                for el in self._terminalElements:  # searching type
                    if re.search(el + '$', element.attrib['type']):
                        return True
        
        return False


    def _getCableNum(self, diagram, terminalId):
        """Return the cable number connected at 'terminalId' in the page 'diagram'
        @param diagram: diagram(page) XML etree object
        @param terminalId: text with the terminal Id
        @return: string whith cable  number"""

        ret = ''
        for cable in diagram.find('conductors').findall('conductor'):
            for cable_terminal in \
                    [x for x in cable.attrib if x[:8] == 'terminal' ]:
                if cable.attrib[cable_terminal] == terminalId:
                    ret = cable.attrib['num']
        return ret

    
    def _getXRef(self, diagram, element, offset_x = 0, offset_y = 0):
        """Return a string with the xreference.

        The element is specified by 'element' at page 'diagam'.
        The page number incremented in one if there are a "index" page

        @param diagram: diagram(page) XML etree object
        @param element: element XML etree object
        @param offset_x: correction of the coord x.
               Useful for Xref for the terminal of an element
        @param offset_y: correction of the coord y
        @return: string like "p-rc" (page - rowLetter colNumber)"""
        ret = self.folio_reference_type

        # get coord
        element_x = int(float(element.attrib['x'])) + int(float(offset_x))
        element_y = int(float(element.attrib['y'])) + int(float(offset_y))
        row, col = self._getXRefByCoord (diagram, element_x, element_y)
        diagram_page = str(int(diagram.attrib['order']) + self.pageOffset)

        # Change tags to real value
        if '%f' in ret:
            ret = ret.replace('%f', diagram_page)
        if '%F' in ret:
            # %F could include extra tags
            folio_label = diagram.attrib['folio']
            if '%id' in folio_label:
                folio_label = folio_label.replace('%id', diagram_page)
            if '%total' in folio_label:
                folio_label = folio_label.replace('%total', str(self._totalPages))
            if '%autonum' in folio_label:
                folio_label = folio_label.replace('%autonum', diagram_page)
            ret = ret.replace('%F', folio_label)
        if '%M' in ret:
            ret = ret.replace('%M', diagram.attrib['machine'])
        if '%LM' in ret:
            ret = ret.replace('%LM', diagram.attrib['locmach'])
        if '%l' in ret:
            ret = ret.replace('%l', row)
        if '%c' in ret:
            ret = ret.replace('%c', col)

        return ret


    def _getXRefByCoord(self, diagram, x, y):
        """Return a string with the xreference for the coordinates at page 'diagam'
        The page number incremented in one if there are a "index" page

        @param diagram: diagram(page) XML etree object
        @param x,y: coordinates
        @return: string like "p-rc" (page - rowLetter colNumber)"""

        # get requiered data
        cols = int(diagram.attrib['cols'])
        col_size = int(diagram.attrib['colsize'])
        rows = int(diagram.attrib['rows'])
        row_size = int(diagram.attrib['rowsize'])
        element_x = int(x)
        element_y = int(y)
        rows_letters = [chr(x + 65) for x in range(rows)]

        if self.DEBUG:
            print( '<getXRef>: Page order: {}\tCol size: {}\tRow size: {}\tX position: {}\tY Position: {}'. \
                format (page, col_size, row_size, element_x, element_y))

        row_letter = rows_letters[ int(
                (element_y - QETProject.QET_COL_ROW_SIZE) / row_size) - 1 + 1]
                # +1: cal calc. -1 index of lists start 0.
        column = str(int((element_x - QETProject.QET_COL_ROW_SIZE) / col_size) + 1)
        return (row_letter, column)


    def get_list_of_used_terminals(self):
        """Return a list of all terminal elements used in the qet project.
        @return list where every element is a dict. See class info.
            strip: a long terminal strip is splited into a smaller parts.
        """
        ret = []  # return dict

        # first search for elements of type 'terminal' and its conductors.
        for diagram in self.qet_project.findall('diagram'):  # all diagrams
            for element in diagram.findall('.//element'):  # all elements in diagram
                el = {}

                if self._isValidTerminal(element):

                    terminalName = self._getElementName (element)
                    meta_data = self._getElementMetadata (element)
                    
                    terminals = element.find('terminals').findall( 'terminal' )
                    terminalId = terminals[0].attrib['id']
                    cableNum = self._getCableNum(diagram, terminalId)
                    terminalId2 = terminals[1].attrib['id']
                    cableNum2 = self._getCableNum(diagram, terminalId2)
                    if cableNum == '': cableNum = cableNum2
                    
                    el['uuid'] = element.attrib['uuid']
                    el['block_name'] = terminalName.split(':')[0]
                    el['segment'] = ''
                    el['terminal_name'] = terminalName.split(':')[1]
                    el['terminal_pos'] = meta_data['terminal_pos']
                    el['terminal_xref'] = self._getXRef(diagram, element)
                    el['terminal_type'] = meta_data['terminal_type']
                    el['conductor_name'] = cableNum
                    el['cable'] = meta_data['cable']
                    el['cable_cond'] = meta_data['cable_cond']
                    el['bridge'] = meta_data['bridge']
                if el: ret.append(el)

        return ret


    def save_tb(self, data, filename):
        """Save the array 'data' to the XML file"""
        for diagram in self.qet_project.findall('diagram'):  # all diagrams(pages)
            for element in diagram.iter('element'):  # all elements in diagram
                dt = [x for x in data if x['uuid'] == element.attrib['uuid']]
                if dt:
                    found = False
                    value = '%p{}%t{}%c{}%n{}%b{}'.format(
                            dt[0]['terminal_pos'], \
                            dt[0]['terminal_type'], \
                            dt[0]['cable'], \
                            dt[0]['cable_cond'],
                            dt[0]['bridge'])
                    for elinfo in element.iter('elementInformation'):
                        if elinfo.attrib['name'] == 'function':
                            elinfo.text = value
                            found = True
                    if not found:  # crete a new child
                        #~ print ('----------------------- {}'.format(element.attrib['uuid']))
                        father = element.find('elementInformations')
                        new = etree.SubElement(father, \
                                'elementInformation',
                                name="function", \
                                show="0")
                        new.text = value

        self._qet_tree.write(filename)  #, pretty_print=True)


    def insert_tb(self, segment_name, tb_node):
        """Inserts a xml node representing a terminal block,
        removing first the old element if exists
        @param segment_name: name of the segment
        @param tb_node: xml tree of the terminal block.
        @return: none"""
        
        element_name_to_delete = 'TB_' + segment_name + '.elmt'
        father = self.qet_project.find('collection').find('category')
        
        # remove the old element
        for element in father.iter('element'):  # all elements in the imported collection
            if element.attrib['name'] == element_name_to_delete:
                father.remove(element)

        # adding the element
        father.insert(0,tb_node)


class TerminalBlock:
    """This class represents a Terminal Block for a QET project.
    The list of terminals has dicts like:
        {uuid, block_name, segment, terminal_name, terminal_pos, 
        terminal_xref, terminal_type, conductor_name, cable, cable_cond}
    """

    DEBUG = False
    HEAD_WIDTH = 44
    HEAD_HEIGHT = 120
    UNION_WIDTH = 6
    UNION_HEIGHT = 70
    TERMINAL_WIDTH = 20
    TERMINAL_HEIGHT = HEAD_HEIGHT + 40
    CONDUCTOR_LENGTH = 40
    CABLE_LENGTH = 80
    CONDUCTOR_END_LENGTH = 40
    


    def __init__(self, tb_segment, collec):
        """initializer.
        @param string tb_id: name for this terminal block (e.g. -X1)
        @param string tb_segment: longs teminal blocks are splitet to fit in a
            page. A segment has the same name that the terminal block thats
            belongs, but adding a suffix.
        @param collec: collection of terminals. Only the terminals of the
            segment 'tb_id' are accepted.
        """
        self.tb_segment = tb_segment
        self.terminals = self._addTerminals(collec)
        self.num_terminals = len(self.terminals)
        self.tb_id = self.terminals[0]['block_name']


    def _addTerminals (self, terminals):
        """Add terminals to the block, but only accept terminals that haves
        the same 'terminal block' as the defined on constructor. The order of
        the termnals is respected
        @param terminals: list of dics with terminal info. The format is
            explained in the class definition."""
        ret = []
        for ter in terminals:
            if ter['segment'] == self.tb_segment:
                ret.append(ter)
        return ret
        

    def _getNum(self, x):
        """ Returns the page part as integer of a XREF. Is there isn't digits,
        return 9999. Usefull for sort reasons.
        e.g. '12-B8' """

        foo = x.split('-')[0]
        if foo.isdigit():
            return int(foo)
        else:
            return 9999


    def _get_empty_terminal(self, terminal_name=''):
        """Returns a list corresponding a new empty terminalself.

        The new terminal haves the same teminal_block_name.

        @param terminal_name: name/number for the terminal block
        @return: valid list format for a terminal.
        """
        # [element_uuid, terminal_block_name, terminal_name/number, terminal_xref,
        # NORTH cable id side 1, N.cable id side 2, N.cable num, N. cable destination xref,
        # SOUTH cable id side 1, S.cable id side 2, S.cable num, S. cable destination xref]
        return ['', self.tb_id, str(terminal_name), '', \
                '', '', self.config['reservation_label'], '', \
                '', '', self.config['reservation_label'], '']


    def _generate_reservation_numbers(self):
        """Creates new terminals ID for gaps if exist.

        Only check gaps for numerical ID's (not for +1, -0,...).
        The list of terminal_numbers comes from a unique block terminal,
        i.e. X1, X12,...

        NOTE: Modify self.terminals
        @return list with gaps filled and sorted.
        """

        only_numbers = [int(x[self._IDX_TERM_NAME_])
            for x in self.terminals if x[self._IDX_TERM_NAME_].isdigit()]
        only_numbers.sort()
        if self.DEBUG:
            print ("<drawTerminalBlock> Reservation - {}". \
                format(only_numbers))

        print ('{}'.format(self.terminals[0]))

        if only_numbers:  # if the are digits in terminals numeration
            for i in range(1, int(only_numbers[-1])):
                if i not in only_numbers:
                    self.terminals.append( self._get_empty_terminal(i))


    def drawTerminalBlock(self):
        """
        Creates a XML node of the terminal block.
        coord (0,0) al corner upper-left

        @(param) self.terminals
        @return: none"""

        # calc some values    
        name = 'TB_'+ self.tb_segment        
        total_width = TerminalBlock.HEAD_WIDTH + \
                TerminalBlock.UNION_WIDTH + \
                self.num_terminals * TerminalBlock.TERMINAL_WIDTH + \
                1  # +1 to force round the next tenth
        while (total_width % 10): total_width += 1
        total_height = TerminalBlock.TERMINAL_HEIGHT + \
                TerminalBlock.CONDUCTOR_LENGTH + \
                TerminalBlock.CABLE_LENGTH + \
                TerminalBlock.CONDUCTOR_END_LENGTH + 20 + \
                1  # +1 to force round the next tenth
        while (total_height % 10): total_height += 1

        # define the element
        """Save the array 'data' to the XML file"""
        cursor = 0  #seves current X coord.
        root = etree.Element('element', name=name + '.elmt')
        
        definition = etree.SubElement(root, "definition", \
                height = str(total_height) , \
                width = str(total_width), \
                hotspot_x = '5', hotspot_y = '24', \
                link_type = 'simple', \
                orientation = 'dyyy' ,\
                version = '0.4', \
                type='element')
        self._element_definitions(definition, name)
        self._element_label(definition)
        
        informations = etree.SubElement(definition, 'informations')
        informations.text = 'Terminal block'

        description = etree.SubElement(definition, 'description')
        
        # draw TB header
        y1 = (TerminalBlock.TERMINAL_HEIGHT - TerminalBlock.HEAD_HEIGHT) / 2
        hd = self._rect (description, x=cursor, y=y1, \
                width=TerminalBlock.HEAD_WIDTH, height=TerminalBlock.HEAD_HEIGHT)
        hd_label = self._label_header(description, text=self.tb_id)
        
        cursor += TerminalBlock.HEAD_WIDTH
        y1 = (TerminalBlock.TERMINAL_HEIGHT - TerminalBlock.UNION_HEIGHT) / 2
        un = self._rect (description, x=cursor, y=y1, \
                width=TerminalBlock.UNION_WIDTH, height=TerminalBlock.UNION_HEIGHT)
                
        # process every TerminalBlock of max length per folio
        cursor += TerminalBlock.UNION_WIDTH
        last_trmnl = {'uuid':'', 'block_name':'', 'segment':'', \
                'terminal_name':'', 'terminal_pos':'', 'terminal_xref' : '', \
                'terminal_type':'', 'conductor_name':'', 'cable':'', \
                'cable_cond':'', 'bridge':''}
        last_cable_coord_x = cursor
        for i in range(0, self.num_terminals):
            trmnl = self.terminals[i]
            halfx = cursor + TerminalBlock.TERMINAL_WIDTH / 2
            
            # draw terminal
            term = self._rect(description, x=cursor, y=0, \
                    width= TerminalBlock.TERMINAL_WIDTH, \
                    height= TerminalBlock.TERMINAL_HEIGHT)
            term_label = self._label_term(description, cursor, 0, trmnl['terminal_name'])
            term_xref_label = self._label_term_xref(description, cursor, 0, trmnl['terminal_xref'])
            
            # draw fuse, ground,... logo
            logo = self._type_term(description, x=cursor, y=0, typ=trmnl['terminal_type'])

            # draw bridge if needed
            if trmnl['bridge']:
                bridge = self._line(description, x1=halfx, \
                        x2=halfx + TerminalBlock.TERMINAL_WIDTH , \
                        y1=TerminalBlock.TERMINAL_HEIGHT / 2 + 10+ 1.5, \
                        y2=TerminalBlock.TERMINAL_HEIGHT / 2 + 10 +1.5)
            
            # draw north cables
            north_cable = self._line_vc(description, x=cursor, y1 = 0, y2 = -20)
            north_cable_label = self._label_cond(description, cursor, -2 , trmnl['conductor_name'])
            north_terminal = self._qet_term(description, cursor, -20, 'n')


            # draw south conductor depens if belongs or not a cable.
            if trmnl['cable'] != '':  # belongs
                south_cable = self._line_vc (description, x=cursor, \
                    y1 = TerminalBlock.TERMINAL_HEIGHT, \
                    y2 = TerminalBlock.TERMINAL_HEIGHT + TerminalBlock.CONDUCTOR_LENGTH)
                south_cable_label = self._label_cond(description , x=cursor, \
                    y=TerminalBlock.TERMINAL_HEIGHT + TerminalBlock.CONDUCTOR_LENGTH / 2, \
                    text=trmnl['cable_cond'])
                y1 = TerminalBlock.TERMINAL_HEIGHT + \
                        TerminalBlock.CONDUCTOR_LENGTH + \
                        TerminalBlock.CABLE_LENGTH
                y2 = TerminalBlock.TERMINAL_HEIGHT + \
                        TerminalBlock.CONDUCTOR_LENGTH + \
                        TerminalBlock.CABLE_LENGTH + \
                        TerminalBlock.CONDUCTOR_END_LENGTH
                south_cable_end = self._line_vc (description, x=cursor, y1=y1, y2=y2) 
                south_cable_end_label = self._label_cond(description , x=cursor, \
                    y= y1 + (y2-y1)/2, text=trmnl['cable_cond'])    
                south_terminal = self._qet_term(description, cursor, y2, 's')
            else:  # independend conductor
                south_cable = self._line_vc (description, x=cursor, \
                y1 = TerminalBlock.TERMINAL_HEIGHT, \
                y2 = TerminalBlock.TERMINAL_HEIGHT + 20)
                south_cable_label = self._label_cond(description , x=cursor, \
                    y=TerminalBlock.TERMINAL_HEIGHT + 10, text=trmnl['cable_cond'])
                south_terminal = self._qet_term(description, cursor, \
                    TerminalBlock.TERMINAL_HEIGHT + 20 , 's')

            # draw representation of the cable of conductors
            y1 = TerminalBlock.TERMINAL_HEIGHT + TerminalBlock.CONDUCTOR_LENGTH
            y2 = TerminalBlock.TERMINAL_HEIGHT + \
                    TerminalBlock.CONDUCTOR_LENGTH + \
                    TerminalBlock.CABLE_LENGTH

            if ( (trmnl['cable'] != last_trmnl['cable']) and (last_trmnl['cable'] != '') ) or \
               ( (last_trmnl['cable'] != '') and (i == self.num_terminals - 1) ) : # change cable or last term.
                    
                x1 = last_cable_coord_x + (TerminalBlock.TERMINAL_WIDTH / 2)
                x2 = cursor - (TerminalBlock.TERMINAL_WIDTH / 2)
                
                # Change coord for horizontal line    
                if i == self.num_terminals - 1:
                    if trmnl['cable'] == last_trmnl['cable']:
                        x2 = x2 + TerminalBlock.TERMINAL_WIDTH 

                hor_line1 = self._line(description, x1, x2, y1, y1)
                hor_line2 = self._line(description, x1, x2, y2, y2)
                ver_line = self._line(description, (x1+x2)/2, (x1+x2)/2, y1, y2)
                ver_line_label = self._label_cond(description, \
                        (x1+x2)/2 - TerminalBlock.TERMINAL_WIDTH + 10, \
                        y1 + ((y2-y1)/2) + len(last_trmnl['cable'])*3, \
                        last_trmnl['cable'])


                # Extra line if last cable has only one conductor
                if i == self.num_terminals-1:
                    if trmnl['cable'] != last_trmnl['cable']:
                        x1 = x1 + TerminalBlock.TERMINAL_WIDTH
                        x2 = x2 + TerminalBlock.TERMINAL_WIDTH
                        ver_line = self._line(description, x2, x2, y1, y2)
                        ver_line_label = self._label_cond(description, \
                        (x1+x2)/2 - TerminalBlock.TERMINAL_WIDTH + 10, \
                        y1 + ((y2-y1)/2) + len(last_trmnl['cable'])*3, \
                        trmnl['cable'])                   
                        
                        
            # memo of x coord.
            if trmnl['cable'] != last_trmnl['cable']:
                last_cable_coord_x = cursor

                
            # task at loop end
            cursor += TerminalBlock.TERMINAL_WIDTH
            last_trmnl = trmnl

        #~ etree.ElementTree(root).write('tmp.xml') #, pretty_print=True)
        return root


    def _element_definitions(self, father, name):
        sUUID = uuidly.uuid1().urn[9:]
        uuid = etree.SubElement(father, 'uuid', uuid=sUUID)
        
        names = etree.SubElement(father, 'names')
        lang1 = etree.SubElement(names, 'name', lang='de')
        lang1.text = 'Terminalblock ' + name
        lang2 = etree.SubElement(names, 'name', lang='ru')
        lang2.text = '&#x422;&#x435;&#x440;&#x43C;&#x438;&#x43D;&#x430;&#x43B;&#x44C;&#x43D;&#x44B;&#x439; &#x431;&#x43B;&#x43E;&#x43A; ' + name
        lang3 = etree.SubElement(names, 'name', lang='pt')
        lang3.text = 'Bloco terminal ' + name
        lang4 = etree.SubElement(names, 'name', lang='en')
        lang4.text = 'Terminal block ' + name
        lang5 = etree.SubElement(names, 'name', lang='it')
        lang5.text = 'Terminal block ' + name
        lang6 = etree.SubElement(names, 'name', lang='fr')
        lang6.text = 'Bornier ' + name
        lang7 = etree.SubElement(names, 'name', lang='pl')
        lang7.text = 'Blok zacisk&#xF3;w ' + name
        lang8 = etree.SubElement(names, 'name', lang='es')
        lang8.text = 'Bornero ' + name
        lang9 = etree.SubElement(names, 'name', lang='nl')
        lang9.text = 'Eindblok ' + name
        lang10 = etree.SubElement(names, 'name', lang='cs')
        lang10.text = 'Termin&#xE1;lov&#xFD; blok ' + name


    def _element_label(self, father):
        # element label
        label = etree.SubElement(father, 'dynamic_text', \
                x=str(TerminalBlock.HEAD_WIDTH + 5), \
                y=str(TerminalBlock.HEAD_HEIGHT + 5), \
                z='2', \
                text_from='ElementInfo', text_width='-1', \
                uuid = uuidly.uuid1().urn[9:], \
                font_size='10', frame='false')
        label_text = etree.SubElement(label, 'text')
        label_text.text = self.tb_id
        label_info = etree.SubElement(label, 'info_name')
        label_info.text = 'label'


    def _type_term(self, father, x, y, typ):
        """Generates a xml element that represents the logo of the teminal
        """
        y = y + 10  # move all down
        if typ.lower() == 'ground':
            logo_with = 15
            y = y - 6
            x1 = x + (TerminalBlock.TERMINAL_WIDTH / 2)
            y1 = y + (TerminalBlock.TERMINAL_HEIGHT /2)
            y2 = y1 + 10
            vert_line1 = self._line(father, x1, x1, y1, y2)
                        
            x1 = x + (TerminalBlock.TERMINAL_WIDTH - logo_with) / 2
            x2 = x1 + logo_with
            hor_line1 = self._line(father, x1, x2, y2, y2)
            
            hor_line2 = self._line(father, x1+2, x2-2, y2+2, y2+2)
            hor_line3 = self._line(father, x1+4, x2-4, y2+4, y2+4)
        elif typ.lower() == 'fuse':
            logo_height = 36
            x1 = x
            x2 = x + TerminalBlock.TERMINAL_WIDTH
            y1 = y + (TerminalBlock.TERMINAL_HEIGHT / 2) - (logo_height/2)  # centering
            y2 = y1 + logo_height
            hor_line1 = self._line(father, x1, x2, y1, y1)
            hor_line2 = self._line(father, x1, x2, y2, y2)
            
            # central square
            xc = x + (TerminalBlock.TERMINAL_WIDTH / 2)
            x1a = xc - 3
            x2a = xc + 3
            y1a = y1 + 6
            y2a = y2 - 6
            hor_line3 = self._line(father, x1a, x2a, y1a, y1a)
            hor_line4 = self._line(father, x1a, x2a, y2a, y2a)
                        
            vert_line1 = self._line(father, x1a, x1a, y1a, y2a)
            vert_line2 = self._line(father, x2a, x2a, y1a, y2a)
            vert_line3 = self._line(father, x1a + (x2a-x1a)/2, \
                    x1a + (x2a-x1a)/2, y1a-3, y2a+3)
        else:
            x1 = x + TerminalBlock.TERMINAL_WIDTH / 2
            y1 = y + TerminalBlock.TERMINAL_HEIGHT / 2 
            cir = self._circle(father, x1, y1, 3)
            
                        
    def _circle(self, father, x, y, diameter):
        """Generates a xml element that represents a line verticalcentered 
        on the terminal
        """
        ls = 'line-style:normal;line-weight:normal;filling:none;color:black'
        return etree.SubElement(father, 'circle', \
                        x = str(x), y = str(y), diameter = str(diameter), \
                        antialias = 'false', \
                        style = ls)
                        
                        
    def _line_vc(self, father, x, y1, y2):
        """Generates a xml element that represents a line verticalcentered 
        on the terminal
        """
        xc= x + TerminalBlock.TERMINAL_WIDTH / 2
        ls = 'line-style:normal;line-weight:normal;filling:none;color:black'
        return etree.SubElement(father, 'line', \
                        x1 = str(xc), \
                        x2 = str(xc), \
                        y1 = str(y1), \
                        y2 = str(y2), \
                        length1 = '1.5', \
                        length2 = '1.5', \
                        end1 = 'none', \
                        end2 = 'none', \
                        antialias = 'false', \
                        style = ls)


    def _line(self, father, x1, x2, y1, y2):
        """Generates a xml element that represents a line  
        on the terminal
        """
        ls = 'line-style:normal;line-weight:normal;filling:none;color:black'
        return etree.SubElement(father, 'line', \
                        x1 = str(x1), \
                        x2 = str(x2), \
                        y1 = str(y1), \
                        y2 = str(y2), \
                        length1 = '1.5', \
                        length2 = '1.5', \
                        end1 = 'none', \
                        end2 = 'none', \
                        antialias = 'false', \
                        style = ls)


    def _rect(self, father, x, y, width, height):
        """Generates a xml element that represents a line verticalcentered 
        on the terminal
        """
        style = 'line-style:normal;line-weight:normal;filling:none;color:black'
        return etree.SubElement(father, 'rect', \
                    x = str(x), \
                    y = str(y), \
                    width = str(width), \
                    height = str(height), \
                    antialias = 'false', \
                    style = style)


    def _qet_term(self, father, x, y, orientation):
        """Generates a xml element that represents a line verticalcentered 
        on the terminal
        """
        xc = x + TerminalBlock.TERMINAL_WIDTH / 2
        orth_terminal = etree.SubElement(father, 'terminal', \
                    x=str(xc), y=str(y), \
                    orientation=orientation)


    def _label_cond(self, father, x, y, text):
        """Generates a xml element that represents a label of a conductor centered
        on the terminal
        @ param father: xml node father
        @ param x: x pos. of terminal
        @ param y: y pos. of the text
        @ param text: text to show
        """
        xc = x + TerminalBlock.TERMINAL_WIDTH / 2
        return etree.SubElement(father, 'text', \
                        x = str(xc - 2), \
                        y = str(y), \
                        rotation='270', \
                        size='6', \
                        text=text)
                        
                        
    def _label_header(self, father, text):
        """Generates a xml element that represents a label of a conductor centered
        on the terminal
        @ param father: xml node father
        @ param x: x pos. of the header
        @ param y: y pos. of the header
        @ param text: text to show
        """
        size = 10
        x = (TerminalBlock.HEAD_WIDTH / 2) + 5
        y = (TerminalBlock.HEAD_HEIGHT / 2) + (len(text) / 2) * size * 1.06 

        return etree.SubElement(father, 'text', \
                        x = str(x), \
                        y = str(y), \
                        rotation='270', \
                        size=str(size), \
                        text=text)


    def _label_term(self, father, x, y, text):
        """Generates a xml element that represents a label of a conductor centered
        on the terminal
        @ param father: xml node father
        @ param x: x pos. of the terminal
        @ param y: y pos. of the terminal
        @ param text: id of the terminal
        """
        size = 9
        x1 = x + (TerminalBlock.HEAD_WIDTH / 2) - 8
        y1 = y + TerminalBlock.TERMINAL_HEIGHT - 12
        return etree.SubElement(father, 'text', x = str(x1), y = str(y1), \
                rotation='270', size=str(size), text=text)
                
                
    def _label_term_xref(self, father, x, y, text):
        """Generates a xml element that represents a label of a conductor centered
        on the terminal
        @ param father: xml node father
        @ param x: x pos. of the terminal
        @ param y: y pos. of the terminal
        @ param text: id of the terminal
        """
        size = 6
        x1 = x + (TerminalBlock.HEAD_WIDTH / 2) - 8
        y1 = y + 70
        return etree.SubElement(father, 'text', x = str(x1), y = str(y1), \
                rotation='270', size=str(size), text=text)


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
    right_on_field ( event.widget, frmFoot.winfo_children()[0] )


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
    #~ right_on_field ( event.widget, frmFoot.winfo_children()[5] )


def right_on_cable(event):
    right_on_field ( event.widget, frmFoot.winfo_children()[6] )


def right_on_cond(event):
    right_on_field ( event.widget, frmFoot.winfo_children()[7] )

            
def return_on_pos(event):
    return_on_field( event.widget, frmFoot.winfo_children()[0])


def return_on_type(event):
    return_on_field( event.widget, frmFoot.winfo_children()[5])


def return_on_cable(event):
    return_on_field( event.widget, frmFoot.winfo_children()[6])


def return_on_cond(event):
    return_on_field( event.widget, frmFoot.winfo_children()[7])


def click_on_save(event):
    """Event button. Create terminal block.
    Inserts terminal block into XML structure.
    Saves project."""
    
    global wdg_data
    global qet_file
    global frmFoot
    global qet_project
    
    progress_label = tk.Label(frmFoot, font=('Helvetica', 12, 'bold '), fg='red',  \
            text='                GENERATING TERMINAL BLOCKS...               ')
    progress_label.grid(row=1, columnspan=8)
    
    ## sorting 
    click_on_reorder(event)  # this updates wdg_data
    data_from_ui = convert_from_control_var()

    ## Loop segments
    segments = list(OrderedDict.fromkeys([x['segment'] for x in data_from_ui]))
    for seg in segments:
        a_block = TerminalBlock(seg, data_from_ui)
        qet_project.insert_tb (seg, a_block.drawTerminalBlock())  # creates XML element file

    ## Depends if overwrite (in config tab) is checked.
    if config['overwrite'].get():
        # finding new backup free name
        i = 1
        full_back_path = qet_file[:qet_file.rfind('.')] + '_' + str(i) + '.qet' 
        while os.path.isfile( full_back_path) or \
              os.path.isdir( full_back_path ) :
            i += 1
            full_back_path = qet_file[:qet_file.rfind('.')] + '_' + str(i) + '.qet' 
        
        # backup    
        shutil.copyfile(qet_file, full_back_path)
        
        # saving to file
        qet_project.save_tb(convert_from_control_var(), qet_file)
        messagebox.showinfo("QET", "- Document saved as {}\n\n- The original project backed up as {}\n\n- Reload the QET project.". \
            format(qet_file, full_back_path))
    else:
        # saving 
        full_save_path = qet_file[:qet_file.rfind('.')] + '_tb.qet' 
        qet_project.save_tb(convert_from_control_var(), full_save_path)
        messagebox.showinfo("QET", "Document saved as {}". \
            format(full_save_path))

    ## removing progres text
    progress_label.destroy()
    

def print_tb(data):
    if DEBUG:
        print ('{}\t{}\t{}\t{}\t{}\t{}'.format( \
            'Segm.', \
            'Blk', \
            'Ter.Pos', \
            'Cable', \
            'Conduct', \
            'Ter.Nam'))
        for it in data:
            print ('{}\t{}\t{}\t{}\t{}\t{}'.format( \
                    it['segment'], \
                    it['block_name'], \
                    it['terminal_pos'], \
                    it['cable'], \
                    it['cable_cond'], \
                    it['bridge'], \
                    it['terminal_name']))
    
            
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
            
        #~ ## wdg_data = convert_to_control_var(data_sorted)
    #~ ## print_tb(wdg_data)


    #~ messagebox.showinfo("QET", \
            #~ "This will redraw the table according the POS. column values.")
  

def sort_terminals(data):
    """Terminals are sorter by: block_name, terminal_pos, cable, 
    cable_cond, terminal_name.
    Later, if a terminal block is longer than STRIP_LONG, will be split
    using 'strip' field.
    @param data: lista de diccionarios con los datos de los terminales.
    """
    ret = []
    
    # convert values to int
    data = convert_numerical(data)
    # spliting if needed
    terms = list(OrderedDict.fromkeys([x['block_name'] for x in data])) # no dupl.
    for t in terms:
        tb = [x for x in data if x['block_name'] == t]
        tb_sorted = multikeysort(tb, \
                ['terminal_pos', 'cable', 'cable_cond', 'terminal_name'])
        segment_label = 0
        for i in range(0, len(tb), STRIP_LONG):
            segment_label += 1  # segment label
            segment = tb_sorted[i:i+STRIP_LONG]
            
            # Labeling strip
            for item in segment:
                item['segment'] = '{}({})'.format(t, segment_label)
            
            ret += segment
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
    regex_digits = '^(\d+)$'
    for ter in data:
        if re.search(regex_digits, ter['terminal_name']):
            ter['terminal_name'] = int(ter['terminal_name'])
        if re.search(regex_digits, ter['terminal_pos']):
            ter['terminal_pos'] = int(ter['terminal_pos'])
        if re.search(regex_digits, ter['cable']):
            ter['cable'] = int(ter['cable'])
        if re.search(regex_digits, ter['cable_cond']):
            ter['cable_cond'] = int(ter['cable_cond'])
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


def initUI(root, data):
    """Creates the UI
    param root: root frame
    param data: list of a dictionary for every terminal
      {uuid, block_name, terminal_name, terminal_pos, 
            terminal_xref, terminal_type, conductor_name,
            cable, cable_cond, bridge}
    """
    global frmFoot
    global wdg_data
    global config


    GRID_CONFIG = [
    {'TITLE':'POS.', 'WIDTH': 8, 'AUTOFILL': '1', 'dicc_index':'terminal_pos', \
        'right':right_on_pos,'return':return_on_pos}, \
    {'TITLE':'TERM.BLOCK', 'WIDTH': 15, 'AUTOFILL': '', 'dicc_index':'block_name', \
        'right':'','return':''}, \
    {'TITLE':'ID', 'WIDTH': 10, 'AUTOFILL': '', 'dicc_index':'terminal_name', \
        'right':'','return':''}, \
    {'TITLE':'XREF', 'WIDTH': 14, 'AUTOFILL': '', 'dicc_index':'terminal_xref', \
        'right':'','return':''}, \
    {'TITLE':'CONDUCTOR', 'WIDTH': 12, 'AUTOFILL': '', 'dicc_index':'conductor_name', \
        'right':'','return':''}, \
    {'TITLE':'BRIDGE', 'WIDTH': 9, 'AUTOFILL': ' ', 'dicc_index':'bridge', \
        'right':right_on_bridge,'return':''}, \
    {'TITLE':'TYPE', 'WIDTH': 10, 'AUTOFILL': ' ', 'dicc_index':'terminal_type', \
        'right':right_on_type,'return':''}, \
    {'TITLE':'CABLE', 'WIDTH': 14, 'AUTOFILL': '-W1', 'dicc_index':'cable', \
        'right':right_on_cable,'return':return_on_cable}, \
    {'TITLE':'CABLE COND.', 'WIDTH': 14, 'AUTOFILL': '1', 'dicc_index':'cable_cond', \
        'right':right_on_cond,'return':return_on_cond}, \
    ]
    #~ {'TITLE':'UUID', 'WIDTH': 13, 'AUTOFILL': '', 'dicc_index':'uuid', \
        #~ 'right':'','return':''} \
 
    ## config root window
    root.title("QET - Terminal block generator - v{}".format(VERSION))
    root.resizable(True, True)  # width, height
    #~ img = tk.PhotoImage(file='qet.png')
    #~ root.tk.call('wm', 'iconphoto', root._w, img)
    #~ root.iconbitmap("qet.ico")  # only b/n ico for linux
    
    ## frame header
    frmHeader = tk.Frame(root, borderwidth=1, relief='solid')
    
    b1 = tk.Button(frmHeader,text='CREATE TERMINAL BLOCKS')
    b1.pack(side='right')
    b1.bind("<Button-1>", click_on_save)
    
    b2 = tk.Button(frmHeader,text='SORT')
    b2.pack(side='right')
    b2.bind("<Button-1>", click_on_reorder)
    
    
    ## TABS
    tabs = ttk.Notebook(root)  # populates 'segment' field

    segments = list(OrderedDict.fromkeys([x['segment'] for x in data])) # no dupl.
    wdg_data_index = 0
    for seg in segments:
        ## frame data
        frmData = tk.Frame(tabs)
        
        ## caption
        for c in range(len(GRID_CONFIG)):
            tk.Label(frmData, text=GRID_CONFIG[c]['TITLE'], \
                     width = GRID_CONFIG[c]['WIDTH'], \
                     font=('Helvetica', 10, 'bold underline')).grid(row=0, column=c)
        offset = 1
        terminals = [x for x in data if x['segment'] == seg]  # choose a segment
        tab_row = 0
        for ter in terminals:
            for c in range(len(GRID_CONFIG)):
                lbl = tk.Entry(frmData, borderwidth=0, \
                        width = GRID_CONFIG[c]['WIDTH']-1, \
                        justify = 'center', fg='blue', bg='gray85', \
                        textvariable = wdg_data[wdg_data_index][GRID_CONFIG[c]['dicc_index']])
                lbl.grid(row=tab_row+offset,column=c)
                
                if GRID_CONFIG[c]['AUTOFILL'] == '':
                    lbl.config(state='disabled', disabledforeground = 'black', \
                            disabledbackground='gray85')
                #~ elif GRID_CONFIG[c]['AUTOFILL'] == '@':
                    #~ lbl.config(state='disabled', disabledforeground = 'blue', \
                            #~ disabledbackground='gray85')
                    
                if GRID_CONFIG[c]['right'] != '':
                    lbl.bind("<Button-3>",GRID_CONFIG[c]['right'])
                if GRID_CONFIG[c]['return'] != '':
                    lbl.bind("<Return>",GRID_CONFIG[c]['return'])
            tab_row += 1
            wdg_data_index += 1
        tabs.add(frmData, text=seg)

    ## Config tab
    frmConfig = tk.Frame(tabs)
    config['overwrite'] = tk.IntVar()
    tk.Checkbutton(frmConfig, \
            text='Write changes in the original QET project', \
            variable=config['overwrite']).pack(side='top', anchor='w')
    config['overwrite'].set(True)

    tk.Label(frmConfig, text=txt[1], justify='left').pack(side='top', anchor='w')
    tk.Label(frmConfig, text=txt[2], justify='left').pack(side='top', anchor='w')

    tabs.add(frmConfig, text='Config')

    ## Help tab
    frmInfo = tk.Frame(tabs)
    tk.Label(frmInfo, text=txt[3], justify='left').pack()
    tabs.add(frmInfo, text='Help')

    ## Form Header
    frmHeader = tk.Frame(root, borderwidth=1, relief='solid')
    tk.Label(frmHeader, text=txt[0], justify='left').pack(side='left')
    
    b1 = tk.Button(frmHeader,text='CREATE TERMINAL BLOCKS')
    b1.pack(side='right')
    b1.bind("<Button-1>", click_on_save)
    
    b2 = tk.Button(frmHeader,text='SORT')
    b2.pack(side='right')
    b2.bind("<Button-1>", click_on_reorder)
    

    ## frame foot
    frmFoot = tk.Frame(root, borderwidth=1, relief='solid')
    for c in range(len(GRID_CONFIG)):
        t = GRID_CONFIG[c]['AUTOFILL']
        tk.Label(frmFoot, text=t, padx=2, \
                 width = GRID_CONFIG[c]['WIDTH'], \
                 font=('Helvetica', 10, 'bold'), fg='gray').grid(row=0, column=c)
        
    ## Packing
    frmHeader.pack(anchor='n', fill='x', expand='True', pady=6, padx=6)
    tabs.pack(fill='x', expand='True',pady=6, padx=6)
    frmFoot.pack(anchor='s', fill='x', expand='True', pady=6, padx=6)

    ## Bottom Label recording save qet project before
    info_label = tk.Label(frmFoot, font=('Helvetica', 10, 'bold '), fg='red',  \
            text='Remember to record the QET project before using this plug-in.')
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
    
    
def print_debug_xml(element):
    if DEBUG:
        print (etree.tostring(element).decode())
    
     
def main():
    global qet_project
    global wdg_data  
    global qet_file
    

    ## UI Root
    wdg_root = tk.Tk(  )
    
    ## Get QET path from command line or show dialog to choose one.
    qet_file = get_QET_path(wdg_root)
    
    ## QET Project
    qet_project = QETProject(qet_file)  # allow working with a QET XML file.
    qet_terminals_used = qet_project.get_list_of_used_terminals()

    ## Converting to number, sorting splitting and converting to a widgets dicc
    qet_terminals_used_sorted = sort_terminals(qet_terminals_used)

    wdg_data = convert_to_control_var(qet_terminals_used_sorted)
    
    ## UI
    initUI(wdg_root, qet_terminals_used_sorted)
    
    ## main loop
    wdg_root.mainloop(  )


if __name__ == '__main__':
    main()
