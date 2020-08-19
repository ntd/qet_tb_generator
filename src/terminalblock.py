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
 

# Imports
import logging as log
import re
import xml.etree.ElementTree as etree  # python3-lxml
import uuid as uuidly


class TerminalBlock:
    """This class represents a Terminal Block for a QET project.
    The list of terminals has dicts like:
        {uuid, block_name, segment, terminal_name, terminal_pos, 
        terminal_xref, terminal_type, conductor_name, cable, cable_cond}
    """

    HEAD_WIDTH = 44
    HEAD_HEIGHT = 120
    UNION_WIDTH = 6
    UNION_HEIGHT = 70
    TERMINAL_WIDTH = 20
    TERMINAL_HEIGHT = HEAD_HEIGHT + 40
    CONDUCTOR_LENGTH = 70
    CABLE_LENGTH = 80
    CONDUCTOR_END_LENGTH = 70
    


    def __init__(self, tb_block_name, collec):
        """initializer.
        @param string tb_block_name: block_name
        @param collec: collection of terminals. Only the terminals of the
            segment 'tb_id' are accepted.
        """
        self.tb_block_name = tb_block_name
        self.terminals = collec
        self.num_terminals = len(self.terminals)
        self.tb_id = self.terminals[0]['block_name']


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
        """Creates new terminals ID for gaps if exist. # TODO: not used?

        Only check gaps for numerical ID's (not for +1, -0,...).
        The list of terminal_numbers comes from a unique block terminal,
        i.e. X1, X12,...

        NOTE: Modify self.terminals
        @return list with gaps filled and sorted.
        """

        only_numbers = [int(x[self._IDX_TERM_NAME_])
            for x in self.terminals if x[self._IDX_TERM_NAME_].isdigit()]
        only_numbers.sort()
        log.debug("<drawTerminalBlock> Reservation - {}".format(only_numbers))

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
        name = 'TB_'+ self.tb_block_name  
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
        hd_label = self._label_header(description, text=self.tb_block_name)
        
        cursor += TerminalBlock.HEAD_WIDTH
        y1 = (TerminalBlock.TERMINAL_HEIGHT - TerminalBlock.UNION_HEIGHT) / 2
        un = self._rect (description, x=cursor, y=y1, \
                width=TerminalBlock.UNION_WIDTH, height=TerminalBlock.UNION_HEIGHT)
                
        # process every teminal
        cursor += TerminalBlock.UNION_WIDTH
        last_trmnl = {}  
        for k in self.terminals[0]: last_trmnl[k] = ''  # init last_trmnl

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
            north_cable = self._line_vc(description, x=cursor, y1 = 0, y2 = -30)
            north_cable_label = self._label_cond(description, cursor, -2 , trmnl['cable'])
            north_terminal = self._qet_term(description, cursor, -30, 'n')

            # draw south conductor depens if belongs or not a cable.
            if trmnl['hose'] != '':  # belongs
                # cable touching the terminal block
                south_cable = self._line_vc (description, x=cursor, \
                    y1 = TerminalBlock.TERMINAL_HEIGHT, \
                    y2 = TerminalBlock.TERMINAL_HEIGHT + TerminalBlock.CONDUCTOR_LENGTH)
                south_cable_label = self._label_cond(description , x=cursor, \
                    y=TerminalBlock.TERMINAL_HEIGHT +  28, \
                    text=trmnl['cable'])

                # conductor tick and label
                conductor_label = self._label_cond(description , x=cursor, \
                    y=TerminalBlock.TERMINAL_HEIGHT + TerminalBlock.CONDUCTOR_LENGTH -7, \
                    text=trmnl['conductor'])
                conductor_tick = self._line(description, \
                    x1=cursor + TerminalBlock.TERMINAL_WIDTH/2 - 2, \
                    x2=cursor + TerminalBlock.TERMINAL_WIDTH/2 + 2, \
                    y1=TerminalBlock.TERMINAL_HEIGHT + TerminalBlock.CONDUCTOR_LENGTH -7-8, \
                    y2=TerminalBlock.TERMINAL_HEIGHT + TerminalBlock.CONDUCTOR_LENGTH -7-5)

                # end part of the conductor
                y1 = TerminalBlock.TERMINAL_HEIGHT + \
                        TerminalBlock.CONDUCTOR_LENGTH + \
                        TerminalBlock.CABLE_LENGTH
                y2 = TerminalBlock.TERMINAL_HEIGHT + \
                        TerminalBlock.CONDUCTOR_LENGTH + \
                        TerminalBlock.CABLE_LENGTH + \
                        TerminalBlock.CONDUCTOR_END_LENGTH
                y_label = y1 + 20
                south_cable_end = self._line_vc (description, x=cursor, y1=y1, y2=y2) 
                conductor_tick_end = self._line(description, \
                    x1=cursor + TerminalBlock.TERMINAL_WIDTH/2 - 2, \
                    x2=cursor + TerminalBlock.TERMINAL_WIDTH/2 + 2, \
                    y1=y_label - 8, y2=y_label - 5)
                south_cable_end_label = self._label_cond(description , x=cursor, \
                    y= y_label, text=trmnl['conductor'])    
                south_terminal = self._qet_term(description, cursor, y2, 's')
            
            else:  # independend conductor (no hose)
                south_cable = self._line_vc (description, x=cursor, \
                y1 = TerminalBlock.TERMINAL_HEIGHT, \
                y2 = TerminalBlock.TERMINAL_HEIGHT + 30)
                south_cable_label = self._label_cond(description , x=cursor, \
                    y=TerminalBlock.TERMINAL_HEIGHT + 28, text=trmnl['cable'])
                south_terminal = self._qet_term(description, cursor, \
                    TerminalBlock.TERMINAL_HEIGHT + 30 , 's')
                    
            # draw hose of conductors
            y1 = TerminalBlock.TERMINAL_HEIGHT + TerminalBlock.CONDUCTOR_LENGTH
            y2 = TerminalBlock.TERMINAL_HEIGHT + \
                    TerminalBlock.CONDUCTOR_LENGTH + \
                    TerminalBlock.CABLE_LENGTH

            if ( (trmnl['hose'] != last_trmnl['hose']) \
                        and (last_trmnl['hose'] != '') ) \
                or \
               ( (last_trmnl['hose'] != '') \
                        and (i == self.num_terminals - 1) ) : # change hose or last term.
                    
                x1 = last_cable_coord_x + (TerminalBlock.TERMINAL_WIDTH / 2)
                x2 = cursor - (TerminalBlock.TERMINAL_WIDTH / 2)
                
                # Change coord for horizontal line    
                if i == self.num_terminals - 1:
                    if trmnl['hose'] == last_trmnl['hose']:
                        x2 = x2 + TerminalBlock.TERMINAL_WIDTH 

                hor_line1 = self._line(description, x1, x2, y1, y1)
                hor_line2 = self._line(description, x1, x2, y2, y2)
                ver_line = self._line(description, (x1+x2)/2, (x1+x2)/2, y1, y2)
                ver_line_label = self._label_cond(description, \
                        (x1+x2)/2 - TerminalBlock.TERMINAL_WIDTH + 10, \
                        y1 + ((y2-y1)/2) + len(last_trmnl['hose'])*3, \
                        last_trmnl['hose'])


                # Extra line if last cable has only one conductor
                if i == self.num_terminals-1:
                    if (trmnl['hose'] != last_trmnl['hose']) \
                       and \
                       (trmnl['hose'] != ''):
                        x1 = x1 + TerminalBlock.TERMINAL_WIDTH
                        x2 = x2 + TerminalBlock.TERMINAL_WIDTH
                        ver_line = self._line(description, x2, x2, y1, y2)
                        ver_line_label = self._label_cond(description, \
                        x2 - 10, \
                        y1 + ((y2-y1)/2) + len(last_trmnl['hose'])*3, \
                        trmnl['hose'])                   
                        
                        
            # memo of x coord.
            if trmnl['hose'] != last_trmnl['hose']:
                last_cable_coord_x = cursor

                
            # task at loop end
            cursor += TerminalBlock.TERMINAL_WIDTH
            last_trmnl = trmnl

        #~ etree.ElementTree(root).write('tmp.xml') #, pretty_print=True)
        return root


    def _element_definitions(self, father, name):
        sUUID = '{' + uuidly.uuid1().urn[9:] + '}'
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
                uuid = '{' + uuidly.uuid1().urn[9:] + '}', \
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
        size = 6
        xc = x - size + 1
        label = etree.SubElement(father, 'dynamic_text', \
                x=str(xc), \
                y=str(y), \
                z='3', \
                text_from='UserText', \
                uuid = '{' + uuidly.uuid1().urn[9:] + '}', \
                font_size=str(size), frame='false', \
                rotation='270')
        label_text = etree.SubElement(label, 'text')
        label_text.text = text
        #label_color = etree.SubElement(label, 'color')
        #label_color.text = '#ff0000'  
        return label          
        

    def _label_header(self, father, text):
        """Generates a xml element that represents a label of a conductor centered
        on the terminal
        @ param father: xml node father
        @ param x: x pos. of the header
        @ param y: y pos. of the header
        @ param text: text to show
        """
        size = 13
        x = (TerminalBlock.HEAD_WIDTH / 2) - size
        y = (TerminalBlock.HEAD_HEIGHT / 2) + (len(text) / 2) * size * 1.3 
        label = etree.SubElement(father, 'dynamic_text', \
                x=str(x), \
                y=str(y), \
                z='3', \
                text_from='UserText', \
                uuid = '{' + uuidly.uuid1().urn[9:] + '}', \
                font_size=str(size), frame='false', \
                rotation='270')
        label_text = etree.SubElement(label, 'text')
        label_text.text = text
        label_color = etree.SubElement(label, 'color')
        label_color.text = '#777777'
        return label


    def _label_term(self, father, x, y, text):
        """Generates a xml element that represents a label of a conductor centered
        on the terminal
        @ param father: xml node father
        @ param x: x pos. of the terminal
        @ param y: y pos. of the terminal
        @ param text: id of the terminal
        """
        size = 9
        x1 = x + (TerminalBlock.HEAD_WIDTH / 2) - TerminalBlock.TERMINAL_WIDTH - size + 6
        y1 = y + TerminalBlock.TERMINAL_HEIGHT - 12
        label = etree.SubElement(father, 'dynamic_text', \
                x=str(x1), \
                y=str(y1), \
                z='3', \
                text_from='UserText', \
                uuid = '{' + uuidly.uuid1().urn[9:] + '}', \
                font_size=str(size), frame='false', \
                rotation='270')
        label_text = etree.SubElement(label, 'text')
        label_text.text = text
        label_color = etree.SubElement(label, 'color')
        label_color.text = '#555555'
        return label


    def _label_term_xref(self, father, x, y, text):
        """Generates a xml element that represents a label of a conductor centered
        on the terminal
        @ param father: xml node father
        @ param x: x pos. of the terminal
        @ param y: y pos. of the terminal
        @ param text: id of the terminal
        """
        size = 6
        x1 = x + (TerminalBlock.HEAD_WIDTH / 2) - TerminalBlock.TERMINAL_WIDTH - size + 5
        y1 = y + 70
        label = etree.SubElement(father, 'dynamic_text', \
                x=str(x1), \
                y=str(y1), \
                z='3', \
                text_from='UserText', \
                uuid = '{' + uuidly.uuid1().urn[9:] + '}', \
                font_size=str(size), frame='false', \
                rotation='270')
        label_text = etree.SubElement(label, 'text')
        label_text.text = text
        #label_color = etree.SubElement(label, 'color')
        #label_color.text = '#ff0000'  
        return label          