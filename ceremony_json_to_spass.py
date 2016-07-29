import json
import re
import os

class Spass(object):

    def __init__(self):
        counter = 1
        ceremony_file = "ceremony1.json"
        while(os.path.exists(ceremony_file)):
            print ceremony_file

            with open(ceremony_file, "r") as j_file:
                self.j = json.load(j_file)
            
            self.fromJson(counter)

            counter += 1
            ceremony_file = "ceremony"+str(counter)+".json"

    def fromJson(self,counter):
        self.peers=[] #no repetitions
        self.msgs=[] #no repetitions
        self.atts=[] #no repetitions

        self.peer1=[] #senders
        self.peer2=[] #receivers
        self.layer=[] #layers
        self.capab=[] #capabilities
        self.att=[] #attackers
        self.msg=[] #all in the order which they happened 

        self.sev = 0 #number of total not empty messages 

        for i in self.j["db"]: #for all messages
            if i["peer1"] not in self.peers and i["peer1"] != "": #not empty
                self.peers.append(i["peer1"]) #adds peer1 to peers if it is not already there

            elif i["peer2"] not in self.peers and i["peer2"] != "": #not empty
                self.peers.append(i["peer2"]) #adds peer2 to peers

            if i["peer1"] != "": #not empty
                self.peer1.append(i["peer1"]) #adds peer1s

            if i["peer2"] != "": #not empty
                self.peer2.append(i["peer2"]) #adds peer2s

            if i["layer"] != "": #not empty
                self.layer.append(i["layer"]) #adds layers

            if i["msg"] not in self.msgs and i["msg"] != "": #not empty
                self.msgs.append(i["msg"]) #adds all different messages

            if i["msg"] != "": #not empty
                self.sev += 1
                self.msg.append(i["msg"]) #adds all messages in order

            if i["att1"] not in self.atts and i["att1"] != "": #not empty and no repetitions
                self.atts.append(i["att1"]) #adds att to atts

        self.several = [False]*self.sev #indicates which messages have more than one attacker

        for i in range(len(self.j["db"])): #for all messages

            aux = 2 #for second attacker ahead
            self.capabAux = [self.j["db"][i]["capab1"]] #starts with the capab of the first att
            self.attAux = [self.j["db"][i]["att1"]] #starts with first att
 
            while "capab"+str(aux) in self.j["db"][i] and "capab"+str(aux) != "": #for capab2 ahead, while they exist AND NOT EMPTY
                self.several[i] = True #several for index i becames True
                self.capabAux.append(self.j["db"][i]["capab"+str(aux)]) #adds capab

                if self.j["db"][i]["att"+str(aux)] != "": #FOR NOT EMPTY ATT
                    self.attAux.append(self.j["db"][i]["att"+str(aux)])

                if self.j["db"][i]["att"+str(aux)] not in self.atts and self.j["db"][i]["att"+str(aux)] != "": #NOT EMPTY att added to atts if already not in
                    self.atts.append(self.j["db"][i]["att"+str(aux)])

                aux += 1 #increments aux and keep checking for further attackers

            if i < len(self.several): #for all msgs that have more than one attacker
                if self.several[i]:
                    self.capab.append(self.capabAux) #adds the set of capabilities as a list
                    self.att.append(self.attAux) #adds the set of attackers as a list

                else: #adds att and capab normally (even when empty) - ok
                    if self.msg[i] != "": #for not empty msgs (those needed only to fill in the layers space)
                        self.capab.append(self.j["db"][i]["capab1"]) #adds capab1 only as string
                        self.att.append(self.j["db"][i]["att1"]) #adds att1 only as string

        for i in range(len(self.several)):
            print i, self.several[i], self.peer1[i], self.peer2[i]
            print self.layer[i], self.capab[i], self.att[i]
            print self.msg[i]
            print "\n"

        print len(self.several), len(self.peer1), len(self.peer2), len(self.layer), len(self.capab), len(self.att), len(self.msg)
        print "\n"

        with open("ceremony_model.dfg", "r") as spassTxt:
            self.spass = spassTxt.read() #open what is already written in spass 'template' file

        self.write_dfg(counter) #calls the method to write the specifics to spass file


    def write_dfg(self, counter):
        self.db = "" 
        self.messages=""

##VARIABLES##
        for peer in self.peers:
            self.db += '({},0),\n'.format(peer.lower()) #all peers with no repetition are declared in spass

        self.knows="\n"

        self.keys = ""
        pairCase = False

        for index, msg in enumerate(self.msg): #for each message

            if "encr" in msg:
                match = re.search(r'\S+?\((\S+),(\S+)\)', msg) #searches for msg and key
                encr = match.groups() #gets the array containing the results of the search

		if encr[0] == "pair(email,password)":
                    self.db += '(email,0),\n'  
                    self.db += '(password,0),\n'
                    pairCase = True

                if '({},0),\n'.format(encr[0].lower()) not in self.db and not pairCase:
                    self.db += '({},0),\n'.format(encr[0].lower())  #adds declaration for message

                if '({},0),\n'.format(encr[1].lower())  not in self.db:
                    self.db += '({},0),\n'.format(encr[1].lower())  #adds declaration for key
        
                if 'Key({0}),key_{0}'.format(encr[1].lower()) not in self.keys:
                    self.keys += 'formula(Key({0}),key_{0}).\n'.format(encr[1].lower()) #adds Key predicate
               
                if encr[0] == "pair(email,password)" and 'formula(KnowsPair({0},pair(email,password)),agent_{0}_knows_pair_email_and_password).\n'.format(self.peer1[index].lower()) not in self.knows:
                    self.knows += 'formula(KnowsPair({0},pair(email,password)),agent_{0}_knows_pair_email_and_password).\n'.format(self.peer1[index].lower())

                if 'formula(Knows({0},{1})'.format(self.peer1[index].lower(),encr[0].lower()) not in self.knows and not "pair" in encr[0]:
                    self.knows += 'formula(Knows({0},{1}),agent_{0}_knows_{1}).\n'.format(self.peer1[index].lower(),encr[0].lower())
#               adds Knows predicate: Knows(Sender, Message) for each message

                if 'formula(Knows({0},{1}),agent_{0}_knows_key_{1}'.format(self.peer1[index].lower(),encr[1].lower()) not in self.knows:
                     self.knows += 'formula(Knows({0},{1}),agent_{0}_knows_key_{1}).\n'.format(self.peer1[index].lower(),encr[1].lower())
#               adds Knows predicate: Knows(Sender, Key) 


            else: #in the case no key is used
                if  '({},0),\n'.format(msg.lower()) not in self.db and not "pair(email,password)" in msg:
                    self.db += '({},0),\n'.format(msg.lower()) #message declaration
          
                if 'formula(Knows({0},{1})'.format(self.peer1[index].lower(),msg.lower()) not in self.knows and not "pair(email,password)" in msg:
                    self.knows += 'formula(Knows({0},{1}),agent_{0}_knows_{1}).\n'.format(self.peer1[index].lower(),msg.lower())


        for att in self.atts:
            if (att != ""):
                self.db += '({},0),\n'.format(att.lower()) #attackers declaration


        self.db += "\n"
      
        self.spass = self.spass.replace("%VARIABLES TODO\n\n", self.db) #variables listed above are now part of the spass file
        self.db = ""

##DECLARATIONS##

        for peer in self.peers: #for all peers
            self.db += 'formula(Agent({0}),agent_{0}).\n'.format(peer.lower()) #peers are agents (with no repetition)
            self.db += 'formula(Honest({0}),honest_{0}).\n'.format(peer.lower()) #all peers are honest

        self.db += self.keys +"\n" #write Key predicates to main string ;p
        self.db += self.messages #write the messages to main string :D
        self.db += self.knows +"\n" #write Knows predicates to main string
 
        dy = False

        for att in self.atts:
            att = att.lower()
            self.db += 'formula(Attacker({0}),attacker_{0}).\n'.format(att)

            if att == "dy" and not dy: #guarantees there is only one DY
                dy = True
                self.db += 'formula(DY({0}),DY_{0}).\n'.format(att)

            elif "da" in att:
                self.db += 'formula(DA({0}),DA_{0}).\n'.format(att)

            elif "ma" in att:
                self.db += 'formula(MA({0}),Ma_{0}).\n'.format(att) 

        self.db += "\n" #main string has all attackers, also

        self.steps(self.db, counter) #calls methods for ceremony steps




##STEPS#############################################################################

    def steps(self, db, counter):
        if self.several[0]: #if the very first message has more than one attacker
            info = self.firstStepSeveral(db)
        else:
            info = self.firstStep(db) #method for one attacker only in first message

        self.db = self.remainingSteps(info) #calls method for remaining steps!


        self.spass = self.spass.replace("%DECLARATIONS AND STEPS TODO", self.db) #writes all the remaining contents of the main string to spass file


        with open("ceremony"+str(counter)+".dfg","w") as bs:
            bs.write(self.spass) #updates spass file with its final version
#THE END!!!!!


    def firstStep(self,db): #one attacker!
        self.db = db
        form = ""
        next = ""

        if len(self.capab[0]) == 1:  # only one cap: 'N' , ' E' , ' S' ...

            if self.capab[0] == "N": #checked
                form += 'formula(\n\t{}_N(sent({},{},{})),\nstep1).\n\n'.format(self.layer[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower())
            
                next += '\t\t{}_N(sent({},{},{})),\n'.format(self.layer[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower())


            else: #for DY - {N} #checked
                form += 'formula(\n\t{}_{}(sent({},{},{}),{}),\nstep1).\n\n'.format(self.layer[0], self.capab[0],self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower(), self.att[0].lower())

                next += '\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], self.capab[0],self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower(), self.att[0].lower())


        else:  # more *capabilities* than just one 
            cap_set = self.capabilitiesArray(self.capab[0])

            form = "formula(\n\tand(\n" #needs and in the formulae
            next = "\t\tand(\n" #needs and in the formulae

            for i in range(len(cap_set) - 1): #for each capability but the last

                if cap_set[i] == "N": #checked
                    form += '\t\t{}_N(sent({},{},{})),\n'.format(self.layer[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower())

                    next += '\t\t\t{}_N(sent({},{},{})),\n'.format(self.layer[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower())

                else: #checked
                    form += '\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], cap_set[i], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower(), self.att[0].lower())

                    next += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], cap_set[i], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower(), self.att[0].lower())


            if cap_set[len(cap_set)-1] == "N": #fot the last capability #checked

                next += '\t\t\t{}_N(sent({},{},{}))\n\t\t),\n'.format(self.layer[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower())

                form += '\t\t{}_N(sent({},{},{}))\n\t),\nstep1).\n\n'.format(self.layer[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower())

            else: #checked
                next += '\t\t\t{}_{}(sent({},{},{}),{})\n\t\t),\n'.format(self.layer[0], cap_set[len(cap_set)-1], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower(), self.att[0].lower())

                form += '\t\t{}_{}(sent({},{},{}),{})\n\t),\nstep1).\n\n'.format(self.layer[0], cap_set[len(cap_set)-1], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower(), self.att[0].lower())

        self.db += form

        return [self.db, next]




    def capabilitiesArray(self, capab): #perfectly done q

        if len(capab) == 1 and capab.isalpha():
            return capab

        elif capab == "DY":
            return ["E", "B", "S", "I", "C", "O", "F"]

        else: 
            return capab.split("+")



    def remainingSteps(self,info):
        self.db = info[0]
        next = info[1]

        for index in range(1,len(self.msg)):

            form = "formula(\n\timplies(\n" + next #implies

            if self.several[index]: ##SEVERAL
              
                ssi = self.severalSteps(index)
                form += ssi[0]
                next = ssi[1]
 
            else: #ONLY ONE ATTACKER

                if len(self.capab[index]) == 1: ##ONLY ONE CAPABILITY!

                    if self.capab[index] == "N": #checked
                        form += '\t\t{}_N(sent({},{},{}))\n\t),\nstep{}).\n\n'.format(self.layer[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), str(index+1))

                        next = '\t\t{}_N(sent({},{},{})),\n'.format(self.layer[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), str(index+1))

                    else: #checked
                        form += '\t\t{}_{}(sent({},{},{}),{})\n\t),\nstep{}).\n\n'.format(self.layer[index], self.capab[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), self.att[index].lower(), str(index+1))

                        next = '\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[index], self.capab[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), self.att[index].lower(), str(index+1))


                else: # SEVERAL CAPABILITIES
                    form += "\t\tand(\n"
                    next = "\t\tand(\n"

                    cap_set = self.capabilitiesArray(self.capab[index])

                    for i in range(len(cap_set)-1): #all capabilities of the list but the last one
                        if cap_set[i] == "N": #checked

                            form += '\t\t\t{}_N(sent({},{},{})),\n'.format(self.layer[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), str(index+1))

                            next += '\t\t\t{}_N(sent({},{},{})),\n'.format(self.layer[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), str(index+1))

                        else: #checked
                            form += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[index], cap_set[i], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), self.att[index].lower(), str(index+1))

                            next += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[index], cap_set[i], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), self.att[index].lower(), str(index+1))


                    if cap_set[len(cap_set)-1] == "N": #last capability
                        form += '\t\t\t{}_N(sent({},{},{}))\n\t\t)\n\t),\nstep{}).\n\n'.format(self.layer[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), str(index+1))

                        next += '\t\t\t{}_N(sent({},{},{}))\n\t\t),\n'.format(self.layer[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), str(index+1))

                    else: #checked
                        form += '\t\t\t{}_{}(sent({},{},{}),{})\n\t\t)\n\t),\nstep{}).\n\n'.format(self.layer[index], cap_set[len(cap_set)-1], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), self.att[index].lower(), str(index+1))

                        next += '\t\t\t{}_{}(sent({},{},{}),{})\n\t\t),\n'.format(self.layer[index], cap_set[len(cap_set)-1], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), self.att[index].lower(), str(index+1))

            self.db += form

        return self.db


    def firstStepSeveral(self,db): #first msg - several
        self.db = db
        form = "formula(\n\tand(\n"
        next = "\t\tand(\n"


        for index in range(len(self.capab[0])):

            if len(self.capab[0][index]) == 1:  # only one cap: 'N' , ' E' , ' S' ...

                if self.capab[0][index] == "N": #checked
                    form += '\t\t{}_N(sent({},{},{})),\n'.format(self.layer[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower())

                    next += '\t\t\t{}_N(sent({},{},{})),\n'.format(self.layer[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower())

                else: #checked
                    form += '\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], self.capab[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower(), self.att[0].lower())

                    next += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], self.capab[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower(), self.att[0].lower())


            else:  # more capabilities than just one (DY or N + E + B ...and so on and so forth)
                cap_set = self.capabilitiesArray(self.capab[0][index])

                for i in range(len(cap_set) - 1):
                    if cap_set[i] == "N":

                        form += '\t\t{}_N(sent({},{},{})),\n'.format(self.layer[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower())

                        next += '\t\t\t{}_N(sent({},{},{})),\n'.format(self.layer[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower())

                    else:
                        form += '\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], cap_set[i], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower(), self.att[0].lower())

                        next += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], cap_set[i], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower(), self.att[0].lower())


                if cap_set[len(cap_set) - 1] == "N": #last capability

                    next += '\t\t{}_N(sent({},{},{})),\n\t\t),\n'.format(self.layer[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower())

                    form += '\t\t\t{}_N(sent({},{},{})),\n\t),\nstep1).\n\n'.format(self.layer[0], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower())

                else:
                    next += '\t\t\t{}_{}(sent({},{},{}),{})\n\t\t),\n'.format(self.layer[0], cap_set[len(cap_set) - 1], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower(), self.att[0].lower())

                    form += '\t\t{}_{}(sent({},{},{}),{})\n\t),\nstep1).\n\n'.format(self.layer[0], cap_set[len(cap_set) - 1], self.peer1[0].lower(), self.peer2[0].lower(), self.msg[0].lower(), self.att[0].lower())


            self.db += form

        return [self.db, next]


    def severalSteps(self, index):

        form = "\t\tand(\n"
        next = "\t\tand(\n"

        for i_cap in range(len(self.capab[index])): #[DY,DY]


            if len(self.capab[index][i_cap]) == 1: 

                if self.capab[index] == "N":
                    form += '\t\t{}_N(sent({},{},{}))\n\t),\nstep{}).\n\n'.format(self.layer[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(),str(index + 1))

                    next = '\t\t{}_N(sent({},{},{})),\n'.format(self.layer[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower())

                else:
                    form += '\t\t{}_{}(sent({},{},{}),{})\n\t),\nstep{}).\n\n'.format(self.layer[index], self.capab[index][i_cap], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), self.att[index][i_cap].lower(),str(index+1))
                    

                    next = '\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[index], self.capab[index][i_cap], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), self.att[index][i_cap].lower())


            else:
                cap_set = self.capabilitiesArray(self.capab[index][i_cap])

                for i in range(len(cap_set)-1):

                    if cap_set[i] == "N":
                        
                        form += '\t\t\t{}_N(sent({},{},{})),\n'.format(self.layer[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(),str(index + 1))
        
                        next += '\t\t{}_N(sent({},{},{})),\n'.format(self.layer[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(),str(index + 1))


                    else:
                        form += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[index], cap_set[i], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), self.att[index][i_cap].lower())

                        next += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[index], cap_set[i], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), self.att[index][i_cap].lower())


                if cap_set[len(cap_set)-1] == "N":
                    form += '\t\t\t{}_N(sent({},{},{}))\n\t\t),\nstep{}).\n\n'.format(self.layer[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(),str(index + 1))

                    next +='\t\t\t{}_N(sent({},{},{}))\n\t\t),\n'.format(self.layer[index], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower())


                else:
                    form += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[index], cap_set[len(cap_set)-1], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), self.att[index][i_cap].lower())


                    next += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[index], cap_set[len(cap_set)-1], self.peer1[index].lower(), self.peer2[index].lower(), self.msg[index].lower(), self.att[index][i_cap].lower())


        form = form[:-2]
        form += '\n\t\t)\n\t),\nstep{}).\n\n'.format(str(index+1))

        next = next[:-2]
        next += "\n\t\t),\n"


        return [form,next]



spass = Spass()



