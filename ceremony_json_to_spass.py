import json
import re
import os

class Spass(object):

    def __init__(self):
        counter = 1
        ceremony_file = "ceremony1.json"
        while(os.path.exists(ceremony_file)):
            print "-------------------------------------------" +ceremony_file + "-------------------------------------------------------"

            with open(ceremony_file, "r") as j_file:
                self.j = json.load(j_file)

            self.fromJsonToSpass(counter)

            counter += 1
            ceremony_file = "ceremony"+str(counter)+".json"


#NOW RUN SPASS!

        spass_number = 1
        spass_file = "ceremony1.dfg"

        while(os.path.exists(spass_file)):

            print spass_file
            os.system('SPASS -DocProof ceremony{0}.dfg > ceremony{0}.txt'.format(str(spass_number)))
            spass_number += 1
            spass_file = "ceremony"+str(spass_number)+".dfg"



    def fromJsonToSpass(self,counter):

        self.peers=[] #no repetitions - senders and receivers
        self.msgs=[] #no repetitions
        self.atts=[] #no repetitions

        self.sender=[] #senders
        self.receiver=[] #receivers
        self.layer=[] #layers
        self.capab=[] #capabilities
        self.att=[] #attackers - possible blank
        self.msg=[] #all messages in the order which they happened

        for i in self.j["ceremony"]: #for all messages

            if i["sender"] == "" or i["receiver"] == "" or i["layer"] == "" or i["message"] == "":
                return 0

            if i["sender"] not in self.peers:
                self.peers.append(i["sender"]) #adds peer1 to peers if it is not already there

            if i["receiver"] not in self.peers:
                self.peers.append(i["receiver"]) #adds peer2 to peers if it is not already there

            if i["message"] not in self.msgs:
                self.msgs.append(i["message"]) #adds all different messages

            self.sender.append(i["sender"]) #adds peer1s
            self.receiver.append(i["receiver"]) #adds peer2s
            self.layer.append(i["layer"]) #adds layers
            self.msg.append(i["message"]) #adds all messages in order

            if len(i["attackers"]) == 0:
                self.att.append([])
                self.capab.append(["N"])

            else:
                attackers = []
                capabilities = []

                for attacker in i["attackers"]:

                    if attacker not in self.atts:
                       self.atts.append(attacker["attacker"]) #adds att to atts

                    attackers.append(attacker["attacker"])
                    capabilities.append(attacker["capability"])

                self.att.append(attackers)
                self.capab.append(capabilities)


#-----------------------------------Reading finished, all variables stored from json file---------------------------------------------------------



        with open("ceremony_model.dfg", "r") as spassModel:
            self.spass = spassModel.read() #open what is already written in spass 'model' file

        self.write_SPASS(counter) #calls the method to write the specifics to spass file



#-----Starting SPASS specifications---------------------------------------------------------------------------------------------------------------


    def write_SPASS(self, counter):
        self.ceremony = ""
        self.messages= ""
        self.conjectures = ""

##VARIABLES##
        for peer in self.peers:
            self.ceremony += '({},0),\n'.format(peer.lower()) #all peers with no repetition are declared in spass

        self.knows="\n"
        self.keys = ""

        for index, msg in enumerate(self.msg): #for each message

            pairCase = False

            if "encr" in msg:
                match = re.search(r'\S+?\((\S+),(\S+)\)', msg) #searches for msg and key
                encr = match.groups() #gets the array containing the results of the search

                if encr[0] == "pair(email,password)":
                    self.ceremony += '(email,0),\n'
                    self.ceremony += '(password,0),\n'
                    pairCase = True

                if '({},0),\n'.format(encr[0].lower()) not in self.ceremony and not pairCase:
                    self.ceremony += '({},0),\n'.format(encr[0].lower())  #adds declaration for message as a variable

                if '({},0),\n'.format(encr[1].lower())  not in self.ceremony:
                    self.ceremony += '({},0),\n'.format(encr[1].lower())  #adds declaration for key as a variable

                if 'Key({0}),key_{0}'.format(encr[1].lower()) not in self.keys:
                    self.keys += 'formula(Key({0}),key_{0}).\n'.format(encr[1].lower()) #adds Key predicate

                if encr[0] == "pair(email,password)" and 'formula(KnowsPair({0},pair(email,password)),agent_{0}_knows_pair_email_and_password).\n'.format(self.sender[index].lower()) not in self.knows:
                    self.knows += 'formula(KnowsPair({0},pair(email,password)),agent_{0}_knows_pair_email_and_password).\n'.format(self.sender[index].lower())
#               adds Knows predicate: Knows(Sender, Pair)

                if 'formula(Knows({0},{1})'.format(self.sender[index].lower(),encr[0].lower()) not in self.knows and not pairCase:
                    self.knows += 'formula(Knows({0},{1}),agent_{0}_knows_{1}).\n'.format(self.sender[index].lower(),encr[0].lower())
#               adds Knows predicate: Knows(Sender, Message) for each message

                if 'formula(Knows({0},{1}),agent_{0}_knows_key_{1}'.format(self.sender[index].lower(),encr[1].lower()) not in self.knows:
                     self.knows += 'formula(Knows({0},{1}),agent_{0}_knows_key_{1}).\n'.format(self.sender[index].lower(),encr[1].lower())
#               adds Knows predicate: Knows(Sender, Key) for the key

#CONJECTURES
                if len(self.att[index]) == 1:
                    if 'formula(KnowsEncr({0},{1})'.format(self.att[index][0].lower(),msg.lower()) not in self.conjectures:
                        self.conjectures += 'formula(KnowsEncr({0},{1}),attacker_{0}_knows_{2}).\n'.format(self.att[index][0].lower(),msg.lower(), msg.lower().replace("(", "_").replace(")", "_").replace(",","_"))

                elif len(self.att[index]) > 1:
                    for att in self.att[index]:
                        if 'formula(KnowsEncr({0},{1})'.format(att.lower(),msg.lower()) not in self.conjectures:
                            self.conjectures += 'formula(KnowsEncr({0},{1}),attacker_{0}_knows_{2}).\n'.format(att.lower(),msg.lower(), msg.lower().replace("(", "_").replace(")", "_").replace(",","_"))


            else: #in the case no key is used -- FOR UNENCRYPTED MESSAGES
                if  '({},0),\n'.format(msg.lower()) not in self.ceremony and not "pair(email,password)" in msg:
                    self.ceremony += '({},0),\n'.format(msg.lower()) #message declaration as a variable

                if 'formula(Knows({0},{1})'.format(self.sender[index].lower(),msg.lower()) not in self.knows and not "pair(email,password)" in msg:
                    self.knows += 'formula(Knows({0},{1}),agent_{0}_knows_{1}).\n'.format(self.sender[index].lower(),msg.lower())
#               adds Knows predicate: Knows (Sender, Message)

                if len(self.att[index]) == 1:
                    if 'formula(Knows({0},{1})'.format(self.att[index][0].lower(),msg.lower()) not in self.conjectures:
                        self.conjectures += 'formula(Knows({0},{1}),attacker_{0}_knows_{2}).\n'.format(self.att[index][0].lower(),msg.lower(), msg.lower().replace("(", "_").replace(")", "_").replace(",","_"))

                elif len(self.att[index]) > 1:
                    for att in self.att[index]:
                        if 'formula(Knows({0},{1})'.format(att.lower(),msg.lower()) not in self.conjectures:
                            self.conjectures += 'formula(Knows({0},{1}),attacker_{0}_knows_{2}).\n'.format(att.lower(),msg.lower(), msg.lower().replace("(", "_").replace(")", "_").replace(",","_"))



        for att in self.atts:
            if (att != "") and not "("+att.lower()+",0)," in self.ceremony:
                self.ceremony += '({},0),\n'.format(att.lower()) #attackers declaration as a variable


        self.ceremony += "\n"

        self.spass = self.spass.replace("%VARIABLES TODO\n\n", self.ceremony) #variables listed above are now part of the spass file
        self.ceremony = ""

##DECLARATIONS##

        for peer in self.peers: #for all peers -- CONSIDERING THAT NO AGENT IS ALSO AN ATTACKER!!!!!!!!!!!!!
            self.ceremony += 'formula(Agent({0}),agent_{0}).\n'.format(peer.lower()) #peers are agents (with no repetition)
            self.ceremony += 'formula(Honest({0}),honest_{0}).\n'.format(peer.lower()) #all peers are honest

        self.ceremony += self.keys +"\n" #adds Key predicates to main string ;p
        self.ceremony += self.messages +"\n" #adds messages to main string :D
        self.ceremony += self.knows +"\n" #adds Knows predicates to main string

        for att in self.atts:
            att = att.lower()
            if not "formula(Attacker("+att+"),attacker_"+att+").\n" in self.ceremony:
                self.ceremony += 'formula(Attacker({0}),attacker_{0}).\n'.format(att) #attacker predicate

            if att == "dy" and not "formula(DY(dy),DY_dy).\n" in self.ceremony:
                self.ceremony += 'formula(DY({0}),DY_{0}).\n'.format(att)

            elif "da" in att and not "formula(DA("+att+"),DA_"+att+").\n" in self.ceremony:
                self.ceremony += 'formula(DA({0}),DA_{0}).\n'.format(att)

            elif "ma" in att and not "formula(MA("+att+"),MA_"+att+").\n" in self.ceremony:
                self.ceremony += 'formula(MA({0}),MA_{0}).\n'.format(att)

        self.ceremony += "\n" #main string has all attackers at this point

        self.steps(self.ceremony, counter) #calls methods for ceremony steps


##STEPS#############################################################################

    def steps(self, ceremony, counter):
        if len(self.att[0]) > 1: #if the very first message has more than one attacker
            info = self.firstStepSeveral(ceremony)
        elif len(self.att[0]) == 1: #ONE ATTACKER ONLY
            info = self.firstStep(ceremony) #method for one attacker only in first message

        else: #no attacker = N
            form = 'formula(\n\t{}_N(sent({},{},{})),\nstep1).\n\n'.format(self.layer[0], self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower())
            previous = '\t\t{}_N(sent({},{},{})),\n'.format(self.layer[0], self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower())

            self.ceremony += form
            info = [self.ceremony, previous]

        self.ceremony = self.remainingSteps(info) #calls method for remaining steps!

        self.spass = self.spass.replace("%DECLARATIONS AND STEPS TODO", self.ceremony) #adds declarations and all messages to spass file
        self.spass = self.spass.replace("%CONJECTURES TODO", self.conjectures)

        with open("ceremony"+str(counter)+".dfg","w") as bs:
            bs.write(self.spass) #updates spass file with its final version

########################################################################################################################################################################################################

    def firstStep(self,ceremony): #one attacker!
        self.ceremony = ceremony
        form = ""
        previous = ""

        if not "+" in self.capab[0][0] and not "DY" in self.capab[0][0]:  # only one capability: ' E' , ' S' ...

            form += 'formula(\n\t{}_{}(sent({},{},{}),{}),\nstep1).\n\n'.format(self.layer[0], self.capab[0][0], self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower(), self.att[0][0].lower())
            previous += '\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], self.capab[0][0], self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower(), self.att[0][0].lower())


        else:  # more *capabilities* than just one
            cap_set = self.capabilitiesArray(self.capab[0])

            form = "formula(\n\tand(\n" #needs and in the formulae
            previous = "\t\tand(\n" #needs and in the formulae

            for capability in cap_set[:-1]: #for each capability but the last

                form += '\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], capability, self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower(), self.att[0][0].lower())
                previous += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], capability, self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower(), self.att[0][0].lower())

            previous += '\t\t\t{}_{}(sent({},{},{}),{})\n\t\t),\n'.format(self.layer[0], cap_set[-1], self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower(), self.att[0][0].lower())
            form += '\t\t{}_{}(sent({},{},{}),{})\n\t),\nstep1).\n\n'.format(self.layer[0], cap_set[-1], self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower(), self.att[0][0].lower())

        self.ceremony += form

        return [self.ceremony, previous]


    def capabilitiesArray(self, capab): #perfect

        if capab == "DY":
            return ["E", "B", "S", "I", "C", "O", "F"]

        else:
            return capab[0].split("+")


    def firstStepSeveral(self,ceremony): #first msg - several

        self.ceremony = ceremony
        form = "formula(\n\tand(\n"
        previous = "\t\tand(\n"

        for index, att in enumerate(self.att[0]):

            if len(self.capab[0][index]) == 1:  # only one cap: ' E' , ' S' ...

                form += '\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], self.capab[0], self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower(), att.lower())
                previous += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], self.capab[0], self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower(), att.lower())

            else:  # more capabilities than just one (DY or  E + B ...and so on and so forth)
                cap_set = self.capabilitiesArray(self.capab[0][index])

                for capab in cap_set[:-1]:

                        form += '\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], capab, self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower(), att.lower())
                        previous += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[0], capab, self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower(), att.lower())

                previous += '\t\t\t{}_{}(sent({},{},{}),{})\n\t\t),\n'.format(self.layer[0], cap_set[-1], self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower(), att.lower())
                form += '\t\t{}_{}(sent({},{},{}),{})\n\t),\nstep1).\n\n'.format(self.layer[0], cap_set[-1], self.sender[0].lower(), self.receiver[0].lower(), self.msg[0].lower(), att.lower())

            self.ceremony += form
            return [self.ceremony, previous]



    def remainingSteps(self,info):
        self.ceremony = info[0]
        previous = info[1]

        msg1 = self.msg[1:]
        index = 1

        for msg in msg1:

            form = "formula(\n\timplies(\n" + previous #implies

            if len(self.att[index]) == 0: #NO ATTACKER

                form += '\t\t{}_N(sent({},{},{}))\n\t),\nstep{}).\n\n'.format(self.layer[index], self.sender[index].lower(), self.receiver[index].lower(), msg.lower(), str(index+1))
                previous = '\t\t{}_N(sent({},{},{})),\n'.format(self.layer[index], self.sender[index].lower(), self.receiver[index].lower(), msg.lower())


            elif len(self.att[index]) == 1: #ONLY ONE ATTACKER
                if len(self.capab[index][0]) == 1: ##ONLY ONE CAPABILITY!

                    form += '\t\t{}_{}(sent({},{},{}),{})\n\t),\nstep{}).\n\n'.format(self.layer[index], self.capab[index][0], self.sender[index].lower(), self.receiver[index].lower(), self.msg[index].lower(), self.att[index][0].lower(), str(index+1))
                    previous = '\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[index], self.capab[index][0], self.sender[index].lower(),self.receiver[index].lower(), self.msg[index].lower(), self.att[index][0].lower())

                else: # SEVERAL CAPABILITIES
                    form += "\t\tand(\n"
                    previous = "\t\tand(\n"

                    for capability in self.capab[index]:

                        cap_set = self.capabilitiesArray(capability)

                        for capab in cap_set[:-1]: #all capabilities of the list but the last one

                            form += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[index], capab, self.sender[index].lower(), self.receiver[index].lower(), msg.lower(), self.att[index][0].lower(), str(index+1))
                            previous += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[index], capab, self.sender[index].lower(), self.receiver[index].lower(), msg.lower(), self.att[index][0].lower())

                        form += '\t\t\t{}_{}(sent({},{},{}),{})\n\t\t)\n\t),\nstep{}).\n\n'.format(self.layer[index], cap_set[-1], self.sender[index].lower(), self.receiver[index].lower(), msg.lower(), self.att[index][0].lower(), str(index+1))
                        previous += '\t\t\t{}_{}(sent({},{},{}),{})\n\t\t),\n'.format(self.layer[index], cap_set[-1], self.sender[index].lower(), self.receiver[index].lower(), msg.lower(), self.att[index][0].lower())


            else: #SEVERAL ATTACKERS
                ssi = self.severalSteps(index)
                form += ssi[0]
                previous = ssi[1]

            self.ceremony += form
            index += 1

        return self.ceremony



    def severalSteps(self, i):

        form = "\t\tand(\n"
        previous = "\t\tand(\n"

        for index, att in enumerate(self.att[i]):

            if len(self.capab[i][index]) == 1:

                form += '\t\t{}_{}(sent({},{},{}),{})\n\t),\nstep{}).\n\n'.format(self.layer[i], self.capab[i][index], self.sender[i].lower(), self.receiver[i].lower(), self.msg[i].lower(), att.lower(),str(i+1))
                previous = '\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[i], self.capab[i][index], self.sender[i].lower(), self.receiver[i].lower(), self.msg[i].lower(), att.lower())

            else: #more than one capab

                cap_set = self.capabilitiesArray(self.capab[i][index])

                for cap in cap_set[:-1]:

                    form += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[i], cap, self.sender[i].lower(), self.receiver[i].lower(), self.msg[i].lower(), att.lower())
                    previous += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[i], cap, self.sender[i].lower(), self.receiver[i].lower(), self.msg[i].lower(), att.lower())

                form += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[i], cap_set[-1], self.sender[i].lower(), self.receiver[i].lower(), self.msg[i].lower(), att.lower())
                previous += '\t\t\t{}_{}(sent({},{},{}),{}),\n'.format(self.layer[i], cap_set[-1], self.sender[i].lower(), self.receiver[i].lower(), self.msg[i].lower(), att.lower())


        form = form[:-2]
        form += '\n\t\t)\n\t),\nstep{}).\n\n'.format(str(i+1))

        previous = previous[:-2]
        previous += "\n\t\t),\n"

        return [form,previous]



spass = Spass()
