from z3 import*


#############################################################################################################
#																											#
#													Lógica												    #
#																											#
#############################################################################################################

def SPC(inst):
	return SPCaux(inst)[0]


def SPCaux(inst):
	if not inst:
		return False,False

	h = inst[-1]
	typ,pars = h 
	
	if typ == "alternative":
		lef = SPCaux(inst[:-1] + pars[0])
		rig = SPCaux(inst[:-1] + pars[1])
		rzt = Or(lef[0],rig[0])

		return rzt,True


	
	zt,h = SPCaux(inst[:-1])
	if h:
		if typ == "assume":
			rzt = And(zt,pars[0])

		elif typ == "assert":
			rzt = Implies(zt,pars[0])

		elif typ == "skip":
			rzt = zt

		elif typ == "atrib":
			rzt = And(zt,pars[0] == pars[2])

	else:
		if typ == "assume":
			rzt = pars[0]

		elif typ == "assert":
			rzt = pars[0]

		elif typ == "skip":
			rzt = True

		elif typ == "atrib":
			rzt = pars[0] == pars[2]

	return rzt,True


###################################################################################################
def WPC(inst):
	return WPCaux(inst)[0]


def WPCaux(inst):
	if not inst:
		return False,False

	typ,pars = inst[0]
	
	if typ == "alternative":
		e = pars[0].copy()
		d = pars[1].copy()
		e.extend(inst[1:])
		d.extend(inst[1:])
		lef = WPCaux(e)
		rig = WPCaux(d)

		rzt = And(lef[0],rig[0])
		return rzt,True


	zt,h = WPCaux(inst[1:])
	if h:
		if typ == "assume":
			rzt = Implies(pars[0],zt)

		elif typ == "assert":
			rzt = And(pars[0],zt)

		elif typ == "havoc":
			rzt = ForAll(pars[0],zt)



		elif typ == "skip":
			rzt = zt

		elif typ == "atrib":
			rzt = substitute(zt,(pars[0],pars[2]))

	else:
		if typ == "assume":
			rzt = BoolVal(True)

		elif typ == "assert":
			rzt = pars[0]

		elif typ == "skip":
			rzt = BoolVal(True)

		elif typ == "atrib":
			rzt = BoolVal(True)

	return rzt,True



#############################################################################################################
#																											#
#													STRINGS													#
#																											#
#############################################################################################################


def SPCstr(inst):
	return SPCstraux(inst)[0]

def SPCstraux(inst):
	if not inst:
		return "",False

	h = inst[-1]
	typ,pars = h 
	
	if typ == "alternative":
		lef = SPCstraux(inst[:-1] + pars[0])
		rig = SPCstraux(inst[:-1] + pars[1])

		rst = f"({lef[0]}) ∨ ({rig[0]})\n"

		return rst,True


	
	st,h = SPCstraux(inst[:-1])
	if h:
		if typ == "assume":
			rst = f" ({st}) ∧ ({pars[1]})"

		elif typ == "assert":
			rst = f"({st}) → ({pars[1]})"


		elif typ == "skip":
			rst = st


		elif typ == "atrib":
			rst = f"({pars[1]} == {pars[3]}) ∧ ({st})"

	else:
		if typ == "assume":
			rst = pars[1]

		elif typ == "assert":
			rst = pars[1]


		elif typ == "skip":
			rst = "True"


		elif typ == "atrib":
			rst = f"({pars[1]} == {pars[3]})"


	return rst,True


####################################################################
def WPCstr(inst):
	return WPCstraux(inst)[0]


def WPCstraux(inst):
	if not inst:
		return False,""

	typ,pars = inst[0]
	
	if typ == "alternative":
		e = pars[0].copy()
		d = pars[1].copy()
		e.extend(inst[1:])
		d.extend(inst[1:])
		lef = WPCstraux(e)
		rig = WPCstraux(d)

		rst = f"({lef[0]}) ∧ ({rig[0]})"
		return rst,True


	st,h = WPCstraux(inst[1:])
	if h:
		if typ == "assume":
			rst = f"({pars[1]}) → ({st})"

		elif typ == "assert":
			rst = f"({pars[1]}) ∧ ({st})"

		elif typ == "havoc":
			rst = f"∀{pars[1]} ({st})"



		elif typ == "skip":
			rst = st


		elif typ == "atrib":
			rst = f"({st}) [{pars[3]}/{pars[1]}]"

	else:
		if typ == "assume":
			rst = "True"


		elif typ == "assert":
			rst = pars[1]

		elif typ == "skip":
			rst = "True"


		elif typ == "atrib":
			rst = "True"

	return rst,True


####################################################################

def FLOW(inst):
	return FLOWaux(inst,0)



def FLOWaux(inst,ident):
	if not inst:
		return ""

	h = inst[0]
	typ,pars = h 
	
	if typ == "alternative":
		lef = FLOWaux(pars[0].copy(), ident+1)
		rig = FLOWaux(pars[1].copy(), ident+1)

		rst = ("  " * ident) + f"({lef} \n{'  ' * ident}||\n{rig}{'  ' * ident});\n{FLOWaux(inst[1:],ident)}"

		return rst

	a = FLOWaux(inst[1:],ident)

	if typ == "assume":
		rst =  "  " * ident + f"assume {pars[1]};\n{a}"

	elif typ == "assert":
		rst = "  " * ident + f"assert {pars[1]};\n{a}"

	elif typ == "skip":
		rst = "  " * ident + f"skip;\n{a}"

	elif typ == "atrib":
		rst = "  " * ident + f"{pars[1]} = {pars[3]};\n{a}"

	elif typ == "havoc":
		rst = "  " * ident + f"havoc {pars[1]};\n{a}"
	
	return rst






#############################################################################################################
#																											#
#													FLOWS													#
#																											#
#############################################################################################################

# HAVOC

bits = 16
x,y,m,n,r = BitVecs("x y m n r",bits)

inv = And(m*n == x*y + r,y >= 0)
invStr = "m * n == x * y + r and y >= 0"

pre = And( m>=0, n>=0, r == 0, x == m, y == n)
preStr = "m >= 0 and n >= 0 and r == 0 and x == m and y == n"

pos = r == m*n
posStr = "r == m*n"



havocInternIF = [
					("assume", [y&1 == 1, "y & 1 == 1"]),
					("atrib", [y, "y", y-1, "y-1"]),
					("atrib", [r, "r", r+x, "r+x"])
				]

havocInternElse = [
					("assume", [Not(y&1 == 1), "not(y & 1 == 1)"]),
					("skip",[])
				  ]


havocThen = [
				("assume", [And(y > 0, inv) , f"y > 0 and {invStr}"]),
				("alternative", [havocInternIF, havocInternElse]),
				("atrib", [x, "x", x<<1, "x<<1"]),
				("atrib", [y, "y", y>>1, "y>>1"]),
				("assert", [inv,invStr]),
				("assume",[False,"False"])
			]



havocElse = [
				("assume", [And(Not(y>0),inv), f"not(y > 0) and {invStr}"])
			]


havoc  = [
			("assume", [pre,preStr]),
		 	("assert", [inv,invStr]),
		 	("havoc", [x,"x"]),
		 	("havoc", [y,"y"]),
		 	("alternative", [havocThen,havocElse]),
		 	("assert", [pos,posStr])
		 ]






##############################################################################################################

#  UNFOLD

maxFold = 16
bits = 16
varbs = {
		 "y":[BitVec(f"y{i}",bits) for i in range((maxFold+1)*2)], 
		 "x":[BitVec(f"x{i}",bits) for i in range(maxFold+1)],
		 "r":[BitVec(f"r{i}",bits) for i in range(maxFold+1)],
		 "m":[BitVec(f"m0",bits)],
		 "n":[BitVec(f"n0",bits)]
		}




def internPattern(varbs,i):
	internThen = [
					("assume",[varbs["y"][(2*i)] & 1 == 1, f"y{(2*i)} & 1 == 1"]),
					("atrib",[varbs["y"][(2*i)+1], f"y{(2*i)+1}",varbs["y"][(2*i)] - 1,f"y{(2*i)} - 1"]),
					("atrib",[varbs["r"][i+1], f"r{i+1}",varbs["r"][i] + varbs["x"][i],f"r{i} + x{i}"])
				]
	
	internElse = [
					("assume",[Not(varbs["y"][(2*i)] & 1 == 1), f"not(y{(2*i)} & 1 == 1)"]),
					("atrib",[varbs["y"][(2*i)+1], f"y{(2*i)+1}", varbs["y"][(2*i)],  f"y{(2*i)}"]),
					("atrib",[varbs["r"][i+1], f"r{i+1}", varbs["r"][i],  f"r{i}"])
				]
	

	res = [
			("alternative",[internThen,internElse]),
			("atrib",[varbs["y"][(2*i)+2],f"y{(2*i)+2}",varbs["y"][(2*i)+1] >> 1, f"y{(2*i)+1} >> 1"]),
			("atrib",[varbs["x"][i+1],f"x{i+1}",varbs["x"][i] << 1, f"x{i} << 1"])
		]

	return res




def unfold(N):
	
	pre = And(varbs["m"][0]>= 0, varbs["n"][0]>= 0, varbs["r"][0] == 0, varbs["x"][0] == varbs["m"][0], varbs["y"][0] == varbs["n"][0])
	prestr = "m0 >= 0 and n0 >= 0 and r0 == 0 and x0 == m0 and y0 == n0"

	pos = And(varbs["r"][maxFold] == varbs["m"][0] * varbs["n"][0])
	postr = f"r{maxFold} == m0 * n0"

	acc = [("assume", [pre, prestr])]

	


	for i in range(N):
		body = internPattern(varbs,i)

		acc += [
				("assume",[varbs["y"][(2*i)] > 0, f"y{(2*i)} > 0"]),
				*body
				]

	if N != maxFold:
		acc += [
				("assume", [Not(varbs["y"][(2*N)] > 0), f"not(y{(2*N)} > 0)"]),
				("atrib", [varbs["y"][2*maxFold], f"y{maxFold}", varbs["y"][2*N],  f"y{N}"]),
				("atrib", [varbs["x"][maxFold], f"x{maxFold}", varbs["x"][N],  f"x{N}"]),
				("atrib", [varbs["r"][maxFold], f"r{maxFold}", varbs["r"][N],  f"r{N}"]),
				("assert", [pos, postr])
			   ]

	else:
		acc += [
		("assert",[And(pos,Not(varbs["y"][2*maxFold] > 0)), postr + f" and not(y{2*maxFold} > 0)"])
		]

	

	return acc



#############################################################################################################
#																											#
#													PROVES													#
#																											#
#############################################################################################################

# PROVE HAVOC

def prove(f):
    s = Solver()
    s.add(Not(f))
    r = s.check()
    if r == unsat:
        print("Proved")
    elif r == sat:
        print("Failed to prove")
        m = s.model()
        for v in m:
            print(v,'=', m[v])
    elif r == unknown:
        print("unknown")

# PROVE UNFOLD

def proveUnfold():

	for i in range(maxFold):
		print(f"Unfolding {i}...")
		res = unfold(i)
		zExp = SPC(res)

		print(f"Solving for unfold {i}...")
		
		s = Solver()
		s.add(Not(zExp))
		res = s.check()
		
		if res == unsat:
			print(f"Proved for unfold {i}!")
		
		elif res == sat:
			m = s.model()
			for i in m:
				print(f"{i} = {m[i]}")
			print(f"Could not Prove for unfold {i}")
		
		else:
			print(f"Unknown result for unfold {i}")

	return


#############################################################################################################
#																											#
#												Exemplos												    #
#																											#
#############################################################################################################



# tudo com 16 bits 
print(FLOW(havoc))
print(WPCstr(havoc))

logic = WPC(havoc)

prove(logic)

unfold5 = unfold(5)

print(FLOW(unfold5))
print(SPCstr(unfold5))
logic = SPC(unfold5)

prove(logic)

proveUnfold()

