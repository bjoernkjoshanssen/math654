forall = '∀'
exists = '∃'
mp     = '→'
land   = '∧'
lor    = '∨'
lnot   = '¬'
liff   = '↔'

def checkFormula(fmla):
	r0 = [*fmla]
	r0.reverse()
	r1 = ['F']
	while r0 != []:
		print(r0,r1)
		if r0[-1] in [forall,exists]:
			if r1[-1] == 'F':
				r1.append('V')
			else:
				print("Not a formula due to",r0[-1])
				break

		if r0[-1] in ['x','a','y','c','0','1']: # add more single-symbol variables and constants as needed
			if r1[-1] == 'V' or r1[-1] == 'T':
				r1.pop()

		if r0[-1] == lnot:
			if r1[-1] == 'F':
				pass
			else:
				print("Not a formula due to",r0[-1])
				break

		if r0[-1] in [mp,land,lor,liff]:
			if r1[-1] == 'F':
				r1.append('F')
			else:
				print("Not a formula due to",r0[-1])
				break

		if r0[-1] == '=':
			if r1[-1] == 'F':
				r1.pop()
				r1.append('T')
				r1.append('T')
			else:
				print("Not a formula due to",r0[-1])
				break

		if r0[-1] == '+' or r0[-1] == '*':
			if r1[-1] == 'T':
				r1.append('T')
			else:
				print("Not a formula due to",r0[-1])
				break
		r0.pop()


fmla = '∀x∀y→=+ax+ay=xy'
checkFormula(fmla)

fmla = '∀x∀y→*ax*ay=xy'
checkFormula(fmla)

fmla = '∀x∀y→=x*ay=xy'
checkFormula(fmla)

fmla = '∀x∀y→=*ax*ay=x*aa'
checkFormula(fmla)

checkFormula([forall,forall])
