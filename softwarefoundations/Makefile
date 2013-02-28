opts = -opt
coqc = coqc $(opts)

all: Basics.vo Lists.vo Poly.vo Gen.vo Prop.vo

Basics.vo: Basics.v
	$(cocq) Basics.v

Lists.vo: Basics.vo Lists.v
	$(cocq) Lists.v

Poly.vo: Lists.vo Poly.v
	$(cocq) Poly.v

Gen.vo: Poly.vo Gen.v
	$(cocq) Gen.v

Prop.vo: Poly.vo Prop.v
	$(coqc) Prop.v

clean:
	rm -f *.glob *.vo
