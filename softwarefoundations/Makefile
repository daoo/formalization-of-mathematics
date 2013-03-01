opts = -opt
coqc = coqc $(opts)

all: Basics.vo Lists.vo Poly.vo Gen.vo Prop.vo Logic.vo

Basics.vo: Basics.v
	$(coqc) Basics.v

Lists.vo: Basics.vo Lists.v
	$(coqc) Lists.v

Poly.vo: Lists.vo Poly.v
	$(coqc) Poly.v

Gen.vo: Poly.vo Gen.v
	$(coqc) Gen.v

Prop.vo: Poly.vo Prop.v
	$(coqc) Prop.v

Logic.vo: Prop.vo Logic.v
	$(coqc) Logic.v

clean:
	rm -f *.glob *.vo
