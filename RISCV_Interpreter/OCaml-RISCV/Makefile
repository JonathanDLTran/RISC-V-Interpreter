MODULES=ast ast_factory parse eval main 
OBJECTS=$(MODULES:=.cmo)
MLS=$(MODULES:=.ml)
MLIS=$(MODULES:=.mli)
TEST=test.byte
MAIN=main.byte
VISUAL=visual.byte
OCAMLBUILD=ocamlbuild -use-ocamlfind
PKGS=oUnit,str

default: build
	utop

run:
	$(OCAMLBUILD) $(MAIN) && ./$(MAIN)

build:
	$(OCAMLBUILD) $(OBJECTS)

test:
	$(OCAMLBUILD) -tag debug $(TEST) && ./$(TEST)

bisect-test:
	BISECT_COVERAGE=YES $(OCAMLBUILD) -tag 'debug' $(TEST) && ./$(TEST) -runner sequential

bisect: clean bisect-test
	bisect-ppx-report -I _build -html report bisect0001.out

repl:
	$(OCAMLBUILD) $(REPL) && ./$(REPL)

check:
	bash checkenv.sh && bash checktypes.sh

finalcheck: check
	bash checkzip.sh
	bash finalcheck.sh

zip:
	zip a6src.zip *.ml* _tags Makefile

docs: docs-public docs-private

docs-public: build
	mkdir -p doc.public
	ocamlfind ocamldoc -I _build -package $(PKGS) \
		-html -stars -d doc.public $(MLIS)

docs-private: build
	mkdir -p doc.private
	ocamlfind ocamldoc -I _build -package $(PKGS) \
		-html -stars -d doc.private \
		-inv-merge-ml-mli -m A -hide-warnings $(MLIS) $(MLS)

clean:
	ocamlbuild -clean
	rm -rf doc.public doc.private a6src.zip report bisect*.out
	
