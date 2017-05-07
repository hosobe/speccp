TARGET = speccp
OBJS = SpecCp.cmo test.cmo
LIBS = bigarray.cma
OCAMLC = ocamlc -g

speccp: $(OBJS)
	$(OCAMLC) -o $(TARGET) $(LIBS) $(OBJS)

SpecCp.cmo: SpecCp.ml
	$(OCAMLC) -c $<

test.cmo: test.ml SpecCp.ml
	$(OCAMLC) -c $<

clean:
	rm -f $(TARGET) $(OBJS)
