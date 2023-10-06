PREPROCESSOR ?= ../ext/jasmin-preprocessor/preprocessor
JASMIN ?= jasminc

run: map
	./map

map: map.c map.s
	$(CC) -Wall -o $@ $^

map.s: map.jpp
	$(JASMIN) -o $@ $<

map.jpp: map.jazz
	$(PREPROCESSOR) --input_file $< --output_file $@

#--
extract: map_optimized.ec map_simple.ec

map_optimized.ec: map.jpp
	$(JASMIN) -oec $@ -ec __map_optimized_plus_one_u64_16_4 $<

map_simple.ec: map.jpp
	$(JASMIN) -oec $@ -ec __map_simple_plus_one_u64_16 $<

#--
clean:
	rm -f map

distclean: clean
	rm -f map.jpp map.s map_optimized.ec map_simple.ec WArray128.ec Array16.ec
