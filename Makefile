# Build wrapper around `coq_makefile` (Rocq 9: `rocq makefile`).
# Mirrors LernaSpec/dimsum's pattern: proper .vo dependency tracking.
# Depends only on `rocq`/`coq_makefile` being on PATH (nix dev shell or opam switch).

all: Makefile.coq
	+@$(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject Makefile
	@if command -v rocq >/dev/null 2>&1; then \
		rocq makefile -f _CoqProject -o Makefile.coq; \
	else \
		coq_makefile -f _CoqProject -o Makefile.coq; \
	fi

clean:
	+@$(MAKE) -f Makefile.coq clean 2>/dev/null || true
	rm -f Makefile.coq Makefile.coq.conf .lia.cache
	find . -type f \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' \
		-o -name '*.glob' -o -name '*.aux' -o -name '*.d' -o -name '*.cache' \) -delete

.PHONY: all clean
