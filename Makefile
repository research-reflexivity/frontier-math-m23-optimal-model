GP ?= gp
PYTHON ?= python3
SAGE ?= sage
MAGMA ?= magma
SINGULAR ?= Singular

.PHONY: verify verify-boundary verify-specialization verify-progression verify-progression-85 verify-ramification verify-model verify-model-singular verify-model-sage verify-model-magma verify-geometry verify-python-arithmetic verify-data verify-all

verify: verify-boundary verify-specialization verify-progression verify-progression-85 verify-ramification

verify-boundary:
	cd verification && $(GP) -q -f verify_boundary_valuations.gp

verify-specialization:
	cd verification && $(GP) -q -f verify_specialization_t2.gp

verify-progression:
	cd verification && $(GP) -q -f verify_progression_319.gp

verify-progression-85:
	cd verification && $(GP) -q -f verify_progression_85.gp

verify-ramification:
	cd verification && $(GP) -q -s 4000000000 -f verify_ramified_t3830.gp

verify-model: verify-model-singular verify-model-sage verify-model-magma

verify-model-singular:
	cd verification && SINGULAR="$(SINGULAR)" $(PYTHON) verify_optimal_23_4.py

verify-model-sage:
	$(SAGE) verification/verify_sage.py

verify-model-magma:
	$(PYTHON) scripts/emit_magma_certificate.py --check
	$(MAGMA) -b verification/verify_optimal_23_4.m

verify-geometry:
	cd verification && $(SINGULAR) --cpus=1 --threads=1 -q verify_nodes_mod31.sing
	$(PYTHON) verification/verify_adjoint_mod31.py

verify-python-arithmetic:
	$(PYTHON) verification/verify_specialization_t2.py
	$(PYTHON) verification/verify_progression_319.py
	$(PYTHON) verification/verify_ramified_t3830.py

verify-data:
	shasum -a 256 -c CHECKSUMS.sha256

verify-all: verify verify-model verify-geometry verify-python-arithmetic verify-data
