# Q35 descended versal base: shared definition ownership repair

The independent H2 return for immutable delivery 33a28145b624 requires extracting
S1, literal test subalgebras, the total object, S_x and minimality from
ArtinMinimalDescentTransport into a definition node/module. The worker completed
this refactor, but its normal stage-2 delivery cannot carry the old theorem
module: that theorem is outside the item's prerequisite closure after H2 removes
the spurious statement dependency. deliver2.py also drops dependency-node
stmt_deps changes. This caused repeated identical compile-success/preflight-fail
attempts; the dispatcher counted 81 on entry to maintenance.

Maintenance installs the shared extraction on the base, under the merge lock.
All eight moved declaration bodies are byte-for-byte equal to the previous
module, with only blueprint owner tags changed. Everything from descentImageRing
through the original theorem and proof is byte-for-byte unchanged. The old module
publicly imports the new module, preserving existing consumers' declaration names
and signatures; its node gains the new definition prerequisite and its Lean
record no longer claims ownership of the moved declarations. Original stage-1
and stage-2 review records remain as provenance for the unchanged mathematics;
this note records the subsequent maintenance extraction.

The retained item theorem is byte-for-byte equal to the returned theorem. Its
advisory FormalBaseMorphism extraction is also byte-for-byte equal to the returned
body. Maintenance installs that definition owner as well and adds both definition
prerequisites to the unstated item record so they are reached immediately. The
item keeps its current statement, proof, proof_deps, reviews and null Lean record.
No theorem proof, mathematical signature, dispatcher state, review service or
landing/preflight tool is changed. The original independent H2 return remains
pending for the item's normal review.

Before commit, the three shared Lean files and the retained worker item module are
compiled one at a time with tools/lean_file.sh (60 seconds per file). The next
worker packet omits the already installed shared files and cites the new landed
definition. A normal deliver2.py --no-push verifies that packet with only the item node,
item module and worker report. Adjacent
*.maint-Q35-ownership-1792878687.bak retain every replaced/removed file. New files
have an identical adjacent .bak copy after validation.

Validation receipt: individual compiles passed in 2.2 s (Schlessinger definitions),
2.3 s (formal-base morphism), 3.3 s (minimal descent theorem module), and 1.9 s
(retained item verification copy). Incremental DAG validation and existing import
checks passed. Ordinary item-only deliver2.py --no-push passed at 9a140af884a.
Interface landing record: `20261024T221155-L-1140015-296`; normal global verification remains
with the build service. The two new definition nodes now record this maintenance
ownership/provenance review, without marking the item theorem reviewed.
