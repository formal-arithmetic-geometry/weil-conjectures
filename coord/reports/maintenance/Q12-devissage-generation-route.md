# Q12 generation-unit circular prerequisite repair

Maintenance, 2026-10-16 08:27 UTC; item lem-trf-devissage-generation, dispatcher key
lem-trf-devissage-generation@new. This is a unit-route correction, not a
review or landing of the worker's mathematical split.

The original generation unit inferred membership of its generators from
sk-thm-sf-ctf-stability. Its only stamped node and full realization carrier
is thm-sf-ctf-stability. The current DAG has the exact dependency path:

    thm-sf-ctf-stability -> cor-weil-finite-constructible-hom -> lem-weil-finite-duality-site-comparison -> lem-trf-devissage-generation

Requiring the generation lemma to cite that aggregate theorem therefore
closes a dependency cycle. The inference fails as an ordering of proof
prerequisites. The statement itself is not disputed. Removing realization,
inventing a carrier for all of stability, or suppressing the unit checker
would conceal the problem.

The maintainer confirms the established circularity and replaces only the
opening reference by the existing open/closed immersion construction and
etale/pro-etale comparison interfaces already used in the Q12 split.
The remaining flat-model, brutal-tail and dimension-induction route, the
unit statement, chapter, source ancestry and realization are preserved.
The uses list now cites the units containing those narrower interfaces.

Changed record: dag/units/sk-lem-sf-ctf-generation.json.
Changed local literature source: literature/blueprint/master/blueprint/sec-six-functors/sk-lem-sf-ctf-generation/_section.md.
Literature documents are ignored by repository policy. The exact source
patch is committed beside this note as Q12-devissage-generation-route.patch
so the local source correction is reproducible. Original source SHA256:
8834aec2040e2b26a81c6d39d9eb2d0805670fb1da2f8f5810fbf376ec21f1f7
Corrected source SHA256: 4e6d5ca428ed3c2b1410da8117bb87bd8939e59deaa92dcc5f2fe3d2d96b6cf2.
Every pre-existing changed file has a sibling .maint-Q12-devissage-generation-1792138933.bak backup.

Apply this correction to the authoritative live project first and then to
the side project, as coord/dag-sync.md requires. Their unit records must
agree outside the independently maintained realization bindings. The
corrected source also prevents units.py build from restoring the bad edge.

The next worker should keep the current proof and honest search/citation
records, rerun the normal deliver.py Q12 lem-trf-devissage-generation
--no-push command against the refreshed base, and hand a passing split to
the independent second reader. Do not add thm-sf-ctf-stability as a
dependency. The earlier ATTACH candidate describes the small etale site
and does not establish the whole pro-etale item or its negative
constant-coefficient clause. No Lean changes or compilation are required
by this metadata repair. Normal mathematical review is still required.
