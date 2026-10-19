1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-mittag-leffler-faithfully-flat-descent.json`: statement, split proof, and blueprint metadata; no Mathlib match for the target.
- `dag/nodes/sec-trace-formula/lem-trf-module-finitely-presented-directed-colimit.json`: statement-only supporting node; Mathlib searches found no exact match.
- `dag/nodes/sec-trace-formula/lem-trf-mittag-leffler-eventual-domination.json`: statement-only supporting node; Mathlib searches found no exact match.
- `dag/nodes/sec-trace-formula/lem-trf-domination-pushout-universal-injective.json`: statement-only supporting node; Mathlib searches found no exact match.
- `dag/nodes/sec-trace-formula/lem-trf-faithfully-flat-universal-injective-reflection.json`: statement-only supporting node; Mathlib searches found no exact match.
- `citations.json`: verbatim statement quotes for every cited node at every proof step.

2. Attachments: none.

3. WANTED: none.

4. The imported item had an empty proof. I checked the source statement in `literature/stacks-project/algebra.tex`, Tag 05A5, against the node and retained its hypotheses, including the absence of flatness, countability, and finite-presentation assumptions on `M`. I searched the whole DAG and blueprint for each supporting fact and found no exact existing node. The four new nodes state strictly smaller generic facts used by the source proof; they do not restate the target.

## Not duplicates

- `lem-trf-module-finitely-presented-directed-colimit` vs existing `lem-trf-ml-countable-colimit`: the new node presents an arbitrary module as a filtered colimit of finitely presented modules, while the existing node assumes Mittag-Leffler and countable generation and extracts a countable cofinal subsystem.
- `lem-trf-mittag-leffler-eventual-domination` vs existing `lem-trf-mittag-leffler-hom-systems`: the new node gives the equivalent eventual domination criterion for a colimit presentation; the existing node only states eventual stabilization of Hom-image systems.
- `lem-trf-domination-pushout-universal-injective` vs existing `lem-trf-universal-injective-finite-test`: the new node relates domination of two maps to universal injectivity of a pushout leg; the existing node only reduces universal injectivity tests to finitely presented tensor factors.
- `lem-trf-faithfully-flat-universal-injective-reflection` vs existing `lem-weil-pbc-faithfully-flat-universally-injective`: the new node reflects universal injectivity of an arbitrary module map from its faithfully flat scalar extension; the existing node only states injectivity of the canonical map `N -> N tensor_R S`.

5. What I checked in detail:

## Review by NZ

I read the full Tag 05A5 statement and proof, including its pushout square, the tensorized pushout, and its final faithful-flat reflection argument. Step 1 uses the new colimit node exactly for the source’s presentation of `M`; its statement introduces the directed index, finitely presented stages, transition maps, and colimit maps. Step 2 uses the tensor-product definition, the target’s Mittag-Leffler definition, and the new Tag 059E characterization; finite presentation after scalar extension and commutation of tensor with this directed colimit are the direct finite-presentation/tensor identities described in the step. Step 3 verifies that the pushout remains a pushout after tensoring, with the category-colimit and tensor definitions cited. Step 4 uses the new Tag 0AUM pushout criterion, whose statement explicitly says that domination is equivalent to universal injectivity of the pushout leg. Step 5 applies the new faithful-flat reflection node with exactly the target map `R -> S` and the pushout map `M_j -> N`; its hypotheses match the item’s faithful-flat assumption. Step 6 applies the same pushout criterion in reverse and then the new Tag 059E criterion to conclude that `M` is Mittag-Leffler. I read every cited node statement and recorded each verbatim quote in `citations.json`; all hypotheses are present where used. I tested edge cases conceptually: the zero module has the empty finitely presented stage, identity maps are universally injective, and the argument does not use finite generation or flatness of `M`. No Lean source declaration with the target blueprint tag exists, and no SGA source is cited.

- `lem-trf-faithfully-flat-universal-injective-reflection` vs `lem-trf-mittag-leffler-faithfully-flat-descent`: the new node is the general faithful-flat reflection lemma for an arbitrary module map; the existing item is the specific Mittag-Leffler descent theorem whose proof invokes this reflection.
- `lem-trf-faithfully-flat-universal-injective-reflection` vs `lem-weil-pbc-faithfully-flat-descent-noetherian`: the new node reflects universal injectivity of arbitrary module maps; the existing node descends the Noetherian property of rings.
- `lem-trf-faithfully-flat-universal-injective-reflection` vs `lem-weil-pbc-faithfully-flat-ideal-contraction`: the new node reflects universal tensor-injectivity of a map after scalar extension; the existing node only identifies contractions of extended ideals (and the special injectivity of the ring map).
- `lem-trf-module-finitely-presented-directed-colimit` vs `lem-kun-lazard-flat-module`: the new node presents every module as a directed colimit of finitely presented modules; the existing Lazard node presents only modules whose tensor functor preserves short exact sequences as colimits of finite free modules.
- `lem-trf-faithfully-flat-universal-injective-reflection` vs `lem-weil-pbc-gabber-upstairs-tensor-coefficients`: the new node concerns universal injectivity of arbitrary module maps under faithful-flat scalar extension; the existing node constructs a faithfully flat algebra and a tensor relation for a finite algebra splitting problem.
- `lem-trf-faithfully-flat-universal-injective-reflection` vs `lem-weil-pbc-zariski-pair-finite-gabber-polynomial-upstairs-relation`: the new node is a map-level tensor-injectivity reflection statement; the existing node is a special tensor relation after quotienting a finite algebra by a coefficient submodule.
- `lem-trf-faithfully-flat-universal-injective-reflection` vs `lem-weil-pbc-zariski-pair-finite-gabber-polynomial`: the new node concerns arbitrary module maps and all tensor factors; the existing node asserts existence of a monic polynomial annihilating one element of a finite algebra.
