## What changed

Proved `RingHom.Etale.isNormalRing` in `lean/Sheaf/RingTheory/EtaleNormalRing.lean` by taking the smoothness conjunct of Mathlib's `RingHom.etale_iff_formallyUnramified_and_smooth` and applying `RingHom.Smooth.isNormalRing` to the unchanged normality hypothesis. Removed the proof-only import `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`. Updated the item's node proof, proof_deps and proof_origin to this ring-theoretic route. All existing signatures, public imports and docstrings are unchanged; the original docstring describes the longer planned route.

The LeanFinder search returned the Mathlib equivalence; direct source inspection confirmed its independent universes and the exact normality conclusion of `RingHom.Smooth.isNormalRing`. The upstream convenience lemma `RingHom.Etale.smooth` restricts its two rings to one universe, so the Mathlib equivalence is preferable here. The item's unit `sk-thm-p1` realizes neither this tool lemma nor its discarded scheme-level dependencies: no unit statement or step is bypassed.

## Proved and sorry left

Proved the sole original sorry, `RingHom.Etale.isNormalRing` (node `lem-weil-pbc-etale-over-normal-ring-normal`), from existing named statements. No sorry remains in the delivered module and none is added. The existing downstream `RingHom.Smooth.isNormalRing` (node `lem-weil-pbc-smooth-over-normal-ring-normal`, module `Sheaf.RingTheory.SmoothNormalRing`) remains sorry in the library; the delivery uses it as intended by stage 3. This is a reduction to that existing stronger theorem, not a claim that all transitive axioms are closed.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`.

The proof does not need nodes `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`, `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`, `def-sbc-smooth-morphisms`, or `def-weil-etale-morphism` as proof dependencies. The last remains an unchanged statement dependency in the node. The discarded modules are `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`, `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, and `Mathlib.AlgebraicGeometry.Morphisms.Etale`. They are unnecessary for this proof; other library users may still need them. Their downstream proof branches are not reached through this removed import.

Retained all three public Mathlib imports needed to express the statement, and the proof-only `Sheaf.RingTheory.SmoothNormalRing` import.

## Where the brief, the DAG or earlier work was wrong

The DAG's three-step detour through affine scheme smoothness is unnecessary for the landed ring-theoretic signature. Mathlib already proves etale implies smooth for ring maps. No false statement, signature change, new definition, or tool workaround was needed. The zero target ring has no prime ideals, so the conclusion remains vacuous as originally stated; independent universes and non-Noetherian rings remain covered.

## Second reading by G2

1. PASS: diffed the sole delivered module against the repository. The existing theorem signature, universes, hypotheses, conclusion, public imports, and definitions are byte-for-byte unchanged. The only Lean changes are the proof and removal of one proof-only import. No change record is needed.
2. PASS: compiled the module with lcompile.py without errors or warnings. There is no sorry or forbidden declaration mechanism in the delivered module. In a scratch copy, #print axioms reports propext, Classical.choice, Quot.sound and sorryAx for RingHom.Etale.isNormalRing. The same probe of RingHom.Smooth.isNormalRing confirms that the pre-existing open smooth-normality theorem supplies sorryAx; the Mathlib etale/smooth equivalence uses only the three permitted axioms. This delivery closes the local proof by reduction, not its transitive open dependency.
3. PASS: no split-off statement, new declaration, new module or new node. Read the stronger existing Smooth.isNormalRing statement and its sourced natural-language proof. Its conclusion matches exactly, and taking smoothness from etaleness adds no assumption. Zero target rings are covered vacuously, and the argument preserves arbitrary commutative rings in independent universes.
4. PASS: independently inspected Mathlib.RingTheory.RingHom.Etale and searched Mathlib smooth/etale files and the library's ring-theory files for normality ascent. The upstream Etale.smooth convenience lemma has a shared-universe restriction; the direct Mathlib equivalence avoids it and additional imports. All remaining public imports concern names in the statement; SmoothNormalRing is a plain proof-only import. Every old proof dependency omitted by the new proof appears under No longer needed. Inspected sk-thm-p1.realized: neither the item nor the discarded dependency nodes realize a unit statement or step, so the unit route is retained.
5. PASS: diffed the node JSON. Only proof, proof_deps and proof_origin changed. The two proof steps describe exactly the Lean reduction, their uses union equals proof_deps, and the existing statement and Lean declaration record remain unchanged.

Changes by the second reader: appended this review and recorded independent compile, axiom, search, pruning and unit-route checks. No repair to the Lean proof or node was necessary. The unchanged theorem docstring records the historical longer proof plan; the current two-step proof is documented in the node and this report.
