## What changed

Replaced the sole sorry in
`lean/Sheaf/AlgebraicGeometry/LocallyOfFiniteTypeOfIsLocallyQuasiFinite.lean`
with a complete proof of
`AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_of_isLocallyQuasiFinite`.
The signature, docstring, public import, and all definitions are unchanged.

The proof specializes Mathlib's `HasRingHomProperty.iff_exists_appLE` to
`LocallyOfFiniteType` and `RingHom.FiniteType`, using finite type's stability
under composition and localization away. For each source point it unpacks
`hf x`, discards the quasi-finiteness-at-the-prime witness, and supplies the
same affine opens and finite-type witness to the criterion. Source and target
opens are exchanged in the existential tuple to match Mathlib's binder order.
The ring-map finite-type predicate uses the same `toAlgebra` as the hypothesis.

This follows both steps of `lem-weil-pbc-lqf-locally-finite-type` unchanged,
including its Mathlib leaf `lem-weil-pbc-lft-pointwise-criterion`; no node update
is needed. No realized step of the unit `sk-thm-p1` is bypassed.

Searches: LeanFinder for the pointwise affine-neighborhood criterion; Loogle
for `AlgebraicGeometry.HasRingHomProperty.iff_exists_appLE`; ripgrep in both
library roots and direct reading of Mathlib's `RingHomProperties.lean` and
`RingHom/FiniteType.lean`. The pinned Mathlib criterion closes the statement
without any new intermediate lemmas. The local single-file compile passed
without errors or warnings.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_of_isLocallyQuasiFinite`
(blueprint: `lem-weil-pbc-lqf-locally-finite-type`). One of one original sorries
is closed. No sorry remains in the module; no new declaration or sorry is added.
The proof uses only definitions and proved Mathlib lemmas.

## No longer needed

None. The sole import, `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`, is required
by the statement and supplies the definitions unpacked in the proof. All four
original proof dependencies remain used: `pqf-def-quasifinite`,
`def-weil-pbc-finite-type-algebra`, `lem-weil-pbc-lft-pointwise-criterion`, and
`def-weil-finite-type-morphism`. No node or module is pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement mismatch was found. The planned pointwise
criterion fits the existing definition directly. The source path
`literature/stacks-project/morphisms.tex` recorded in the DAG is not present
in this local checkout; the existing source-based docstring and DAG plan were
preserved, and the exact criterion and algebra witnesses were checked in the
pinned Mathlib sources and by Lean compilation.

## Second reading by E3

1. Compared the entire delivered module with the repository using `diff -u`.
   The only change is the replacement of the theorem's `sorry` by six proof lines.
   The existing signature, universe, docstrings, public import, and namespace are
   byte-for-byte unchanged. There are no definitions, new modules, node changes,
   or change records in the delivery. Verdict: pass.
2. Compiled the delivered file with `lcompile.py`: exit 0, no errors or warnings.
   Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_of_isLocallyQuasiFinite`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`. The delivered module
   has no remaining sorry or forbidden declaration. Verdict: pass.
3. No statements were split off and no new declarations were introduced.
   Read `IsLocallyQuasiFinite` and `IsQuasiFiniteAtPoint` in
   `QuasiFiniteMorphism.lean`: `hf x` supplies precisely the affine source open
   containing x, affine target open, inclusion, and finite-type algebra witness
   consumed by the proof. The quasi-finiteness-at-the-prime witness is discarded.
   Empty source schemes are covered by the universal pointwise criterion; there
   is no nonemptiness, quasi-compactness, or extra finiteness hypothesis.
   Verdict: pass.
4. Read Mathlib `RingHomProperties.lean:651` (`iff_exists_appLE`),
   `Morphisms/FiniteType.lean:54` (its finite-type instance), and
   `RingTheory/RingHom/FiniteType.lean:41,75` (the stability witnesses).
   The source/target affine opens are correctly reversed in the final tuple,
   and `hft` uses the same `appLE` ring homomorphism's `toAlgebra` as the criterion.
   Searched both project Lean roots for the predicate and theorem name, and ran
   a fresh launcher grep search for `IsQuasiFiniteAtPoint` and the theorem name
   against upstream: no upstream match. The existing Mathlib criterion is already
   the direct route; no helper is needed. The sole public import is required by
   the statement. Read `dag/units/sk-thm-p1.json` and its `realized` statement and
   steps: this elementary descendant proof bypasses none of those nodes.
   `## No longer needed` correctly lists none: all four old dependencies remain
   used as definitions or the pointwise Mathlib criterion. Verdict: pass.
5. Read `lem-weil-pbc-lqf-locally-finite-type.json` and its criterion leaf
   `lem-weil-pbc-lft-pointwise-criterion.json`. Step 1 unpacks the quasi-finite
   definition and retains finite type; step 2 applies the recorded Mathlib
   pointwise criterion. These are exactly the Lean proof's operations.
   `proof`, all four `proof_deps`, and the source-based `proof_origin` remain
   accurate. No new nodes require checking or adding. Verdict: pass.

Second reading changed only this report by adding the independent review.
The Lean proof was retained unchanged. Holes closed: the sole original hole in
`AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_of_isLocallyQuasiFinite`.
Holes added: none. This is one proof, not a decomposition.
