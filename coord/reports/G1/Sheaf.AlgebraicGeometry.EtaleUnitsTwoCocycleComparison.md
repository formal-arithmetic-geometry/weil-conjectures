## What changed

Removed the duplicate `EtaleUnitsH2ComparisonAux` theorem and its new node. Importing the existing theorem in `EtaleGaloisUnitsComparison` is impossible: that module imports this item, so the proposed import closes a cycle. Its proof is already a composition through this item's theorem. No existing dependency module is adapted.

Replaced the duplicate comparison obligation with two strictly weaker directional statements, one embedding homogeneous Galois H² into etale H² and one embedding etale H² into homogeneous Galois H². The item combines these by Mathlib's Schröder–Bernstein theorem and composes with the existing homogeneous/inhomogeneous equivalence. All original theorem binders, universes, visibility, and conclusion stay unchanged.

## Proved and sorry left

Closed the item's one hole: `AlgebraicGeometry.Scheme.nonempty_equiv_twoCocycleClasses_cohomologicalBrauerGroup`.

Added two named holes:

- `AlgebraicGeometry.Scheme.nonempty_embedding_galoisUnitsH2_cohomologicalBrauerGroup`, node `lem-sc-etale-units-h2-forward-embedding`.
- `AlgebraicGeometry.Scheme.nonempty_embedding_cohomologicalBrauerGroup_galoisUnitsH2`, node `lem-sc-etale-units-h2-reverse-embedding`.

This is a decomposition, not a completed mathematical proof. Each remaining statement requires only an injection in one direction; neither asserts a bijection, surjectivity, or an equivalence. The combination is a kernel-checked Lean proof.

## No longer needed

Removed the returned duplicate module `Sheaf.AlgebraicGeometry.EtaleUnitsH2ComparisonAux` and node `lem-sc-etale-units-h2-comparison-aux` entirely.

Removed direct proof imports `Sheaf.AlgebraicGeometry.AbelianSheavesGModules` (node `lem-exc-abelian-sheaves-gmodules`) and `Sheaf.FieldTheory.GaloisUnitsCohomology` (node `def-sc-galois-units-cohomology`) from the item. They remain mathematical prerequisites of the directional comparison statements; this is removal of redundant direct imports, not a claim that their theory is globally unnecessary. The homogeneous comparison module/node remains required. The old direct proof dependencies `def-br` and `def-sc-galois-units-two-cocycle-classes` are now statement dependencies only in the item; their modules remain public imports because the signature needs them. These and `def-sc-galois-units-cohomology` and `lem-exc-abelian-sheaves-gmodules` are every old proof dependency absent from the new item proof. No old prerequisite is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified the duplicate homogeneous-to-etale comparison statement. Direct reuse of that existing statement is circular, as `import_direction.py may` confirms. Adding a vacuous inhabitance binder would not repair the mathematical duplication and was discarded. Moving the hole into the existing comparison would require an unforced adaptation and was also discarded. Neither attempt is part of this delivery.

The repair instead states two proper directional parts of the comparison, preserving the stalk/derived-invariants argument and leaving all existing library interfaces unchanged. The item's proof and dependencies are updated in its node copy.

## New nodes

`lem-sc-etale-units-h2-forward-embedding` records only the forward injection, with its source and complete stalk/derived-invariants and injectivity argument. It is stated in `Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding`.

`lem-sc-etale-units-h2-reverse-embedding` records only the reverse injection, with its source and the reverse injectivity argument. It is stated in `Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding`.

Both statements apply to every field, including imperfect fields; neither needs a closure or characteristic hypothesis. Both source and target contain a zero cohomology class. They do not assert vanishing, finiteness, or equality of the two universes.

## Second reading by G1

1. Compared all delivered modules against the repository. The one existing theorem's
signature, universes, binders, namespace and visibility are byte-for-byte unchanged;
no definition or target changed, and there are no adaptations. Restored the original
author credit. The original documentation's claim that this comparison avoids the
homogeneous model no longer describes the route: the new proof passes through it.
This is a below-unit implementation choice; the mathematical assertion is unchanged.
The existing node statement retains that obsolete route sentence because stage 3 may
change its proof fields, not silently rewrite its statement.

2. Compiled all three modules in import order using lcompile.py: no errors or warnings.
The two directional theorems alone have whole-proof named sorries, both listed above
with their nodes. No new definitions, arbitrary witness constructions, forbidden
axioms, opaque declarations or unsafe code occur. Explicit #print axioms checks reported only propext, Classical.choice, Quot.sound
and sorryAx, and the delivery tool's full constant probe passed; sorryAx is expected
from the two obligations and the existing homogeneous-comparison import closure.
The main proof's orientations are correct: invert the homogeneous-to-inhomogeneous
equivalence, then compose with the Galois-to-etale equivalence supplied by
Function.Embedding.antisymm. No equality of universes is assumed.

3. Read both new statements and their complete word proofs, GaloisUnitsCohomology,
GaloisUnitsHomogeneousComparison, Gm, and abelianSheaves_equiv_discreteGModules.
Checked Stacks 03QU (derived global sections versus derived invariants), 03QV(2)
(the units coefficient), and 0DVG (continuous cochain comparison for profinite groups).
Each obligation is one direction of injectivity, strictly weaker than the equivalence,
and neither asserts surjectivity. The zero class exists on both sides; over a separably
closed field both degree-two groups vanish, over finite fields both vanish, and imperfect
fields use separable-closure units because etale germs contain only separable elements.
No algebraic-closedness or characteristic assumption is missing. Fresh leanfinder search
for injective etale/Galois comparisons found only unrelated injectivity lemmas; loogle
confirmed the exact cross-universe Embedding.antisymm lemma; grep and rg found the
existing EtaleGaloisUnitsComparison, but its imports lead back to this item. The
finite-ring ContinuousCochainsDerivedInvariants theorem cannot specialize to integer
coefficients. Thus neither new obligation is currently closable by an available
noncircular declaration in a few minutes. This is a decomposition with delivery-local net holes -1,
not a completed proof or positive hole-count progress.

4. Checked the shortest available noncircular route and import visibility. All proof-only
imports use plain import. Added the missing plain AbelianSheavesGModules import to each
new module to match its listed proof dependency. Signature imports remain public.
The No longer needed section now lists every old proof dependency absent from the new
item proof, distinguishing direct pruning from prerequisites retained below it.
Read dag/units/sk-thm-br.json: its route remains the Brauer injection into the function
field followed by Tsen, and this below-unit comparison changes neither step nor realized.

5. The existing node proof and proof_deps match the three invoked library declarations;
the Mathlib Schroeder-Bernstein step is recorded in words. Both new nodes have matching
Lean signatures, source, creation and search records, split status, and proof dependency
unions. Added missing mathlib_match:null and blueprint.same_as:[] fields. Repaired both
word proofs and node proofs: universality yields mutually inverse maps on cohomology,
not an unsupported assertion of chain-homotopy equivalences between arbitrary complexes.
Added the homogeneous/inhomogeneous change-of-variables argument required by GaloisUnitsH2.
No theorem signature or Lean proof body needed repair.

Sources checked: https://stacks.math.columbia.edu/tag/03QU,
https://stacks.math.columbia.edu/tag/03QV, https://stacks.math.columbia.edu/tag/0DVG.

Validation: deliver3.py --no-push printed OK; classified CODEX because this delivery
adds two statement modules and nodes and repairs a returned delivery.
