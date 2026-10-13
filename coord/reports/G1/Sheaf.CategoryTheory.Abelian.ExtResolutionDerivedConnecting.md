## What changed

Replaced the hole in CategoryTheory.InjectiveResolution.extMk_resolution_connecting_eq_triangle
with a complete Lean proof from two general split-sequence lemmas. The signature and public
imports are unchanged. The proof constructs the integer-indexed row and its degreewise splittings,
uses cone-boundary naturality, transports the given representatives, and combines the cocycle
formula with extMk_hom by shifted composition. Updated the item's proof, dependencies and origin.
All work is in the sandbox; no delivery is pushed.

## Proved and sorry left

Closed the original hole in
CategoryTheory.InjectiveResolution.extMk_resolution_connecting_eq_triangle
(node lem-sc-p1-ext-resolution-derived-connecting). No sorry remains in the item.
Added two holes, each in a separate new module:
- DerivedCategory.triangleOfSESδ_eq_degreewiseSplit
  (lem-sc-p1-split-ses-boundary-comparison).
- CochainComplex.degreewiseSplit_cocycle_boundary
  (lem-sc-p1-split-ses-cocycle-boundary).
This is a decomposition: one upper hole closed, two strictly separate lower holes added,
not a fully axiom-free proof. The declaration-hole net of this delivery is -1
(one closed, two added); no positive ledger progress is claimed. Both new declarations have complete component arguments in their
docstrings and nodes. All three module statements and the combining proof compile locally.
The zero row, arbitrary integer degree, degree zero of the original theorem, arbitrary
splittings, and arbitrary cocycle lifts are included; no projectivity of M is assumed.

## No longer needed

Removed the proof imports:
- Sheaf.CategoryTheory.Abelian.RHomDerivedConnecting
  (lem-sc-p1-rhom-hom-derived-connecting).
- Sheaf.CategoryTheory.Abelian.RightDerivedTriangleConnecting
  (lem-sc-p1-right-derived-triangle-connecting).
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
  (lem-sp-derived-functor-single-identification).
These modules/nodes are no longer needed by this item's proof. Their other users may still need
them; this report does not claim that they leave the entire target closure. The Ext-resolution
roof comparison, SES triangle, and long-exact-of-triangle Mathlib interfaces remain needed.
The unit record sk-thm-picard-duality has empty realized statement/step lists; no fixed unit
realization is bypassed by this below-unit change.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The original two-step route is mathematically plausible but its
right-derived and RHom interfaces require substantial additional comparison glue. The direct
cone/split calculation removes that route. The existing degreewise-split-derived-triangle leaf
proves distinguishedness, not equality with the canonical cone boundary; the new boundary lemma
records that missing equality, rather than assuming it from distinguishedness alone.
Stacks sources were read online at Tags 0152, 06XR and 011J because the referenced local
literature/stacks-project/derived.tex is absent on this machine. LeanSearch returned HTTP 500;
that is recorded as unavailable, not as a negative search. LeanFinder, Loogle and source grep
were run. The whole blueprint search for split connecting found no matching imported node.

## New nodes

lem-sc-p1-split-ses-boundary-comparison: identifies the cone boundary with the degreewise split
cochain map for any split short exact row, with no M, Ext group or resolution augmentation.
Its module is Sheaf.CategoryTheory.Abelian.SplitSESBoundaryComparison.

lem-sc-p1-split-ses-cocycle-boundary: computes shifted composition on a cocycle with an arbitrary
lift in any split row of complexes, with no original SES of objects, injectivity assumption,
resolution augmentation or canonical single-object triangle.
Its module is Sheaf.CategoryTheory.Abelian.SplitSESCocycleBoundary.

No change records or forced adaptations are needed.

## Second reading by G1

1. PASS. Diffed the delivered item against the repository. Extracted the entire theorem
signature through `:= by` and compared its bytes: identical. Public imports and visibility
are unchanged. There are no definitions or forced adaptations; the only new declarations
are the two reported theorem statements. Only proof, proof_deps and proof_origin changed
in the existing node.

2. PASS as a decomposition. Compiled all three modules in import order with lcompile.py:
no errors or warnings. Compiled scratch copies with #print axioms for all three declarations:
only propext, Classical.choice, Quot.sound and sorryAx. The two named new theorems are the
only sorry sites; the item has none. No forbidden declaration mechanism or hollow data.
The degreewise splittings come from proved Mathlib splittingOfInjective, not either hole.

3. PASS. Read both statements and their complete component proofs. The cone comparison
uses H^k=proj_B r^k and the shifted differential -d_A; the resulting difference is exactly
q followed by the split boundary minus the cone third map -proj_A. For the cocycle formula,
b=t i+c s gives c s d_B r=a-t d_A. Mathlib rightShift and shiftFunctorAdd components carry
no scalar sign, so this proves the claimed unsigned formula in every integer degree.
Checked zero rows, chain-map splittings (boundary zero, a a coboundary), arbitrary lifts
and n=0; no projectivity of M is needed. Each statement isolates a distinct part of the
argument and neither reproduces the original Ext-resolution theorem. Read Stacks
https://stacks.math.columbia.edu/tag/0152, /tag/011J and /tag/06XR. Independently searched
with LeanFinder (cone homotopy), Loogle (equivHomShift) and grep (the fromSingleMk boundary
criterion), and searched Sheaf/WeilConjectures and DAG records for split boundary formulas.
Found the constructors and quotient criterion, but no duplicate of either new theorem.
No split statement had an immediate existing lemma that closes it.

4. PASS. Read the proof from its target downward: cone naturality, two independent split
calculations, then the extMk roof formula. All imports provide symbols in signatures or
proofs; new statement imports are public and the item's two new proof imports are plain.
The three old proof_deps absent from the new proof are exactly the three listed under
No longer needed. The unit sk-thm-picard-duality has empty realized statement/step lists;
its fixed route is untouched. This is one-hole-to-two-hole decomposition, not an axiom-free
proof or a claim that the three pruned modules leave the full target closure.

5. PASS. Checked each new node's statement against its Lean signature, source, complete
proof steps, dependency union, origin, searches, creation, blueprint provenance, chapter,
unit and Lean record. Existing node proof_deps are the union of uses in the new steps and
match the actual splitting, naturality, roof and shifted-composition argument.

Changes by the second reader: made the cone homotopy's degrees and sign equation explicit
in its docstring and node; added independent Loogle search evidence to both new nodes;
made the negative hole net explicit in Proved and sorry left. No Lean statement or proof
body changed.
