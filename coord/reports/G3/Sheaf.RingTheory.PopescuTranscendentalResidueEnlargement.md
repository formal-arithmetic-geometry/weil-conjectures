## What changed

Proved `Algebra.exists_popescu_transcendental_residue_enlargement` with its original
signature and docstring unchanged. The construction is evaluation of `A₀[T]` at `x`,
localized at the inverse image of the ambient maximal ideal, followed by its actual
algebra range. No arbitrary witness of an unproved existence statement is chosen.

Added the fully implemented construction module
`Sheaf.RingTheory.PopescuLocalizedPolynomialImage` and the fully proved structure
module `Sheaf.RingTheory.PopescuTranscendentalImageStructure`. The construction module
proves locality, containment of `A₀` and `x`, and essential finite type. The structure
module proves Artinianity, flatness of inclusion, and the maximal-ideal extension identity.
Its proof uses the existing proved
`Module.flat_and_flat_of_flat_fibre_noetherian`, then faithful flatness and the bijection
with the image.

The item's private residue-generation proof uses polynomial induction and fraction
representatives from localization. The residue algebra is the canonical quotient map
induced by inclusion. Checking its composite on residue representatives proves the
compatibility with the specified ambient residue algebra; transcendence descends along
that composite. Updated the original node's proof, proof dependencies, and origin to
match these arguments. The unit `sk-thm-p1` and its realized statements and steps are
unchanged.

The item's new imports are proof-only:
`Sheaf.RingTheory.PopescuTranscendentalImageStructure`,
`Mathlib.RingTheory.HopkinsLevitzki`, `Mathlib.RingTheory.KrullDimension.Zero`, and
`Mathlib.RingTheory.Algebraic.Basic`. Its original public import interface is retained. No existing definition, statement, or visibility changes, and no forced
adaptations.

## Proved and sorry left

Closed the one original hole:
`Algebra.exists_popescu_transcendental_residue_enlargement`
(node `lem-weil-pbc-popescu-transcendental-residue-enlargement`).

Added zero holes. There are no `sorry`s in any of the three delivered Lean modules.
The new theorem `Algebra.popescu_transcendental_image_structure` and every construction
lemma are proved. This is one hole closed, zero holes added, rather than a decomposition.
The only non-Mathlib theorem applied for flatness is the existing, already proved
Noetherian fibre criterion. The final delivery tool checks the axioms of all declarations.

All three modules compiled in dependency order with the required `lcompile.py`.
Edge cases: if `A₀` is a field, the localization is its rational function field; the
maximal-ideal calculations specialize to zero. If `A₀ = B`, the transcendence assumption
is impossible. The construction itself is defined even without transcendence; the
transcendence assumption is used only to identify the prime and prove the structure.
No positive-characteristic argument is needed in this branch, but the existing `p`,
`hp`, and `hx` binders are preserved exactly.

## No longer needed

Second reading removed two redundant imports from the new modules:
`Mathlib.RingTheory.LocalRing.RingHom.Basic` from the construction, and
`Mathlib.RingTheory.LocalRing.ResidueField.Ideal` from the structure module (replaced
publicly by the required residue-field definitions in `.Basic`).

No original import was removed: the original public import interface is retained.
The following planned dependencies are omitted from the revised argument:

- `lem-weil-pbc-artinian-local-essentially-finite-type-residue`, module
  `Sheaf.RingTheory.ArtinianLocalEssentiallyFiniteTypeResidue`: essential finite type
  follows directly through polynomial extension, localization, and image. Neither this
  theorem nor its module is imported.
- `lem-weil-pbc-artinian-local-unique-prime`: no separate classification of prime ideals
  is needed. Mathlib's Artinian nilpotence facts suffice.
- `lem-weil-pbc-noetherian-local-quotient-artinian-local`: the localization is proved
  Artinian directly by `isArtinianRing_iff_isNilpotent_maximalIdeal`, rather than by
  expressing it as a quotient by zero. Its planned Mathlib module
  `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` is not directly imported for this proof.
- `lem-weil-pbc-faithfully-flat-ideal-contraction`: injectivity is obtained from
  `Module.FaithfullyFlat.faithfulSMul` and `FaithfulSMul.algebraMap_injective`, without
  an ideal-contraction calculation.

These are local pruning decisions for this item's route; other callers may still need
these nodes. The existing `ArtinianTranscendentalLocalization` family was also inspected.
It packages a universe-lifted, essentially smooth extension and canonical residue
structures. This proof uses the explicit unlifted image and the specified residue
algebra directly, retaining the same polynomial-localization argument without importing
that additional essentially smooth interface.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement dispute was found. The DAG's Artinian residue-field
criterion is unnecessary for essential finite type here: the polynomial localization
already inherits it from `A₀`, and its image inherits it by surjectivity. The separate
unique-prime, quotient-Artinian, and ideal-contraction routes are similarly avoidable
using Mathlib's direct statements.

The initial file has no proof-dependency imports, despite the standing brief describing
such imports as already present. The actual declarations were read and the one needed
project theorem was imported in the structure module. LeanSearch returned an internal
server error; the actual failed query and the successful LeanFinder, Loogle, and grep
searches are recorded in `searches.jsonl`. The local Stacks source file is absent on this
machine, so the cited primary-source tags were read online.

## New nodes

`def-weil-pbc-popescu-localized-polynomial-image` records the explicit construction in
`Sheaf.RingTheory.PopescuLocalizedPolynomialImage`, including its proved containment,
locality, and essential finite type properties. Evaluation, the prime, localization
extension, and range are real definitions built from Mathlib, with no postponed data.

`lem-weil-pbc-popescu-transcendental-image-structure` records the fully proved theorem
in `Sheaf.RingTheory.PopescuTranscendentalImageStructure`: its image is Artinian, flatly
included, and has the required maximal-ideal extension. Its proof records the existing
Noetherian fibre criterion and the exact lower facts used. Neither new node leaves a
hole. There is no change record because no existing interface changes.


## Second reading by G3

1. Interface preservation: PASS. Compared the sole existing delivered module with the
   repository using `diff`, and checked the full existing theorem signature byte for byte.
   Its hypotheses, conclusion, docstring, visibility, and all existing definitions remain
   unchanged. The other two modules are new; there are no forced adaptations or interface
   change records. The existing node differs only in `proof`, `proof_deps`, and `proof_origin`.
2. Proof and data: PASS. Independently compiled all three modules with `lcompile.py` in
   import order. No `sorry`, forbidden declaration, or postponed construction occurs in
   delivered Lean. A scratch axiom check of the original theorem, structure theorem,
   image definition, and essential-finite-type theorem shows exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Evaluation, its unique localization extension,
   and the actual range construct the object. The delivery's probe checks all declarations.
3. Split statements: PASS. Zero holes are split off. Read the new construction and proved
   structure statements and their proofs. The structure theorem is strictly a part of the
   original conclusion, and is fully proved. Checked the field base case, zero maximal
   ideal, and impossible case A₀ = B. The closed fibre is a module over the field D/m₀D;
   the fibre criterion is applied with M = B, finite and nonzero over B. The given residue
   algebra is compared with the canonical inclusion map before descending transcendence.
   Independent LeanFinder, Loogle, and grep searches used different queries, recorded in
   `searches.jsonl`; searched project Lean and read the existing universe-lifted
   `ArtinianTranscendentalLocalization` and evaluation theorem. Neither gives this explicit
   image statement or the required residue generation directly. Mathlib's polynomial
   prime-residue rational-function equivalence would require additional equivalence and
   scalar-compatibility transport; the direct polynomial/fraction proof is shorter here.
4. Route and pruning: PASS after import cleanup. Read the proofs downward from the
   original theorem, the existing Noetherian fibre criterion, and Stacks Tags 07FI, 07FH,
   and 00MP. The proof follows polynomial evaluation/localization; essential finite type
   follows directly by composition and surjection. The four genuinely bypassed planned
   dependencies are listed above. Other old dependencies remain used through the two new
   modules, including localization, Noetherianity, faithful flatness, and finite type.
   The unit `sk-thm-p1` and its `realized` fields are unchanged; no unit step is bypassed.
5. DAG agreement: PASS. Checked the three nodes against the actual construction,
   structure proof, and residue-generation proof. New nodes have sources, complete proof
   steps, searches, creation/blueprint records, and Lean records. Their `proof_deps` are
   exactly the unions of their steps' `uses`. The existing node's statement is unchanged.

Second-reading changes: removed the redundant public import
`Mathlib.RingTheory.LocalRing.RingHom.Basic` from the construction module. Replaced the
structure module's public `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` import with
`Mathlib.RingTheory.LocalRing.ResidueField.Basic`: only the residue-field definitions are
needed publicly, and the ideal import proved redundant even as a proof import. Both
cleanups compile. No mathematical proof or statement required repair; no holes added.
