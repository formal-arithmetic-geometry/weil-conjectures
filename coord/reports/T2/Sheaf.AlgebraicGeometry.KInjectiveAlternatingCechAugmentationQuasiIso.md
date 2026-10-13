## What changed

Replaced the sorry in
`AlgebraicGeometry.kInjective_alternatingCech_augmentation_quasiIso` by a complete
Lean proof of the resolution-and-transport argument. The statement and its public
imports are unchanged. Added proof-only imports of the injective-term augmentation,
Čech homotopy theorem, and upstream injective-term resolution instance. The
K-injective quasi-isomorphism criterion is already available through existing imports.

The proof constructs the existing degreewise-injective K-injective resolution I
and its actual map j. Mathlib identifies j with the forward map of a homotopy
equivalence. Global sections preserves it by its additive functor API. Čech
totalization preserves it by applying the new, fully proved homotopy theorem to
both inverse homotopies. Naturality of the augmentation and
`quasiIso_iff_comp_right` then cancel the Čech total map of j.

Added `AlternatingCechTotalHomotopy.lean`. Its private generic helper constructs a
homotopy using `totalDesc`, with coefficient homotopy in the vertical direction
and sign `p.negOnePow`. The proof checks both shape vanishing and the homotopy
identity on each total inclusion. Horizontal terms cancel by the cochain-map
commutation identity and `Int.negOnePow_succ`; vertical signs cancel by
`Int.units_mul_self`. The remaining identity is the coefficient homotopy equation
mapped through an additive functor. The public theorem specializes this to the
actual alternating Čech module functor.

Added `InjectiveTermsAlternatingCechAugmentation.lean` for the remaining finite-column
argument on an unbounded complex with injective terms. It does not assume
K-injectivity and is strictly the injective-term case of the original argument,
not the original assertion renamed or with its hypothesis repackaged.

All three modules compile cleanly with lcompile.py --all. Searches used leanfinder,
loogle and source grep; LeanSearch was attempted and returned an unavailable
service error, recorded as such. Read the authoritative Stacks pages for Tags
08C1 and 01EP since the local literature directory has no cohomology.tex.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.kInjective_alternatingCech_augmentation_quasiIso`
(node `lem-sc-kinjective-alternating-cech-augmentation-quasi-iso`).

Fully proved the added public theorem:
`AlgebraicGeometry.alternatingCechTotal_map_homotopy`
(node `lem-sc-alternating-cech-total-homotopy`), including its private generic helper.

Added one remaining named hole:
`AlgebraicGeometry.injectiveTerms_alternatingCech_augmentation_quasiIso`
(node `lem-sc-injective-terms-alternating-cech-augmentation`). Its proof is exactly
`by sorry` and its docstring gives the augmented-row finite-column chase.

Thus this is a decomposition: one original hole closed, one smaller hole added,
net zero holes. The transport and total-homotopy portions are actual proved Lean.
No sorry remains in the assigned module or the homotopy module.

## No longer needed

No existing import was removed: the assigned module initially imported only
`Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex`, required by its signature.
The second reading removed the first worker’s redundant proof-only import
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`; the criterion remains
available through existing imports. No planned mathematical node was pruned. The original row dependencies
`lem-weil-pbc-module-injective-open-cover-cech-acyclic` and
`lem-pc-alternating-cech-computes` now belong to the smaller injective-term node,
not directly to the assigned module. They remain needed there.

Did not import `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`: its already
proved resolution construction is provided directly by the upstream resolution
API and the Grothendieck instance already exported by the existing statement
import. This is API specialization, not removal of the resolution argument.

## Where the brief, the DAG or earlier work was wrong

The original DAG had the correct mathematics, but its three numbered steps had
no ready Lean interfaces for the unbounded injective-term finite-column assertion
or the signed total homotopy construction. The latter interface is now supplied
with a full proof; the former is the only new sorry. The existing
`injective_cech_total_sections` theorem is nonnegative and abelian-group valued,
so applying it directly would lose the original unbounded module-valued scope.

No signatures, definitions or target statements were changed. No other group's
module was adapted. The unit record `sk-thm-picard-duality` has empty realized
statement/step lists; the original unit route is preserved.

Edge cases checked: the homotopy theorem requires no cover and works for r=0,
zero maps, zero complexes and negative coefficient degrees. The injective-term
statement includes r=0: the cover forces the scheme empty, and all section modules
are zero. It requires no affine intersections or quasi-coherence. Termwise
injectivity is used only for augmented-row exactness; the main theorem adds none
of these hypotheses to the original K-injective statement.

## New nodes

`lem-sc-alternating-cech-total-homotopy`: proved homotopy preservation for the
actual finite-family total functor. Its module is
`Sheaf.AlgebraicGeometry.AlternatingCechTotalHomotopy`. The generic private proof
also applies to any additive functor into integer cochain complexes with totals.

`lem-sc-injective-terms-alternating-cech-augmentation`: the remaining injective-term
finite-column lemma, in
`Sheaf.AlgebraicGeometry.InjectiveTermsAlternatingCechAugmentation`. Its source is
the first paragraph of the proof of Stacks Tag 08C1 using 01EP and alternating
comparison. Its node names the existing row acyclicity and comparison nodes.

Updated the assigned node's proof, proof_deps and proof_origin to match the Lean
resolution, homotopy and naturality argument. No change record is needed.

## Second reading by T2

1. Compared every delivered source with the repository using diff. The assigned
   module changes only its proof body and proof-only imports. Its signature and
   docstring are byte-for-byte unchanged. Both additional modules are new; no
   existing definitions, signatures or target statements change. The existing
   node changes only proof, proof_deps and proof_origin. Verdict: pass.
2. Independently compiled all three modules in import order with lcompile.py.
   All compile without warnings. Scanned all delivered Lean for forbidden
   declarations and sorry: only the reported injective-term theorem has a hole,
   exactly `by sorry`; no data definition or anonymous hole is added. Scratch-copy
   `#print axioms` checks show only propext, Classical.choice and Quot.sound for
   alternatingCechTotal_map_homotopy, and those plus sorryAx for the injective-term
   lemma and the assigned theorem. Read the signed generic homotopy proof and
   the resolution/naturality transport proof in full. The actual upstream
   functorial resolution constructs I and j; no arbitrary data are chosen from
   an unproved existence assertion. Verdict: pass as a decomposition, not an
   axiom-free completion of the assigned theorem.
3. Read the sole split-off statement and its complete row-exactness/finite-column
   proof. It isolates the injective-term case and removes K-injectivity; the
   main proof establishes the additional resolution and transport steps, rather
   than applying a renamed equivalent assertion. Checked r=0 (empty scheme),
   r=1 (the unique open is top, only the restriction column remains), zero
   complexes, repeated opens and unbounded negative coefficient degrees. Finite
   horizontal support, not a vertical bound, makes the row chase terminate.
   Checked Stacks Tags 08C1, 01EP and 01FM at their authoritative pages. New searches
   used leanfinder for bounded-horizontal exact double-complex totalization,
   loogle for HomologicalComplex₂ and Homotopy, and grep for bounded totals and
   alternating augmentations; also searched lean/Sheaf and lean/WeilConjectures.
   No exact existing injective-term assertion was found. Existing
   injective_cech_total_sections is nonnegative and abelian-group valued, and
   ordered one-row augmentation lemmas do not supply this actual alternating,
   unbounded total map. Closing this hole requires further comparison and total
   exactness formalization, not a short application. Verdict: pass.
4. The assigned proof follows the original top-down resolution, injective-row
   and homotopy-transport route. Each added proof import is used. Removed the
   redundant direct Mathlib.Algebra.Homology.DerivedCategory.KInjective import;
   recompilation confirms the criterion is already available. The generic
   homotopy calculation remains appropriate: Mathlib's
   mapBifunctorMapHomotopy₂ acts on a bifunctor and two coefficient complexes,
   not directly on this functor into complexes. Adapting that API would require
   another comparison construction; the existing proved helper is retained.
   The old proof_deps not directly used by the main proof are explicitly listed
   under No longer needed and remain dependencies of the smaller row lemma.
   Checked dag/units/sk-thm-picard-duality.json: realized is unchanged, with empty
   statement and step lists. Verdict: pass.
5. Checked all three nodes against their Lean signatures and proof steps,
   proof_deps against the union of uses, and proof_origin against the actual
   construction. Both new nodes have source, natural-language proof, searches,
   created, blueprint, chapter/unit and complete Lean records. The original
   node retains its statement and interface metadata. Verdict: pass.

Second-reading change: removed one redundant proof-only Mathlib import and
updated this report. No mathematical proof, signature, definition, node route,
unit record or hole count changed. Closed one original hole and added one
strictly smaller hole: net zero, with a fully proved new homotopy theorem.

Source checks: https://stacks.math.columbia.edu/tag/08C1,
https://stacks.math.columbia.edu/tag/01EP,
https://stacks.math.columbia.edu/tag/01FM.
