## What changed

Completed `SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization`
in `lean/Sheaf/Algebra/Homology/SuccessiveDerivedQuotientNormalization.lean` without changing
any public declaration signature, definition, or public import.

The proof chooses the existing ordinary and universal derived presentations, constructs
both comparison isomorphisms by uniqueness of normalized left adjoints, proves both
sectionwise tensor formulas, and verifies the representative/counit and unit equations.
Identity-topos K-flat pullback supplies the intermediate computation. Exact restriction
composition and Mathlib's coherence of left adjoints give associativity. Formal pasting,
including the prescribed equality transports, gives coefficient naturality.

Added proof imports of `Sheaf.Algebra.Homology.SheafRingDerivedHomComparison`,
`Mathlib.CategoryTheory.Adjunction.CompositionIso`, and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
All new helpers are private and proved. The proof instances are local, and elaboration
options and the extra namespace opening are scoped to individual declarations. Updated the existing node's proof, proof
dependencies, proof origin, and removed obsolete tool-use approvals.

## Proved and sorry left

Closed 1 hole:
`SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization`
(node `lem-sfb-successive-derived-quotient-normalization`).

Holes added: 0. Holes left in the item: 0. Split-off theorems: 0.
No other Lean module is changed. This is a proof, not a decomposition.

Validation: the complete module compiles through `lcompile.py` in 29.3 seconds.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The public declaration block, theorem signature, and public-import list were compared
against the repository and are unchanged. Both new project proof imports pass
`tools/import_direction.py may`. The node's proof-dependency list equals the union
of its proof-step uses. There are no overlong Lean lines. The project
`leanindex.interface_changes` check returns an empty list after the proof-local scoping fix.

The construction handles arbitrary, including nonflat and nonsurjective, ring maps,
zero coefficient rings, and unbounded complexes. The representative identity is proved
for every homotopy representative; its public statement retains the original K-flat
and flat-term hypotheses. No target or unit statement changes.

## No longer needed

Removed these private proof imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.Paper.RingedTopoiTensorSections`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`

The item's proof no longer directly needs these planned nodes:

- `lem-pc-kflat-resolution`: adjoint uniqueness constructs the derived comparison
  directly, without choosing another resolution.
- `def-weil-pbc-ringed-tensor-section-calculus`: the normalized ordinary unit and
  linearity give the two tensor formulas.
- `lem-weil-pbc-site-derived-tensor-descent`: the existing derived Hom comparison
  identifies the representative, so another descent construction is unnecessary.
- `lem-weil-pbc-localization-universal-property`: the exact-functor factorization API
  and adjoint coherence provide the needed comparison equalities.
- `def-pur-sheaf-tensor-product`: the existing change-of-rings construction and its
  normalized ordinary adjunction already supply the tensor data.

Removed the obsolete top-level tool-use entries `lem-pc-kflat-resolution` and
`lem-weil-pbc-site-derived-tensor-descent`. The remaining approvals retain their order.
These are removals from this item's direct proof route. Dependencies still needed by
other modules or inside the existing adjunction theorems remain intact; no module is
withdrawn and no global unreachability claim is made. Public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement error or definition repair was needed. The DAG's original resolving-class
construction is longer than necessary given the now-proved normalized adjunction and
homotopy Hom-comparison interfaces. The replacement route preserves the unit's own
statement and its use of successive normalized derived extension. No forced adaptations
or new nodes were required.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
