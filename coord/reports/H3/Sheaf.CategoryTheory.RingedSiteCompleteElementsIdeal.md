## What changed

The existing statement of `CategoryTheory.ringedSite_complete_elements_ideal` is unchanged.
Its proof now constructs the ideal with the complete-element predicate as its carrier.
Localization at zero is proved zero directly from its sequential colimit. Addition is
proved by applying the contravariant triangulated derived-Hom functor to the degree-zero
triangle of the localization short exact sequence. The biproduct term is handled using
its identity decomposition. Restriction, covering-sieve descent, and the locally generated
ideal consequence are complete Lean proofs.

Six new modules record the needed parts of the argument:

- `Sheaf.CategoryTheory.RingedSiteCompleteElementMul`: multiplicative stability; proved
  from the coefficient-model comparison and existing Hom-complex and K-flat APIs.
- `Sheaf.CategoryTheory.RingedSiteLocalizationFractionComparison`: the comparison of the
  sequential coefficient with the sheafified fraction coefficient; unfinished.
- `Sheaf.CategoryTheory.RingedSiteLocalizationSumSequence`: the two-element short exact
  sequence of localization module sheaves; unfinished.
- `Sheaf.CategoryTheory.RingedSiteLocalizationRestriction`: proved. Restriction commutes
  with sheafification by the locally bijective unit criterion, hence with sequential
  colimits. The restricted unit and multiplication maps identify the diagrams.
- `Sheaf.CategoryTheory.RingedSiteCompleteElementRestriction`: proved from the preceding
  coefficient comparison and the existing internal derived-Hom restriction theorem.
  The proof identifies the chosen-representative derived restriction with the induced
  exact derived functor, then uses its composition and degree-zero comparisons.
- `Sheaf.CategoryTheory.RingedSiteCompleteElementLocal`: proved. Exact restriction
  commutes with cohomology; a module sheaf which restricts to zero on a covering sieve
  is zero by separatedness on the pulled-back sieve. Cohomology reflects zero objects.

The sheafification proof generalizes the argument of
`SheafOfModules.exists_open_localized_sheafification` from topological opens to maps
between arbitrary slice sites; the original theorem cannot be applied to this general site.
No definition, existing public signature, target statement, or other group's module changes.

## Proved and sorry left

The original hole `CategoryTheory.ringedSite_complete_elements_ideal` is closed by a
complete Lean proof from the named declarations below. This is a decomposition, not a
claim of a complete proof with only the three permitted axioms: one old hole is removed
and two new holes remain (net minus one by the closed-minus-added measure).

New theorems with complete Lean proofs from the named dependencies:

- `CategoryTheory.ringedSite_complete_element_mul`
  (`lem-weil-pbc-ringed-complete-element-mul`). This uses the ordinary Hom-total-tensor
  isomorphism on K-injective representatives, the K-flatness of the fraction coefficient,
  and the existing coefficient tensor-product comparison. The only new premise is the
  plain coefficient-model isomorphism below; no fixed derived-category universe is used.

- `CategoryTheory.ringedSite_localization_restriction`
  (`lem-weil-pbc-ringed-site-localization-restriction`).
- `CategoryTheory.ringedSite_complete_element_restriction`
  (`lem-weil-pbc-ringed-complete-element-restriction`).
- `CategoryTheory.ringedSite_complete_element_local`
  (`lem-weil-pbc-ringed-complete-element-local`).

Exactly two `sorry`s remain in the delivery, each as the entire proof of a named public
statement in its own module:

- `CategoryTheory.ringedSite_localization_fraction_comparison`
  (`lem-weil-pbc-ringed-site-localization-fraction-comparison`). It still needs the actual
  compatible fraction cocone, its universal property among module presheaves, and the
  resulting sheafification comparison. Its statement is a plain isomorphism of module
  sheaves: it has no derived category, vanishing predicate, or completeness hypothesis.
  The docstring gives the maps and the fraction-relation verification in full.
  In scratch, the ordinary `ModuleCat` comparison was checked by Lean: multiplication
  by f on the sequential colimit has inverse given by the shifted colimit injections;
  `Module.End.isUnit_iff` supplies the hypothesis for `IsLocalizedModule.lift`.
  The lift extends the stage-zero injection, and colimit extensionality proves the
  inverse identities. What remains is making these maps natural in the presheaf and
  transporting the colimit through module sheafification. This scratch calculation is
  not counted as an additional delivered theorem.
- `CategoryTheory.ringedSite_localization_sum_sequence`
  (`lem-weil-pbc-ringed-localization-sum-sequence`). It still needs the actual module
  maps, sectionwise exactness, sheafification, and transport along the stated
  coefficient-model comparison. The docstring supplies the diagonal/difference maps and the
  binomial surjectivity argument. It has no derived-category hypothesis or conclusion.

There are no `sorry`s in definitions, private helpers, the four proved new modules,
or the item module. No axioms or forbidden declarations are introduced.

Validation: all seven delivery modules compile together through `lcompile.py --all`;
the item signature is unchanged, and each new node records its verbatim Lean signature.

Edge cases checked mathematically: zero/nilpotent localization, either multiplier zero,
f + g = 0 (all terms of the localization sequence are zero), zero rings, empty covering
sieves, and zero generators. The locality proof uses arbitrary covering sieves and
requires neither pullbacks in the original site nor boundedness of the derived object.

## No longer needed

Removed these proof imports from the item module:

- `Mathlib.RingTheory.Localization.Away.Basic`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
- `Sheaf.Algebra.Homology.DerivedInternalHom` (already available through the public
  complete-element definition and used through the exactness API).
- `Sheaf.CategoryTheory.RingedSiteModules` (already a statement dependency).
- `Sheaf.Paper.RingedLocalizationRHomCalculus`.

The parent node no longer directly uses
`lem-weil-pbc-ringed-localization-rhom-calculus`,
`lem-weil-pbc-standard-covering-glue`, or
`lem-weil-pbc-ringed-site-module-sheafification-exact`. Their necessary portions now
belong to the multiplication and short-exact-sequence obligations, respectively;
these nodes have not been pruned from the transitive argument.
The parent no longer directly uses `def-pur-derived-internal-hom` or
`def-weil-sheaf-of-modules-category` as proof dependencies; both remain statement
or transitive dependencies. Its explicit cone/cohomology boundary chase is replaced
by `ShortComplex.ShortExact.singleTriangle_distinguished` and exactness of derived Hom.
No existing node or module is claimed globally unnecessary, and none is withdrawn.
The blueprint unit and its realized steps are retained.

## Where the brief, the DAG or earlier work was wrong

No disputed mathematical statement was found. The declared localization calculus uses
sheafified fraction localizations and fixes `HasDerivedCategory.standard`, whereas
this item's predicate uses sequential colimits and an arbitrary localization universe.
Thus its formulas are not immediately applicable to the predicate by elaboration or
rewriting. The proved multiplication theorem avoids the universe issue by using ordinary
Hom-total-tensor on K-injective representatives. The remaining plain module isomorphism
records the coefficient comparison explicitly, rather than silently equating the models.

The definition of `ringedSiteDerivedRestriction` uses a chosen representative and is not
itself the exact derived restriction functor. The proved comparison module explicitly
connects it to that functor using the factorization through Q and the representative
isomorphism. The omitted sheaf verification in Tag 0998 has been carried out in Lean
using arbitrary covering sieves, not just a family of chosen covers.

## New nodes

`lem-weil-pbc-ringed-complete-element-mul` records the multiplicative clause of the
ideal argument, now proved from the coefficient comparison and existing representative APIs.

`lem-weil-pbc-ringed-site-localization-fraction-comparison` records the common plain
module isomorphism needed by multiplication and the localization sequence. It has one
remaining hole. It is strictly a part of the argument, with none of the derived or ideal
conclusions of the original item.

`lem-weil-pbc-ringed-localization-sum-sequence` records the purely module-theoretic
localization sequence. It has one remaining hole; the proof combining it with
multiplicative stability and a distinguished triangle is already complete.

`lem-weil-pbc-ringed-site-localization-restriction` records the proved coefficient
comparison, with a proof of the necessary sheafification and colimit facts.

`lem-weil-pbc-ringed-complete-element-restriction` records the proved derived-Hom
comparison obtained from coefficient restriction and existing exact functor APIs.

`lem-weil-pbc-ringed-complete-element-local` records the proved covering-sieve criterion.

Each new node has its source, self-contained statement, proof steps, dependency union,
three kinds of Mathlib search, and the verbatim public Lean signature. The parent node's
proof and proof dependencies match the implementation. There are no change records,
since no existing statement or definition changes.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
