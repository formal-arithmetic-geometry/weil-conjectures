## Worker report

The module [lean/Sheaf/Paper/ProperCompactCoincidence.lean](lean/Sheaf/Paper/ProperCompactCoincidence.lean) states the blueprint proposition
`prop-weil-proper-compact-coincidence`. It has one real auxiliary definition,
`WeilConjectures.properCompactPointOver`, which supplies the identity structure
morphism on `Spec D.k`; its data are `⟨𝟙 _⟩`, not postponed data. The theorem
`WeilConjectures.properCompactCoincidence` has the one expected `sorry` proof.

The hypotheses are rendered as follows.

* `D : FiniteFieldDatum.{u}`, `l : ℕ`, `[Fact l.Prime]`, and
  `hl : l ≠ D.p` are the finite-field and invertible-prime data from
  `def-weil-ordinary-compact-cohomology`.
* `Ω : Type u` with `[Field Ω]`, `[Algebra (Padic l) Ω]`, and
  `[IsAlgClosure (Padic l) Ω]`, together with
  `E₀ : Padic.FiniteCoefficientFields l Ω`, is the common algebraically closed
  coefficient datum used by the finite-stage and common-stage constructions.
* `Y : Scheme.{u}` has
  `[Y.Over (Spec (CommRingCat.of D.k))]`. The single geometric hypothesis
  `[IsProper (Y ↘ Spec (CommRingCat.of D.k))]` is exactly properness of the
  structure morphism. Properness supplies the separated, locally finite type,
  and quasi-compact properties required by the recorded coefficient categories.
* `c : Compactification (Y ↘ Spec (CommRingCat.of D.k))` is the compactification
  appearing in the compact-support definitions, and `n : ℕ`, `hn : 1 ≤ n`
  select a positive finite coefficient stage.

The conclusion is a conjunction whose clauses are written directly in Lean.

1. The first `Nonempty` is a natural isomorphism between the intrinsic finite
   torsion compact-support functor, restricted along
   `intrinsicFiniteTorsionConstructible.ι`, and
   `proEtaleConstantDerivedDirectImage`. This is the finite-level
   `Ra_{Y!}=Ra_{Y*}` comparison, with the actual compact-support construction
   `sfIntrinsicCompactSupport`.
2. The second `Nonempty` compares
   `sfCompactSupportFiniteIntegralFunctor ... c ⋙ (sfIntegralConstructible ... (Spec ...)).ι`
   with the ordinary integral functor
   `(sfIntegralConstructible ... Y).ι ⋙ sfCompletedDerivedDirectImage ...`.
   This records the completed integral derived-direct-image comparison.
3. The third `Nonempty` compares the recorded rational compact-support action at
   `c` with the same action at
   `Compactification.ofIsProper (Y ↘ Spec (.of D.k))`, the identity
   compactification supplied by properness.
4. The fourth clause gives, for every
   `SfCompactSupportCoefficientAction` package `S` at `c` and every such
   package `S₀` at the identity compactification, a natural isomorphism
   between their `.system.functor` values. It uses the normalized coefficient
   action, rather than introducing an arbitrary functor or a bare choice of
   isomorphism. (Maintainer review fix: the delivered `∃ S, ∃ S₀` was replaced by
   `∀ S, ∀ S₀`, as in `sfFieldShriekCompositionQbar_existsUnique`; the existence of
   such packages is `sfCompactSupportFiniteFieldIndependence`.)
5. For every finite torsion constructible `K`, the next clause gives a
   `Nonempty` isomorphism between `finiteCompactSections` and
   `finiteOrdinarySections`, followed by a `Nonempty` isomorphism between
   `finiteCompactCohomology ... i` and `finiteOrdinaryCohomology ... i` for
   every `i : ℤ`.
6. For every integral constructible `K`, it gives the image isomorphism
   `sfIntegralCompactSupportValue ≅ integralImage`, the sections isomorphism
   `integralCompactSections ≅ integralOrdinarySections`, and the cohomology
   isomorphism in each integer degree.
7. For every rational constructible `K`, it gives the corresponding
   `sfRationalCompactSupportValue ≅ rationalImage`, sections, and all-degree
   cohomology isomorphisms.
8. For every
   `K : generalAlgebraicallyClosedConstructibleCategory l Ω Y`, it gives the
   corresponding `sfQbarCompactSupportValue ≅ qbarImage`, sections, and
   all-degree `qbarCompactCohomology ≅ qbarOrdinaryCohomology` clauses.

The direct-image and section clauses use the actual definitions in
`Sheaf.Paper.OrdinaryCompactCohomology`: `finiteOrdinarySections`,
`finiteCompactSections`, `integralImage`, `integralOrdinarySections`,
`integralCompactSections`, `rationalImage`, `rationalOrdinarySections`,
`rationalCompactSections`, `qbarImage`, `qbarOrdinarySections`, and
`qbarCompactSections`, with their cohomology definitions degreewise. The
finite compact-support side uses
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero` and the intrinsic
`sfIntrinsicCompactSupport`. The finite and coefficient action dependencies
recorded in `stmt_deps` are
`def-weil-compact-support-finite-action` and
`def-weil-compact-support-coefficient-action`; their declarations are
`WeilConjectures.sfCompactSupportFiniteIntegralFunctor`,
`WeilConjectures.sfCompactSupportFiniteFunctor`, and
`WeilConjectures.SfCompactSupportCoefficientAction` in
`Sheaf.Paper.CompactSupportFiniteAction` and
`Sheaf.Paper.CompactSupportCoefficientAction`. Other declarations used are
`WeilConjectures.sfCompletedDerivedDirectImage` from
`Sheaf.Paper.SfDerivedDirectImage`, and the ordinary/compact definitions from
`Sheaf.Paper.OrdinaryCompactCohomology`.

The proof docstring follows the source proof: the identity open immersion has
extension by zero equal to the identity, so finite-level terms and transition
maps agree; the integral towers therefore agree, localization gives the
rational comparison, and common finite stages give the algebraically closed
comparison. The identity compactification is represented by
`Compactification.ofIsProper`. Applying the recorded point fibre and
degreewise cohomology definitions gives the displayed sections and cohomology
clauses. The proof-only coherence import was deliberately omitted: importing
`Sheaf.Paper.CompactificationCoherence` through the old comparison chain
loads both old and new declarations of
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`, which
causes an environment-duplicate error. The needed finite-level and action
interfaces are already imported by the modules above.

Edge cases checked before writing the signature were the empty scheme, the
point `Spec D.k`, the identity compactification, the zero input object,
`n = 1`, and arbitrary integer cohomology degree (including negative
degrees). The statement retains properness; for a nonproper example such as
`𝔸¹`, compact-support and ordinary cohomology do not coincide. No smoothness,
connectedness, reducedness, or extra quasi-compactness hypothesis is added.

Searches for an existing declaration were made with the required tools. The
searches logged for this delivery are:

* `leanfinder`, “proper compact support direct image ordinary derived
  cohomology”: eight unrelated cohomology/derived hits, no match.
* `loogle`, “IsProper direct image compact support”: zero hits (the identifier
  was unknown).
* `grep`, “compactSupport|derivedDirectImage|ordinaryCompact” in Mathlib:
  zero hits.
* `grep`, “rightDerivedLowerShriekIsoRightDerivedLowerStar|compactlySupportedGlobalSectionsIsoOfIsProper”
  with the wrapper subdirectory argument `WeilConjectures`: zero hits; direct
  upstream `rg` nevertheless located the etale declarations discussed below.
* `leanfinder`, “rightDerivedLowerShriekIsoRightDerivedLowerStar”: generic
  localization/sheaf compatibility hits, no match.
* `loogle`, “AlgebraicGeometry.IsProper, CategoryTheory.Iso”: zero hits.

Direct searches of the source and project `lean/Sheaf` found no declaration
with this proposition's name. The related existing etale proper isomorphisms
were inspected and do not state the four coefficient, pro-etale comparison
written here. No new definition node, dependency repair, or statement
correction was required; there is no `STATEMENT-DISPUTED` item.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
