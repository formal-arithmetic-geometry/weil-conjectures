## Worker report

The module `Sheaf.CategoryTheory.GrothendieckDerivedCoproducts` states
`DerivedCategory.isColimit_mapCocone_grothendieckSum`. Its only theorem has proof
`sorry`; no definitions, auxiliary theorems, new nodes or dependency repairs are added.
The item JSON changes only in `lean`.

Source read: `literature/stacks-project/injectives.tex`, Tag 07D9,
`lemma-derived-products`, lines 2008–2046: direct sums in the derived category
are termwise direct sums of arbitrary complexes. The proof uses K-injective
targets and restriction of Hom classes, exactly as the node's five proof steps.
All five steps are reproduced in the theorem docstring with their dependency ids.

Hypotheses and clauses, in order:

- The abelian category is `(A : Type u) [Category.{v} A] [Abelian A]`.
  `[IsGrothendieckAbelian.{w} A]` is the recorded Mathlib notion for
  `def-sp-grothendieck-abelian`: exact filtered colimits and a generator,
  with all colimits of the chosen size supplied by its `hasColimits` instance.
  The object, Hom and indexing universes remain independent.
- The chosen localization is `[HasDerivedCategory.{t} A]`, with
  `DerivedCategory.Q (C := A)`. This is the recorded interface of
  `def-weil-abstract-derived-category`, not an arbitrary functor or replacement
  localization. The derived Hom universe `t` is independent as well.
- An arbitrary set in the chosen indexing universe is `(I : Type w)`;
  the family `(K : I → CochainComplex A ℤ)` consists of unbounded complexes.
  No `Countable`, `Nonempty`, boundedness or other hypotheses are added.
- Existence of the termwise coproduct complex is implemented by the existing
  real construction
  `HomologicalComplex.coconeOfHasColimitEval (Discrete.functor K)`.
  Its required degreewise colimits are inferred from the Grothendieck hypothesis.
  In `Mathlib/Algebra/Homology/HomologicalComplexLimits.lean:145–167`, this
  cocone's point has `X n = colimit (Discrete.functor K ⋙ eval A _ n)`;
  its differential is `colimMap` of the component differentials, and its legs
  have components `colimit.ι`. Thus it is precisely the termwise sum with
  the induced differential, rather than merely some derived coproduct.
  The chain-level universal property is already supplied by
  `HomologicalComplex.isColimitCoconeOfHasColimitEval` in that same module.
- The conclusion `Nonempty (IsColimit (Q.mapCocone ...))` asserts that the
  image of this particular cocone is colimiting. `mapCocone` maps its point
  and every leg by Q, so the legs are exactly the images of the termwise
  coprojections. The discrete diagram has objects Q(K i); its colimit is
  the requested coproduct, with the full existence and uniqueness property.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`,
  `CategoryTheory.IsGrothendieckAbelian`, lines 53–77, and `hasColimits`, line 99.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, lines 68–99.
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`,
  `HomologicalComplex.coconeOfHasColimitEval`, lines 145–163 (construction).
- Proof-only import
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`:
  `CochainComplex.kInjectiveResolutionFunctor`, `toKInjectiveResolution`,
  `monoQuasiIso_toKInjectiveResolution_app`,
  `isKInjective_kInjectiveResolutionFunctor_obj`, read at lines 133–163.
  This is the recorded interface of
  `lem-weil-pbc-kinjective-functorial-existence`.
- Proof-only import `Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
  `CochainComplex.IsKInjective.Qh_map_bijective`, lines 41–46, the exact
  Mathlib match for `lem-sc-kinjective-quasi-iso-comparison`.

Edge cases checked: an empty I gives degreewise initial objects and a mapped
empty cocone, so the conclusion asserts initiality in D(A), with no exclusion
by a typeclass hypothesis. A singleton gives the usual representative complex
up to its canonical coproduct isomorphism. Families of zero complexes give a
zero termwise complex up to unique isomorphism. Arbitrarily unbounded complexes
are permitted because the degree index is all of ℤ and no support predicate
occurs. Independent universes w, v, u, t impose no equality between indexing,
source objects, source morphisms and derived morphisms.

Searches performed:

- `msearch.py leanfinder`: "Termwise coproducts of unbounded complexes in a
  Grothendieck abelian category compute coproducts in its derived category".
  Eight hits: Grothendieck/AB5 instances for complexes, HasExt,
  HasDerivedCategory and its standard construction, ind categories, and a
  derived t-structure lemma. None states this coproduct property.
- `msearch.py loogle`: `"DerivedCategory.Q", "PreservesColimitsOfShape"`.
  Zero hits.
- `msearch.py grep`: `coproduct|PreservesColimitsOfShape|preservesColimit`
  restricted to `Algebra/Homology/DerivedCategory`. Zero hits.
- `msearch.py leansearch`: "Termwise coproducts compute coproducts in the
  derived category of a Grothendieck abelian category". Service unavailable
  (Internal Server Error), not evidence of absence.
- `rg` of the upstream `WeilConjectures` tree for the item id: zero hits.
  Searches for coproducts in its GrothendieckAbelian and DerivedCategory
  directories found colimit infrastructure, tensor preservation and derived
  adjunctions, but no declaration of the present assertion. The upstream
  GrothendieckCategory/Basic discrete-colimit helper was read: it concerns
  coproducts in A, not in D(A).
- `rg` of `lean/Sheaf` for derived coproducts and `Q.mapCocone` found related
  modules. Read `DerivedCountableSumsExact.lean`: it assumes Countable I and
  exact countable sums, so is not this arbitrary-index assertion. Read
  `DerivedAmbientDirectSumsCofan.lean`: it specializes to module sheaves on
  a scheme, so does not state the general-category result. Existing module
  sums are similarly specialized. No private copy of a notion is introduced.
- Searched the proposed declaration name in Mathlib, upstream, side modules
  and `dag/lean_names_upstream.json`: no collision.

Validation: prescribed `scompile.py NF lem-kun-grothendieck-derived-coproducts`
compiled the delivered module in both sandbox and library-path modes, with
no errors or warnings. No global build or direct repository mutation was run.
There is no statement dispute or node fault.

## Second reading by NF

Independently read the item JSON, the complete proposed module, Stacks
`injectives.tex`, Tag 07D9 (`lemma-derived-products`), and the preceding remark
`remark-existence-D`. The source assumes only a Grothendieck abelian category;
its direct-sum assertion uses arbitrary complexes and set-indexed families.
The product assertion is outside this node's stated scope.

Object/hypothesis/conclusion checklist, in node order:

| Node clause | Lean rendering and verdict |
| --- | --- |
| Abelian category A | `(A : Type u) [Category.{v} A] [Abelian A]`: exact. |
| Grothendieck, in the chosen indexing universe | `[IsGrothendieckAbelian.{w} A]`: exact size-relative notion. Read the dependency's `mathlib_match` and Mathlib Basic lines 53–104: locally small at w, exact w-filtered colimits, a separator, and inferred w-small colimits. At w = v local smallness is automatic; the independent-w interface is the documented ShrinkHoms-invariant version. |
| Localization Q at quasi-isomorphisms | `[HasDerivedCategory.{t} A]` and `Q (C := A)`: exact recorded dependency interface. Read DerivedCategory Basic lines 68–109, including the `IsLocalization` instance. This chooses the localization and its Hom universe, rather than assuming an additional mathematical property of A. |
| Every set I and family of unbounded complexes | `(I : Type w) (K : I → CochainComplex A ℤ)`: exact; no countability, nonemptiness or support bound. |
| Termwise coproduct exists, with induced differential | `HomologicalComplex.coconeOfHasColimitEval (Discrete.functor K)`: exact real construction, not an existentially chosen substitute. Read HomologicalComplexLimits lines 145–167: objects are the degreewise `colimit`, differentials are `colimMap`, and legs have components `colimit.ι`. All degreewise colimits follow from the Grothendieck instance. Its already-proved chain universal property is `isColimitCoconeOfHasColimitEval`; no new theorem is needed for this clause. |
| Its image, with images of the coprojections, is the derived coproduct | `Nonempty (IsColimit ((Q (C := A)).mapCocone ...))`: exact existence and full universal property for the particular point and legs. The mapped diagram has objects Q(K i). Quantification over derived targets and uniqueness are contained in `IsColimit`. |
| Empty set included | No `Nonempty I` binder: exact. The mapped empty cocone is asserted initial. |

Read both proof-dependency node records and their actual declarations:
`CochainComplex.kInjectiveResolutionFunctor`, `toKInjectiveResolution`,
`monoQuasiIso_toKInjectiveResolution_app` and
`isKInjective_kInjectiveResolutionFunctor_obj` (upstream KInjectiveResolution,
lines 133–163, with universe-polymorphic Grothendieck assumptions at line 74),
and `CochainComplex.IsKInjective.Qh_map_bijective` (Mathlib KInjective,
lines 41–46). They provide unbounded K-injective targets and the exact
localization Hom bijection required by proof steps 3 and 4. The declaration
docstring reproduces all five node proof steps, including assembly of homotopies,
transport to arbitrary targets, and the empty case. Imports match the statement
and these recorded proof dependencies.

Edge cases: empty I, singleton I, and families of zero complexes are all admitted.
The zero category is admitted; an empty abelian category is not possible because
it has a zero object. Degree zero is an ordinary integer degree and there is no
boundedness condition. No scheme, ring, field, or characteristic hypothesis occurs.
Universes u (objects), v (source Homs), w (indexing/Grothendieck size), and t
(derived Homs) are explicitly bound and independent. No universe equality,
Noetherian condition, finiteness condition or extra instance has been inserted.

Independent searches used different wording from the first reader:

- `msearch.py ... leanfinder`: "Localization of complexes in an AB5 abelian
  category sends degreewise direct sums to direct sums in the derived category".
  Eight hits concern complexes being Grothendieck, additive/linear derived
  categories and localization; none asserts this coproduct property.
- `msearch.py ... loogle`: `"DerivedCategory.Q", "PreservesColimit"`: zero hits.
- `rg` for coproduct/direct-sum/preserves-colimit terminology in Mathlib's
  DerivedCategory and Localization trees and upstream GrothendieckAbelian and
  DerivedCategory trees: no equivalent theorem. Upstream tensor colimits and
  left-derived-functor hypotheses do not state this assertion.
- Searched the side library, read `DerivedCountableSumsExact` in full (countable
  index hypothesis), `DerivedAmbientDirectSumsCofan` (scheme module sheaves),
  and the signature and generic helper in `DerivedModuleDirectSums` (modules
  over a ring). None is this arbitrary Grothendieck-category statement.
  `GrothendieckDerivedBrownRightAdjoint` assumes coproducts for a different
  conclusion and supplies no replacement. Checked the proposed name and node
  id against upstream, side Lean, and `dag/lean_names_upstream.json`: no collision.

No mismatch found; no Lean or node edits were needed. No new definition nodes,
dependency modules, private notions, hollow definitions or statement correction
are present. The sole theorem remains `by sorry`, as required for stage 2.
The node's `lean.statement` was checked against the file signature verbatim.

Validation: the prescribed `scompile.py` compiled the delivered file in sandbox
and library-path modes cleanly (1.4 seconds each), with no warnings or errors.
Only this second-reading report was added.
