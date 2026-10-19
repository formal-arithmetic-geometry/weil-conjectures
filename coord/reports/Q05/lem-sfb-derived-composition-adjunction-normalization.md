## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`
contains one concrete helper and one theorem with `sorry`:
`CategoryTheory.Adjunction.derivedCompositionLeftIso` names the canonical descent of
lambda, including the standard exact-functor composition identification;
`CategoryTheory.Adjunction.derivedCompositionAdjunctionNormalization` states the
complete comparison and its normalization. No theorem is proved and no data is
postponed. The node changes only in `lean`.

Hypothesis and clause correspondence:

- The categories A, B, C are separate `Type uA`, `Type uB`, `Type uC` with
  `Category.{vA}`, `Category.{vB}`, `Category.{vC}`, `Abelian`, and
  `IsGrothendieckAbelian` in the respective hom universes. These are precisely the
  three Grothendieck abelian categories. No equality of universes is imposed.
- Their ordinary unbounded derived categories are `DerivedCategory A/B/C` with
  independent explicit `HasDerivedCategory.{wA/wB/wC}` size conventions. No boundedness,
  monoidal structure, flat resolution hypothesis, or bounded-derived substitution occurs.
- `La : A ⥤ B`, `Lb : B ⥤ C`, `Lc : A ⥤ C` and their three `Additive` instances
  give the exact additive left functors. Exactness is expressed by
  `PreservesFiniteLimits` and `PreservesFiniteColimits` on each functor.
- `Ra : B ⥤ A`, `Rb : C ⥤ B`, `Rc : C ⥤ A` with `Additive` and the actual data
  `adja : La ⊣ Ra`, `adjb : Lb ⊣ Rb`, `adjc : Lc ⊣ Rc` specify the additive right
  adjoints and their unit/counit structures. No arbitrary derived adjunction is supplied.
- `eL : La ⋙ Lb ≅ Lc` is lambda. Composition notation is in application order,
  so `La ⋙ Lb` means Lb La, while `Rb ⋙ Ra` means Ra Rb.
- The ordinary kappa is exactly
  `conjugateIsoEquiv adjc (adja.comp adjb) eL`. It is used directly in the
  representative equation, so there is no extra independent comparison parameter.
- The helper `derivedCompositionLeftIso La Lb Lc eL` is D(lambda), with definition
  `(Functor.mapDerivedCategoryCompIso La Lb).symm ≪≫
  Functor.mapDerivedCategoryNatIso eL`. The two internal `letI` values are existing
  proofs that composites of exact functors are exact; there is no file-local instance
  and no extra hypothesis on the composite in the theorem.
- `Ri.rightDerivedFunctor` is total unbounded right derivation, with its canonical
  `Ri.rightDerivedFunctorUnit`. Grothendieck K-injective resolutions supply the required
  resolution instances automatically. The resolution construction happens to provide
  monomorphic quasi-isomorphisms, but no monomorphism or chosen resolution is an added
  hypothesis of this statement.
- Every derived adjunction in the conclusion is
  `adji.mapDerivedCategoryRightDerivedAdjunction`, the canonical adjunction induced
  from that precise underived adjunction. It is constructed by the derived-adjunction
  API with the exact left descent comparison and the right-derived unit. Thus its
  normalization agrees with the canonical bijection specified by
  `lem-pc-derived-adjoint-functors`, rather than an arbitrary adjunction on the same functors.
- The existential is a natural *isomorphism*
  `κD : Rc.rightDerivedFunctor ≅ Rb.rightDerivedFunctor ⋙ Ra.rightDerivedFunctor`.
  The first conjunct identifies it with `conjugateIsoEquiv` applied to D(lambda),
  using `adjc`'s derived adjunction and the actual composite derived adjunction.
- `∀ (I : CochainComplex C ℤ) [I.IsKInjective]` covers every K-injective complex.
  Its first conjunct is `IsKInjective ((Rb.mapHomologicalComplex (.up ℤ)).obj I)`.
  `CochainComplex.IsKInjective` says literally that every map from an acyclic complex
  is homotopic to zero.
- The second conjunct is the representative equation
  `beta_c,I ≫ κD(QI) = Q(C(kappa)_I) ≫ comp_inv ≫ beta_a,C(Rb)I ≫ RRa(beta_b,I)`.
  Here Q is written as `DerivedCategory.Qh` after `HomotopyCategory.quotient`.
  `NatTrans.mapHomotopyCategory` gives the homotopy class of the termwise map.
  `Functor.mapHomotopyCategoryCompIso ... .inv` explicitly identifies the image of
  the composite with the composite images. This records both resolution comparisons,
  including application of RRa to the inner comparison; it does not forget that factor.
  The standard units are invertible at I and at C(Rb)I, as required by the preceding
  K-injectivity clause, so this equation is exactly the stated formula after the
  canonical resolution identifications. It is not an assumption on those comparisons.
- The universal quantifier on `X : DerivedCategory A` expresses
  `eta_ba,X ; R_ab(D(lambda)_X) = eta_c,X ; κD_D(Lc)X` using `.comp`'s unit.
- The universal quantifier on `Y : DerivedCategory C` expresses
  `D(Lba)(κD_Y) ; epsilon_ba,Y = D(lambda)_RRc(Y) ; epsilon_c,Y` using `.comp`'s
  counit. These are exactly the final two equations of the node's proof, in Lean's
  left-to-right composition convention.

Dependency declarations and source inspection:

- `def-sp-grothendieck-abelian`: Mathlib module
  `CategoryTheory.Abelian.GrothendieckCategory.Basic`, `CategoryTheory.IsGrothendieckAbelian`.
  Its full class signature and universe convention were read.
- `def-weil-abstract-derived-category`: Mathlib module
  `Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.Qh`. Their localization signatures were read.
- `def-weil-pbc-adjunction-conjugate`: Mathlib module
  `CategoryTheory.Adjunction.Mates`, `conjugateEquiv`, `conjugateIsoEquiv`.
  Their direction, component formula, and the isomorphism construction were read.
- `def-weil-pbc-composite-adjunction`: Mathlib module
  `CategoryTheory.Adjunction.Basic`, `Adjunction.comp`, `comp_unit_app`,
  `comp_counit_app`, `comp_homEquiv`. This is the actual composite adjunction.
- `sk-def-sfb-derived-categories` is an umbrella node without a Lean record in the
  current DAG. Every notion needed from its abstract, right-derived/exact portion is
  already supplied by the recorded abstract-derived node and existing upstream modules:
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`,
  `CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`;
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`,
  `Functor.rightDerivedFunctor` and `Functor.rightDerivedFunctorUnit`;
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`,
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction`; and
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
  `Functor.mapDerivedCategoryNatIso` and `Functor.mapDerivedCategoryCompIso`.
  Their full signatures/docstrings were read. There is no missing abstract notion
  requiring a second definition. This consumer does not require the umbrella node's
  unrelated pro-etale coefficient or K-flat/monoidal specializations.
- `lem-pc-derived-adjoint-functors`: the recorded module
  `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors` is publicly imported.
  Its `Adjunction.exists_derived_adjunction_of_essentially_constant` and its final
  hom-bijection compatibility clause were read. The upstream exact-left construction
  is that induced canonical adjunction for the particular universal pairs in use.
- Proof dependencies are imported, including the recorded
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` and
  `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`. The former's universal,
  uniqueness, and K-injective-unit clauses give the unit-compatible identification
  with its arbitrary-quasi-isomorphism construction when that construction is chosen.
  No new copy of the total derived functor is defined. The exact-left upstream
  adjunction module also imports the recorded `Adjunction.preservesKInjectiveComplexes`
  from `RightDerivedFunctor.Comp` and `Adjunction.mapHomotopyCategory` from
  `HomotopyCategory.Adjunction`; their signatures and docstrings were inspected.
  Mathlib `Algebra.Homology.DerivedCategory.KInjective` provides the recorded
  `CochainComplex.IsKInjective.Qh_map_bijective`.

Source grounding: read `literature/stacks-project/derived.tex` at
`lemma-derived-adjoint-functors` (Tag 09T5) and the following definition of K-injectivity;
read `sites-cohomology.tex` at `lemma-derived-pushforward-composition` (Tag 0D6E).
The latter explicitly constructs composition by left composition and uniqueness of
adjoints. The node's six-step proof supplies the precise representative calculation
and is retained step by step in the theorem docstring.

Edge cases: zero categories, zero complexes, identity functors, and identity comparisons
are included. The equation uses no cancellation of a potentially noninvertible derived
unit; only units on K-injectives become isomorphisms when interpreting the displayed
representative. Arbitrarily unbounded complexes are allowed. Underlying object, hom,
and localization universes are all separately bound; there is no equal-universe API
restriction. The counit equation has source D(Lba)(RRc Y) on both sides and target Y;
the unit equation has source X on both sides and target RRab(D(Lc)X).

Searches (2026-10-18), made using the prescribed `msearch.py` wrapper:

- LeanFinder: `derived composition of right adjoints conjugate to exact left adjoint
  composition on K injective resolutions`: eight hits, including `Adjunction.derived`,
  `derivedε`, `derivedε_fac_app`, and bounded injective-resolution functoriality.
  None is the complete normalization statement.
- Loogle: `CategoryTheory.Adjunction.derived`: three hits, `derived`, `derived_counit`,
  `derived_unit`. These construct the adjunction, rather than state this composition law.
- Mathlib grep: `derived.*[Cc]onjugate|[Cc]onjugate.*derived` in CategoryTheory:
  zero hits.
- LeanSearch: `Composition of total right derived functors of right adjoints of exact
  functors is conjugate to composition of their left adjoints`: eight hits, including
  `Functor.totalRightDerived`, `conjugateIsoEquiv`, and `Adjunction.derived'`.
  None is the full statement.
- `rg` in the upstream `WeilConjectures/CategoryTheory/DerivedCategory` sources found
  `RightDerivedFunctor/CompConjugate.lean`. Its full theorem
  `Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv` was read. It gives
  the conjugacy identity for the oppositely oriented comparison with a shared hom
  universe and an explicit K-injective-preservation instance. It does not state the
  K-injective representative, the preservation conclusion, or the unit/counit
  normalization clauses of this node. It is therefore not an exact existing binding.
- `rg` in `lean/Sheaf` for derived composition/adjunction and the chosen declaration
  names found no existing complete declaration; occurrences of this node in other
  module docstrings only cite it as a future dependency. Searching the upstream
  `WeilConjectures` sources for the node id returned no match. Searching Mathlib and
  both project trees for the new names returned no collision.

Validation: `scompile.py Q05 lem-sfb-derived-composition-adjunction-normalization
<module>` compiled the delivered module successfully, both as a sandbox and under
its final module name (1.6 s and 1.7 s), with no errors or warnings. No statement
correction, disputed statement, new independent notion, or dependency repair was needed.

## Second reading by Q05

Author's final self-check, with the node and module open; independent review is left
to the maintainer as required by the dispatch brief. I checked the direction of all
four comparisons (lambda, kappa, descended lambda, kappaD), the reversal in
`Adjunction.comp`, and each of the three concluding normalizations. The representative
includes the often omitted `RRa(beta_b)` factor. The explicit composition identification
has direction `(Rb ⋙ Ra)_h → Rb_h ⋙ Ra_h`; the returned termwise K-injectivity
statement concerns Rb(I), exactly as the node requires. Both unit and counit refer to
the actual composite adjunction. The only implementation correction was renaming the
reserved Lean token lambda to `eL`; this changed no mathematical statement. No extra
hypotheses or clauses and no omitted clause were found.
