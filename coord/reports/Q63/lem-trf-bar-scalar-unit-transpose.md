## Worker report

Delivered module: `Sheaf.CategoryTheory.BarScalarUnitTranspose`.
Declaration: `CategoryTheory.categoryBarScalarUnitTranspose`.
It is one theorem with proof `sorry`, and no definitions, instances or additional
postponed theorems. The node's natural-language statement and dependencies are unchanged.

Sources read: Stacks `sites-cohomology.tex`, `example-left-derived-colimits` (08PG),
`example-morphism-categories` (08PH), `remark-morphism-fibred-categories`, and
`lemma-change-of-rings` (08Q8). The last lemma's printed functor order and adjoint
direction have the typed corrections already recorded in the node. The declaration
docstring carries all six proof steps of this node, including the finite-support inverse,
last face, representative transpose, composite-unit calculation and uniqueness.

### Hypotheses and conventions

- A small identity-cover category is `E : Type u` with `[SmallCategory E]`.
  The identity-cover module categories are exactly `Eᵒᵖ ⥤ ModuleCat.{u} R`
  and `Eᵒᵖ ⥤ ModuleCat.{u} S`, the presentations used in the recorded bar theorem.
  No nonempty, finite, filtered, skeletal or connected hypothesis is imposed.
- The coefficient map is `(φ : R →+* S)` with explicitly bound
  `{R S : Type u} [CommRing R] [CommRing S]`.
- The bar system is the recorded `B : CategoryColimitBarSystem.{u}`.
  `B.models E R` and `B.models E S` provide `derived`, `adjunction`, `bar`,
  `generator`, and the canonical degree-zero comparison `model`.
  The constant functors are `(Functor.const Eᵒᵖ).mapDerivedCategory`.
- `T₀` and `T₁` are the point and presheaf derived extensions, respectively.
  Their comparison transformations are `ε₀` and `ε₁`, with the ordinary termwise
  extensions exactly `ModuleCat.extendScalars φ` and its right-whiskering functor.
  `_h₀` and `_h₁` say these are universal left-derived pairs using
  `Functor.IsLeftDerivedFunctor` and the respective `HomologicalComplex.quasiIso`.
  These parameters unpack the source's specified derived extensions; they do not
  assume a comparison between the two composites or any desired unit equation.
  Quantifying over universal presentations avoids making a second choice of functor.
  Every such presentation is canonically equivalent to the dependency's derived pair.
- The theorem supplies `a₀` and `a₁`, the normalized adjunctions to exact scalar
  restriction, before `F` is quantified. The first two conjuncts give their
  representative Hom formula using `Adjunction.mapHomologicalComplex` and
  `mapDerivedCategoryFactors`. Thus an arbitrary, rescaled adjunction cannot be
  substituted, and normalization is a conclusion, not an extra assumption.
  Inserting the ordinary coefficient unit in these formulas gives x mapped to
  `1 ⊗ₜ[R,φ] x` on every K-flat model with invertible comparison.
- `F : Eᵒᵖ ⥤ ModuleCat.{u} R` is the module presheaf in degree zero.
  Its complex is `(CochainComplex.singleFunctor _ 0).obj F`.
  Its K-flatness is written as the definition's quantification over every acyclic
  presheaf complex `P`, requiring acyclicity of the existing
  `HomologicalComplex.mapBifunctor P F[0] (curriedTensor _) (.up ℤ)`.
  This is precisely the recorded acyclic-total-tensor definition, on the pointwise
  presheaf presentation. The ringed-sheaf predicate's endpoints cannot be applied
  directly to a `Functor`-valued complex. No alternative predicate is defined.
- Flat terms of `F[0]` are `(∀ U : Eᵒᵖ, Module.Flat R (F.obj U))`;
  the other terms are zero and flat. K-flatness of `K_R(F)` is the dependency's
  public `MorphismProperty.kFlat` specialized to cochain quasi-isomorphisms.
  Its flat terms are `(∀ q : ℤ, Module.Flat R (((B.models E R).bar.obj F).X q))`.
  Both K-flat assumptions and both flat-term assumptions are retained.
- The two `IsIso` conclusions certify the canonical tensor comparisons on these
  representatives: `ε₁.app F[0]` and `ε₀.app K_R(F)`.
  No flatness of S over R and no boundedness condition are added.
- All types and universes are bound explicitly, with `set_option autoImplicit false`.
  The standard bar-derived categories have localization universe `u+1`.
  No equality with the small-Hom `u` presentation in the ordinary scalar-extension
  API is imposed: the universal-pair presentation works at the bar's universe.

### Conclusions, clause by clause

1. The existential `Φ` is an isomorphism of cochain complexes of S-modules from
   `K_S(F tensor S)` to the termwise scalar extension of `K_R(F)`.
   A cochain isomorphism includes all differential-commutation and inverse laws;
   its image under `DerivedCategory.Q.mapIso` is the asserted isomorphism in D(S).
   Mathlib puts S first: `s ⊗ₜ[R,φ] x` is the source's `x tensor s`, via tensor
   symmetry. This convention is already used by the landed parent interface.
2. The first formula conjunct is exactly the forward rule in degree `-(n : ℤ)`:
   the S-bar generator with coefficient `s tensor x` maps to
   `s tensor (R-bar generator x)`.
3. The second formula conjunct gives the inverse for every finite sum:
   arbitrary `I : Type u`, finite `J : Finset I`, strings `σ i`, coefficients `x i`,
   and `s : S`. It distributes `s tensor sum_i (σ_i,x_i)` to
   `sum_i (σ_i,s tensor x_i)`. This covers all finite-support coproduct elements,
   including repeated strings and the empty sum. Positive terms are the zero
   terms from the recorded bar models; the cochain isomorphism covers them too.
4. `t_F` is the actual ordinary coefficient unit
   `((ModuleCat.extendRestrictScalarsAdj φ).whiskerRight Eᵒᵖ).unit.app F`.
   The existing unit formula identifies its sections with `1 tensor x`.
   There is no freely supplied semilinear map.
5. The existential `a` has the exact type `L_R F → r_* L_S(F tensor S)`.
   Its equation fixes it to `model_R.hom`, then `Q.map (B.map (𝟭 E) φ t_F)`,
   then the exact restriction localization factor, then restriction of
   `model_S.inv`. Thus it is precisely the canonical semilinear derived-colimit
   map, with the required `(σ,x) → (σ,1 tensor x)` representative by `B.formula`.
6. The existential `β` has type `T_* L_R F → L_S T_E F`.
   The `a₀.homEquiv` equation says its composite with the canonical target
   representative comparison transposes to `a`. This is the source's coefficient
   adjunct, with the target identification explicitly retained.
7. The next equation states that β is represented by `Φ.inv`: the β composite
   with `L_S(ε₁)`, the single-complex scalar-extension comparison, and
   `model_S.hom`, equals `T₀(model_R.hom)` followed by `ε₀` and `Q.map Φ.inv`.
   Thus the source and target representatives are the specified canonical ones.
8. The next equation is `V(β) η_B = η_A`.
   The composite adjunctions are `(B.models E R).adjunction.comp a₀` and
   `a₁.comp (B.models E S).adjunction`.
   At the ordinary level `restrictScalars φ ⋙ const_R` and
   `const_S ⋙ whiskeringRight(restrictScalars φ)` are definitionally the same.
   The inverses of their `Functor.mapDerivedCategoryCompIso` identify the two
   exact-derived composites with that single functor. Postcomposing both sides
   with those canonical identifications is the displayed unit equation.
9. Finally `c` is a natural isomorphism `B → A` on the WHOLE derived categories,
   with the same unit equation at every derived object `X`, and
   `β = c.hom.app F[0]`. Uniqueness quantifies over all natural transformations
   `c' : B → A`, requiring only the unit equation and concluding `c' = c.hom`.
   It does not require c' invertible or assume K-flat representatives for X.

### Dependency declarations and search findings

- `Sheaf.CategoryTheory.DerivedColimitBar`: read the entire signatures and docs of
  `CategoryColimitBarSystem`, `CategoryColimitBarModel`, their `models`, `bar`,
  `coordinates`, `generator`, `model`, `model_eq`, `adjunction`, `transpose`,
  `colimitAugmentation`, `map`, `formula`, `scalarIso`, `scalarFormula`, and
  `scalarCanonical`, plus `categoryColimitBarSystem_exists`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: read
  `ModuleCat.OrdinaryDerivedChangeOfRings`, `nonempty_ordinaryDerivedChangeOfRings`,
  `ordinaryDerivedChangeOfRings`, and `ordinaryDerivedExtendScalars`, and the
  generic cochain model exposed by its public import. The universal-pair signature
  is used directly rather than a choice of a second scalar-extension construction.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` is the recorded general ringed-site notion;
  the ordinary presheaf presentation uses the actual sectionwise
  `ModuleCat.restrictScalars` under `Functor.whiskeringRight`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  read the full `SheafOfModules.sheafRingDerivedCoefficientAdjunction` signature,
  representative unit/transpose/counit formulas and proof docstring. The two
  returned normalized Hom formulas are its identity-cover and point presentations.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and the publicly exposed
  `CategoryTheory.MorphismProperty.kFlat`. Read both definitions and the
  independent-coefficient resolution interface. The acyclic-total-tensor expression
  for presheaves specializes the definition without replacing the tensor functor.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`,
  `comp_unit_app`, `comp_homEquiv`, and `Adjunction.id`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `unit_conjugateEquiv_symm`;
  read its signature and `conjugateIsoEquiv`, which supply the unit characterization
  and invertibility of the common-right-adjoint comparison.
- Additional exact APIs: `ModuleCat.extendRestrictScalarsAdj`,
  `extendRestrictScalarsAdj_unit_app_apply`,
  `HomologicalComplex.singleMapHomologicalComplex`,
  `Functor.mapDerivedCategoryCompIso`,
  `CategoryTheory.Monoidal.functorCategoryMonoidalPreadditive`.

Searches actually run using `msearch.py Q63 lem-trf-bar-scalar-unit-transpose`:

- LeanFinder: "bar complex scalar extension tensor direct sum derived colimit
  adjunction unit transpose". Eight hits: coefficient unit and Hom formulas,
  group-homology bar constructions; no exact category-bar scalar/unit theorem.
- Loogle: "ModuleCat.extendRestrictScalarsAdj, CategoryTheory.Adjunction.leftDerived".
  Zero hits; the second identifier is unknown. This is not recorded as absence of
  the first identifier; its source was located and read independently.
- Grep: "barScalar|scalar.*[Bb]ar|[Bb]ar.*scalar|extendRestrictScalarsAdj"
  restricted to `Algebra/Category/ModuleCat`. Eleven hits, all on ordinary
  extension/restriction adjunctions, none an exact match for this item.
- LeanSearch: "category bar complex tensor extension of scalars isomorphism
  derived colimit unit". Eight hits, including the ordinary coefficient unit,
  colimit extension facts, tensor-unit complex and `lanCompColimIso`; no exact match.
- Local rg searches of `lean/WeilConjectures` and `lean/Sheaf` for bar/scalar/tensor
  names found `Sheaf.CategoryTheory.DerivedColimitChangeRings` and unrelated bar
  comparisons. The parent gives a comparison structure and a similar proof plan,
  not this theorem with its full finite-sum inverse and transpose/unit clauses.
  It is downstream, so importing it here would close a dependency cycle.
  Its `CategoryBarDerivedExtension` and `categoryBarExtend`/`categoryBarRestrict`
  are NOT duplicated: this module uses the existing functor and universal-pair APIs
  inline, with no new definitions. Exact name/id searches of both Lean roots and
  `grep -rn lem-trf-bar-scalar-unit-transpose lean/WeilConjectures` found no binding.

### Edge cases and validation

Checked before finalizing the statement: E empty (all bar terms zero, no nonempty
assumption); the one-object identity category (the usual coefficient extension);
F zero; S zero; R and S zero; φ the identity; and the nonflat map Z → Z/2 with
flat F. No condition erroneously assumes a flat ring map, finite strings in total,
or a finite indexing category. At n=0 the coefficient unit and colimit generator
have the required tensor normalization. The empty finite sum maps to zero.
Positive cochain degrees are included in the chain isomorphism, not discarded.

Only the `lean` field of the node copy changes. There are no new nodes,
dependency repairs, statement corrections, or disputed mathematical statements.
The theorem uses a single `sorry`, as required in stage 2. Every compiler invocation
uses `scompile.py`; the complete module compiled cleanly in both sandbox and
library module mode. The required delivery dry run and push are run after this report.

## Second reading by Q63

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
