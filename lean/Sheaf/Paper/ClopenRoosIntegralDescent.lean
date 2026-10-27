/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.Paper.ClopenIntegralRestriction
public import Sheaf.Paper.FiniteClopenDerivedDecomposition
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.CategoryTheory.StrictRoosModel
import all Sheaf.Paper.ClopenIntegralRestriction
import all Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosEquivalence
import all Sheaf.Paper.AugmentedIntegralDescent
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-! # Strict Roos comparison and integral descent on a finite clopen partition

Source: Stacks Project, Tags 08TC and 07KC, definition-derived-limit and lemma-products;
Bhatt--Scholze, Definitions 3.4.10 and 3.5.2; blueprint section-invariant argument
(blueprint: lem-pur-clopen-roos-integral-descent).

The restriction below is ordinary exact restriction of completed-ring modules.
It does not complete an arbitrary unbounded complex after restricting it.

## Main statements

* `finiteClopen_strict_tower_equivalence`: strict restriction and product gluing.
* `finiteClopen_strict_roos_comparison`: the normalized signed Roos comparison.
* `finiteClopen_derived_roos_descent`: descent of specified derived-limit triangles.
* `finiteClopen_augmented_reduction`: descent of the actual augmented reduction tower.
* `finiteClopen_integral_membership`: completeness and uniform integral bounds.
* `finiteClopen_integral_subcategories`: the two full-subcategory equivalences.
* `finiteClopen_completed_tensor_unit`: completed tensor and its unit.
* `finiteClopen_integral_scalar_extension`: the actual scalar-extension towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures
namespace PurityFiniteSetting

private theorem clopenIntegralRestriction_countable
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :
    PreservesLimitsOfShape (Discrete ℕ) (clopenIntegralModuleRestriction l E j) := by
  let c := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (asIso (clopenCompletionMap l E j))
  have : (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence :=
    restriction_isEquivalence c
  have : PreservesLimitsOfShape (Discrete ℕ)
      (clopenRestriction j (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)) :=
    Scheme.ProEt.ClopenRoos.pushforward_countable_limits (𝟙 _)
  change PreservesLimitsOfShape (Discrete ℕ)
    (clopenRestriction j (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) ⋙
      SheafOfModules.restrictScalars c.hom)
  infer_instance

private theorem fullSubcategoryPiEquivalence
    {C : Type*} [Category C] {J : Type*} {B : J → Type*} [∀ i, Category (B i)]
    (e : C ≌ ∀ i, B i) (A : ObjectProperty C) (D : ∀ i, ObjectProperty (B i))
    [∀ i, (D i).IsClosedUnderIsomorphisms]
    (h : ∀ K, A K ↔ ∀ i, D i (e.functor.obj K i)) :
    ∃ E : A.FullSubcategory ≌ ∀ i, (D i).FullSubcategory,
      ∀ i, Nonempty (E.functor ⋙ Pi.eval (fun i ↦ (D i).FullSubcategory) i ⋙
        (D i).ι ≅ A.ι ⋙ e.functor ⋙ Pi.eval B i) := by
  let F : A.FullSubcategory ⥤ ∀ i, (D i).FullSubcategory :=
    { obj K i := ⟨e.functor.obj K.obj i, (h K.obj).mp K.property i⟩
      map f i := ObjectProperty.homMk (e.functor.map f.hom i)
      map_id K := by
        funext i
        apply ObjectProperty.hom_ext
        exact congrFun (e.functor.map_id K.obj) i
      map_comp f g := by
        funext i
        apply ObjectProperty.hom_ext
        exact congrFun (e.functor.map_comp f.hom g.hom) i }
  let G : (∀ i, (D i).FullSubcategory) ⥤ A.FullSubcategory :=
    { obj K := ⟨e.inverse.obj (fun i ↦ (K i).obj), (h _).mpr (fun i ↦
        (D i).prop_of_iso (Pi.isoApp (e.counitIso.app (fun i ↦ (K i).obj)) i).symm
          (K i).property)⟩
      map f := ObjectProperty.homMk (e.inverse.map (fun i ↦ (f i).hom))
      map_id K := by
        apply ObjectProperty.hom_ext
        exact e.inverse.map_id (fun i ↦ (K i).obj)
      map_comp f g := by
        apply ObjectProperty.hom_ext
        exact e.inverse.map_comp (fun i ↦ (f i).hom) (fun i ↦ (g i).hom) }
  let η : 𝟭 _ ≅ F ⋙ G := NatIso.ofComponents
    (fun K ↦ A.isoMk (e.unitIso.app K.obj)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact e.unitIso.hom.naturality f.hom)
  let ε : G ⋙ F ≅ 𝟭 _ := NatIso.ofComponents
    (fun K ↦ Pi.isoMk (fun i ↦ (D i).isoMk
      (Pi.isoApp (e.counitIso.app (fun i ↦ (K i).obj)) i))) (by
      intro K L f
      funext i
      apply ObjectProperty.hom_ext
      exact congrFun (e.counitIso.hom.naturality (fun i ↦ (f i).hom)) i)
  exact ⟨CategoryTheory.Equivalence.mk F G η ε, fun i ↦ ⟨Iso.refl _⟩⟩

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted clopenCompletionMap
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

variable (P : PurityFiniteSetting.{u})
  (X : Over (Spec (CommRingCat.of P.field.k)))
  [hft : LocallyOfFiniteType X.hom] [hqc : QuasiCompact X.hom]
  {I : Type w} [hfinite : Finite I]
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i).left] [hclosed : ∀ i, IsClosedImmersion (j i).left]
  (hdisjoint : ∀ i i', i ≠ i' → Disjoint (Set.range (j i).left) (Set.range (j i').left))
  (hcover : (⋃ i, Set.range (j i).left) = Set.univ)

include hft hqc hfinite hclosed hdisjoint hcover

/-- Restriction and sectionwise product gluing are inverse on strict towers.
Source: Stacks 04TS, 08TC (blueprint: lem-pur-clopen-roos-integral-descent).
Proof: step 1 uses the additive exact module equivalence of
lem-pur-clopen-ringed-module-gluing in every degree and level. Glue transitions
and chain maps by that functor. Faithfulness checks all commuting squares.
The unit and counit are natural, so lift to strict towers. On a test object the
inverse is the product of sections on the component pullbacks; every structural
map and module action is coordinatewise. The empty product is the zero sheaf. -/
theorem finiteClopen_strict_tower_equivalence :
    ∃ e : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource P.coefficients.l P.extension X.left) ℤ ≌
        (∀ i, CochainComplex (ℕᵒᵖ ⥤
          scalarReductionSource P.coefficients.l P.extension (Xi i).left) ℤ),
      e.functor = Functor.pi' (fun i ↦
        clopenIntegralStrictRestriction P.coefficients.l P.extension (j i).left) ∧
      ∃ φ : ∀ (F : ∀ i, CochainComplex (ℕᵒᵖ ⥤
          scalarReductionSource P.coefficients.l P.extension (Xi i).left) ℤ)
          (p : ℤ) (n : ℕᵒᵖ) (V : X.left.ProEt),
        (((e.inverse.obj F).X p).obj n).val.obj (op V) ≃+
          (∀ i, (((F i).X p).obj n).val.obj
            (op ((Scheme.proEtaleBaseChange (j i).left).obj V))),
        (∀ F p n V
            (a : (completedIntegralCommRingSheafUnrestricted P.coefficients.l
              P.extension X.left).obj.obj (op V))
            (x : (((e.inverse.obj F).X p).obj n).val.obj (op V)) (i : I),
          φ F p n V (a • x) i =
            ((inv (clopenCompletionMap P.coefficients.l P.extension (j i).left)).hom.app
              (op ((Scheme.proEtaleBaseChange (j i).left).obj V))
              ((completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension
                X.left).obj.map
                (MorphismProperty.Over.homMk
                  (A := (clopenSiteInclusion (j i).left).obj
                    ((Scheme.proEtaleBaseChange (j i).left).obj V)) (B := V)
                  (pullback.fst V.hom (j i).left) pullback.condition).op a)) •
                φ F p n V x i) ∧
        (∀ F p n (V W : X.left.ProEt) (f : V ⟶ W)
            (x : (((e.inverse.obj F).X p).obj n).val.obj (op W)),
          φ F p n V ((((e.inverse.obj F).X p).obj n).val.map f.op x) =
            fun i ↦ (((F i).X p).obj n).val.map
              ((Scheme.proEtaleBaseChange (j i).left).map f).op (φ F p n W x i)) ∧
        (∀ F p n m (f : n ⟶ m) V x,
          φ F p m V ((((e.inverse.obj F).X p).map f).val.app (op V) x) =
            fun i ↦ (((F i).X p).map f).val.app
              (op ((Scheme.proEtaleBaseChange (j i).left).obj V)) (φ F p n V x i)) ∧
        (∀ F p q n V x,
          φ F q n V ((((e.inverse.obj F).d p q).app n).val.app (op V) x) =
            fun i ↦ (((F i).d p q).app n).val.app
              (op ((Scheme.proEtaleBaseChange (j i).left).obj V)) (φ F p n V x i)) ∧
        (∀ F G (a : F ⟶ G) p n V x,
          φ G p n V ((((e.inverse.map a).f p).app n).val.app (op V) x) =
            fun i ↦ (((a i).f p).app n).val.app
              (op ((Scheme.proEtaleBaseChange (j i).left).obj V)) (φ F p n V x i)) := by
  sorry

/-- Termwise products, one minus shift, the signed cone, strict maps and projections
are identified by the same comparison.
Source: Stacks 08TC/07KC (blueprint: lem-pur-clopen-roos-integral-descent).
Proof: steps 2--3. Countable products are sectionwise by
lem-weil-proetale-countable-products-exact. Reindex the two products by (i,n).
Projection n of the conjugated endomorphism is pr_n minus t_n after pr_(n+1).
In the shifted-cone coordinates apply this product comparison to both summands;
the differential (-dy-vx,dx) then commutes. Its inverse uses the inverse product
comparison. Strict maps are diagonal product maps, so naturality follows on both
coordinates. The second cone projection followed by pr_n gives the last equation. -/
theorem finiteClopen_strict_roos_comparison (i : I) :
    ∃ θ : roosF ⋙
        (clopenIntegralModuleRestriction P.coefficients.l P.extension
          (j i).left).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      clopenIntegralStrictRestriction P.coefficients.l P.extension (j i).left ⋙ roosF,
      ∀ T : CochainComplex (ℕᵒᵖ ⥤
          scalarReductionSource P.coefficients.l P.extension X.left) ℤ,
        IsIso (piComparison
          (clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left)
          (fun n : ℕ ↦ T.asFunctor.obj (op n))) ∧
        (clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).map (roosU T) ≫
            piComparison
              (clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left)
              (fun n : ℕ ↦ T.asFunctor.obj (op n)) =
          piComparison
              (clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left)
              (fun n : ℕ ↦ T.asFunctor.obj (op n)) ≫
            roosU ((clopenIntegralStrictRestriction P.coefficients.l P.extension
              (j i).left).obj T) ∧
        (∀ p : ℤ,
          (θ.hom.app T).f (p + 1) ≫
              (roosχ ((clopenIntegralStrictRestriction P.coefficients.l P.extension
                (j i).left).obj T) p).hom =
            (clopenIntegralModuleRestriction P.coefficients.l P.extension (j i).left).map
                (roosχ T p).hom ≫
              Functor.biprodComparison
                (clopenIntegralModuleRestriction P.coefficients.l P.extension (j i).left)
                ((roosP T).X p) ((roosP T).X (p + 1)) ≫
              biprod.map
                ((piComparison
                  (clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left)
                  (fun n : ℕ ↦ T.asFunctor.obj (op n))).f p)
                ((piComparison
                  (clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left)
                  (fun n : ℕ ↦ T.asFunctor.obj (op n))).f (p + 1))) ∧
        (∀ n : ℕ,
          (clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).map
              (roosEval T n) =
            θ.hom.app T ≫ roosEval
              ((clopenIntegralStrictRestriction P.coefficients.l P.extension (j i).left).obj T)
              n) := by
  have := clopenIntegralRestriction_countable P.coefficients.l P.extension (j i).left
  let F := clopenIntegralModuleRestriction P.coefficients.l P.extension (j i).left
  have : PreservesLimitsOfShape (Discrete ℕ) (F.mapHomologicalComplex (.up ℤ)) := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro p
    change PreservesLimitsOfShape (Discrete ℕ)
      (HomologicalComplex.eval _ (.up ℤ) p ⋙ F)
    infer_instance
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    refine ⟨Scheme.ProEt.ClopenRoos.comparison_iso F, ?_⟩
  intro T
  refine ⟨?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact Scheme.ProEt.ClopenRoos.comparison_transition_generic F T
  · exact Scheme.ProEt.ClopenRoos.comparison_iso_coordinates F T
  · exact Scheme.ProEt.ClopenRoos.comparison_iso_evaluation F T

/-- Unbounded restriction is an equivalence and transports the specified Roos triangle.
Source: Stacks 08TC/07KC (blueprint: lem-pur-clopen-roos-integral-descent).
Proof: step 4. The exact module equivalence descends through quasi-isomorphisms.
Exact countable products compute derived products (lem-weil-derived-limit-products-core).
The projection comparison carries 1-s to the component 1-s by additivity. Apply
restriction to the distinguished triangle, using its shift comparison for the last
arrow. Conversely componentwise distinguished triangles are distinguished in the
product, and the inverse triangulated equivalence reflects them. The first map
remains the image of c followed by the projection-normalized product comparison. -/
theorem finiteClopen_derived_roos_descent :
    Nonempty (HasCountableProducts
      (DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left))) ∧
    (∀ i, Nonempty (HasCountableProducts
      (DerivedCategory (scalarReductionSource P.coefficients.l P.extension (Xi i).left)))) ∧
    (Functor.pi' (fun i ↦
      clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left)).IsEquivalence ∧
    ∀ (K : ℕ → DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left))
      [HasProduct K]
      [∀ i, HasProduct (fun n ↦ (clopenIntegralDerivedRestriction P.coefficients.l
        P.extension (j i).left).obj (K n))],
      ∃ φ : ∀ i, (clopenIntegralDerivedRestriction P.coefficients.l P.extension
          (j i).left).obj (∏ᶜ K) ≅
        ∏ᶜ (fun n ↦ (clopenIntegralDerivedRestriction P.coefficients.l P.extension
          (j i).left).obj (K n)),
        (∀ i, (φ i).hom = piComparison
          (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left) K) ∧
        ∀ (t : ∀ n, K (n + 1) ⟶ K n)
          (M : DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left))
          (c : M ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ M⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle t M c δ ↔ ∀ i,
            IsDerivedLimitTriangle
              (fun n ↦ (clopenIntegralDerivedRestriction P.coefficients.l P.extension
                (j i).left).map (t n))
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj M)
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).map c ≫
                (φ i).hom)
              ((φ i).inv ≫
                (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).map δ ≫
                ((clopenIntegralDerivedRestriction P.coefficients.l P.extension
                  (j i).left).commShiftIso (1 : ℤ)).hom.app M) := by
  exact integralRoosCalculus P X Xi j hdisjoint hcover

/-- The actual reduction units and transitions restrict, rather than only the objects.
Source: Bhatt--Scholze 3.5.2 and Stacks 06YY
(blueprint: lem-pur-clopen-roos-integral-descent).
Proof: step 5. Restrict a K-flat resolution q:P→K; the componentwise tensor
calculus preserves K-flatness. On generators the comparison is s tensor x mapped
to the same restricted s tensor x. It sends x mapped to 1 tensor x to the same
unit, and reduction of s to reduction of its restriction, since the coefficient
comparison preserves quotient projections and transitions. Invert [q] to obtain
the claimed equation for c_n. Naturality is the same calculation on strict maps,
then on roofs. Thus the displayed isomorphism includes all transition equations. -/
theorem finiteClopen_augmented_reduction (i : I) :
    ∃ β : clopenDerivedReductionFunctor P.coefficients.l P.extension X.left ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left) ≅
      clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left ⋙
        clopenDerivedReductionFunctor P.coefficients.l P.extension (Xi i).left,
      ∀ K (n : ℕ),
        (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).map
            ((sfDerivedReductionUnit P.coefficients.l P.extension X.left n).app K) ≫
          (β.hom.app K).app (op n) =
            (sfDerivedReductionUnit P.coefficients.l P.extension (Xi i).left n).app
              ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)
    := by
  exact (augmentedIntegralReductionComparison P X Xi j hdisjoint hcover i).2.1

/-- On chosen resolutions the same comparison preserves the recorded c_n=[q]⁻¹γ_n.
Source: Bhatt--Scholze 3.5.2; Stacks 06YY
(blueprint: lem-pur-clopen-roos-integral-descent).
Proof: step 5 and lem-pur-finite-product-derived-tensor-calculus show that exact
restriction preserves the K-flat resolution. The quotient coefficient comparisons
send γ_n and τ_n to their component formulas. Localization sends the inverse of
[q] to the inverse of its restricted image, through mapDerivedCategoryFactors.
Thus the triangle of augmentation maps commutes at every positive level. -/
theorem finiteClopen_resolution_reduction (i : I)
    {T K : CochainComplex (scalarReductionSource.{u, u} P.coefficients.l P.extension X.left) ℤ}
    (q : T ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X.left)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u}
        P.coefficients.l P.extension X.left) q) :
    ∃ hqr : CochainComplex.IsKFlatResolutionIndependentCoefficients.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology (Xi i).left)
        (R := completedIntegralCommRingSheafUnrestricted.{u, u}
          P.coefficients.l P.extension (Xi i).left)
        ((clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).map q),
      ∃ β : canonicalIntegralReductionTower.{u, u} P.coefficients.l P.extension X.left T ⋙
          clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left ≅
        canonicalIntegralReductionTower.{u, u} P.coefficients.l P.extension (Xi i).left
          ((clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).obj T),
        ∀ n : ℕ,
          (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).map
              (canonicalIntegralReductionTowerMap.{u, u}
                P.coefficients.l P.extension X.left (P := T) (K := K) q hq n) ≫
            β.hom.app (op n) =
          (Functor.mapDerivedCategoryFactors
            (clopenIntegralModuleRestriction P.coefficients.l P.extension (j i).left)).hom.app K ≫
            canonicalIntegralReductionTowerMap.{u, u} P.coefficients.l P.extension (Xi i).left
              (P :=
                (clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).obj T)
              (K :=
                (clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).obj K)
              ((clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).map q)
              hqr n := by
  sorry

/-- Completeness and both integral constructibility predicates are detected componentwise.
Source: Bhatt--Scholze 3.5.2; Stacks 08TC
(blueprint: lem-pur-clopen-roos-integral-descent).
Proof: steps 6--7. The augmented reduction comparison keeps the canonical first
map c into the product. Restrict a witnessing triangle to prove the forward
completeness implication. Conversely lift the tuple of connecting maps by the
full faithful derived equivalence; it reflects distinguished triangles while
keeping c and 1-s fixed. Apply lem-pur-clopen-finite-constructibility-bounds to
each positive reduction. Constructibility is local on the finite clopen cover.
Choose a common interval containing the finitely many component intervals;
this works simultaneously at every positive level. The identical argument with
Tor tests, including zero insertions, gives the finite-Tor assertion. For an
empty partition the category is zero, and [0,0] supplies the existential bounds. -/
theorem finiteClopen_integral_membership
    (K : DerivedCategory (scalarReductionSource P.coefficients.l P.extension X.left)) :
    (IntegralOnSlice.IsComplete P.coefficients.l P.extension X.left none K ↔
      ∀ i, IntegralOnSlice.IsComplete P.coefficients.l P.extension (Xi i).left none
        ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ∧
    (sfIntegralConstructible P.coefficients.l P.extension X.left K ↔
      ∀ i, sfIntegralConstructible P.coefficients.l P.extension (Xi i).left
        ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ∧
    (finiteTorConstructibleIntegral P.coefficients.l P.extension X.left K ↔
      ∀ i, finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left
        ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) ⊆
            Set.Icc a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K)) ⊆
              Set.Icc a b)) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj K) a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj K))
          a b)) := by
  have h := augmentedIntegralMembershipBounds P X Xi j hdisjoint hcover K
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- Both full-subcategory equivalences are restrictions of ordinary unbounded restriction.
Source: Stacks 04TS; Bhatt--Scholze 3.5.2
(blueprint: lem-pur-clopen-roos-integral-descent).
Proof: step 7. Restrict the unbounded equivalence using both directions of the
membership equivalences. Its inverse glues the component objects; the common
finite cohomological and Tor intervals prove membership of the glued object.
Fullness and faithfulness are inherited by full subcategories. This construction
also works for the empty family, whose product is a zero category. -/
theorem finiteClopen_integral_subcategories :
    (∃ e : sfIntegralConstructibleCategory P.coefficients.l P.extension X.left ≌
        (∀ i, sfIntegralConstructibleCategory P.coefficients.l P.extension (Xi i).left),
      ∀ i, Nonempty (e.functor ⋙
          (CategoryTheory.Pi.eval
            (fun i ↦ sfIntegralConstructibleCategory P.coefficients.l P.extension (Xi i).left) i) ⋙
          (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι ≅
        (sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
          clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left)) ∧
    (∃ e : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension X.left ≌
        (∀ i, finiteTorConstructibleIntegralCategory P.coefficients.l P.extension (Xi i).left),
      ∀ i, Nonempty (e.functor ⋙
          (CategoryTheory.Pi.eval
            (fun i ↦ finiteTorConstructibleIntegralCategory P.coefficients.l P.extension
              (Xi i).left) i) ⋙
          (finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left).ι ≅
        (finiteTorConstructibleIntegral P.coefficients.l P.extension X.left).ι ⋙
          clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left)) := by
  let r := fun i ↦ clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left
  have : (Functor.pi' r).IsEquivalence :=
    (finiteClopen_derived_roos_descent P X Xi j hdisjoint hcover).2.2.1
  let e := (Functor.pi' r).asEquivalence
  have hmem := finiteClopen_integral_membership P X Xi j hdisjoint hcover
  have hctf (Y : Scheme.{u}) :
      (finiteTorConstructibleIntegral P.coefficients.l P.extension Y).IsClosedUnderIsomorphisms :=
    by
    constructor
    intro K L α hK
    refine ⟨ObjectProperty.prop_of_iso _ α hK.1, ?_⟩
    obtain ⟨a, b, hab, h⟩ := hK.2
    refine ⟨a, b, hab, fun n ↦ ?_⟩
    refine ⟨(h n).1, ?_⟩
    intro T Q hT f hf hQ M q hq
    obtain ⟨γ⟩ := hT
    exact (h n).2 T Q
      ⟨γ ≪≫ (scalarReductionDerivedExtension P.coefficients.l P.extension Y n).mapIso α.symm⟩
      f hf hQ M q hq
  have (i : I) := hctf (Xi i).left
  exact ⟨fullSubcategoryPiEquivalence e _ _ (fun K ↦ (hmem K).2.1),
    fullSubcategoryPiEquivalence e _ _ (fun K ↦ (hmem K).2.2.1)⟩

/-- Completed tensor and its coefficient unit are preserved by ordinary restriction.
Source: Bhatt--Scholze 3.4.10; Stacks 08TC
(blueprint: lem-pur-clopen-roos-integral-descent).
Proof: step 8. Restrict K-flat flat-term representatives of both inputs.
The componentwise derived tensor comparison identifies every finite tensor
level, and its pure-tensor formula commutes with the quotient transitions.
This is an isomorphism of strict towers, so the signed Roos comparison gives
the completed tensor isomorphism. The normalized representative descents make
it natural on derived morphisms. The completed regular module and its section
1 restrict to the corresponding regular module, as do all its quotient units.
No completeness hypothesis on the inputs is needed for this strict computation. -/
theorem finiteClopen_completed_tensor_unit (i : I) :
    Nonempty (IntegralOnSlice.completedTensor P.coefficients.l P.extension X.left none ⋙
        clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left ≅
      ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).prod
        (clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left)) ⋙
        IntegralOnSlice.completedTensor P.coefficients.l P.extension (Xi i).left none) ∧
    Nonempty ((clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left).obj
        (integralConstantCoefficientObject P.coefficients.l P.extension X.left) ≅
      integralConstantCoefficientObject P.coefficients.l P.extension (Xi i).left) := by
  sorry

/-- The strict reduction and completed-tensor comparisons use the same tensor generators.
Source: Stacks 06YY, 08TC; Bhatt--Scholze 3.4.10
(blueprint: lem-pur-clopen-roos-integral-descent).
Proof: steps 5 and 8. Coefficient transport preserves the finite quotient and
its projection from the completed ring. On each sheafified generator s tensor x
there is therefore the displayed restriction map; it is balanced and locally
generates, hence uniquely determines the comparison. It commutes with quotient
transitions. On total tensor summands send x tensor y to the tensor of their two
restricted images. This preserves the signed total differential, strict maps
and transitions, so gives the second natural strict tower isomorphism. Apply the
Roos comparison to this very tower to compute the completed-tensor comparison. -/
theorem finiteClopen_strict_tensor_reductions (i : I) :
    ∃ (γ : clopenStrictReductionFunctor P.coefficients.l P.extension X.left ⋙
          clopenIntegralComplexTowers P.coefficients.l P.extension (j i).left ≅
        clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left ⋙
          clopenStrictReductionFunctor P.coefficients.l P.extension (Xi i).left)
      (β : integralOperationsTensorTowerFunctor P.coefficients.l P.extension X.left ⋙
          clopenIntegralComplexTowers P.coefficients.l P.extension (j i).left ≅
        ((clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).prod
          (clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left)) ⋙
          integralOperationsTensorTowerFunctor P.coefficients.l P.extension (Xi i).left),
      (∀ (T : CochainComplex (scalarReductionSource P.coefficients.l P.extension X.left) ℤ)
        (n : ℕ) (p : ℤ) (U : (Xi i).left.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf P.coefficients.l P.extension
          (Xi i).left n).obj.obj U)
        (x : (T.X p).val.obj ((clopenSiteInclusion (j i).left).op.obj U)),
        ((((γ.hom.app T).app (op n)).f p).val.app U)
          (unrestrictedIntegralTensorSection P.coefficients.l P.extension X.left n
            (T.X p) ((clopenSiteInclusion (j i).left).op.obj U)
            ((clopenConstantMap (j i).left (CommRingCat.of
              (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l P.extension
                (n + 1))))).hom.app U s) x) =
          unrestrictedIntegralTensorSection P.coefficients.l P.extension (Xi i).left n
            ((clopenIntegralModuleRestriction P.coefficients.l P.extension (j i).left).obj (T.X p))
            U s x) ∧
      (∀ (T Q : CochainComplex (scalarReductionSource P.coefficients.l P.extension X.left) ℤ)
        (n : ℕ) (p q : ℤ) (U : (Xi i).left.ProEtᵒᵖ)
        (x : (((unrestrictedIntegralFiniteComplex P.coefficients.l P.extension X.left n).obj
          T).X p).val.obj ((clopenSiteInclusion (j i).left).op.obj U))
        (y : (((unrestrictedIntegralFiniteComplex P.coefficients.l P.extension X.left n).obj
          Q).X q).val.obj ((clopenSiteInclusion (j i).left).op.obj U)),
        ((((β.hom.app (T, Q)).app (op n)).f (p + q)).val.app U)
          (integralOperationsTotalTensorSection P.coefficients.l P.extension X.left n T Q
            p q ((clopenSiteInclusion (j i).left).op.obj U) x y) =
          integralOperationsTotalTensorSection P.coefficients.l P.extension (Xi i).left n
            ((clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).obj T)
            ((clopenIntegralComplexRestriction P.coefficients.l P.extension (j i).left).obj Q)
            p q U
            (((((γ.hom.app T).app (op n)).f p).val.app U) x)
            (((((γ.hom.app Q).app (op n)).f q).val.app U) y)) := by
  sorry

/-- Scalar extension commutes with restriction through an isomorphism of its actual
strict finite-level towers, normalized on every sheafified tensor generator.
Source: Bhatt--Scholze 3.4.10; Stacks 08TC
(blueprint: lem-pur-clopen-roos-integral-descent).
Proof: step 9. The normalized coefficient identifications commute with the
quotient inclusion E into L and the projections from the completed rings.
The termwise change-of-rings comparison therefore sends s tensor x to the
restricted s tensor x. It commutes with the differential, strict maps and the
transition s tensor x mapped to red(s) tensor x. Taking s=1 gives the actual
level maps. Apply the strict Roos comparison over L, then descend along the
K-flat localization with its specified comparison. The result is natural on
all derived morphisms. Ramification does not change this computation. -/
theorem finiteClopen_integral_scalar_extension (i : I)
    (L : Type u) [Field L] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L) :
    Nonempty (integralScalarExtensionOfUniverses P.coefficients.l P.extension L ι X.left ⋙
        clopenIntegralDerivedRestriction P.coefficients.l L (j i).left ≅
      clopenIntegralDerivedRestriction P.coefficients.l P.extension (j i).left ⋙
        integralScalarExtensionOfUniverses P.coefficients.l P.extension L ι (Xi i).left) ∧
    ∃ β : integralScalarTowerFunctor P.coefficients.l P.extension L ι X.left ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((clopenIntegralModuleRestriction P.coefficients.l L (j i).left).mapHomologicalComplex
            (ComplexShape.up ℤ)) ≅
      (clopenIntegralModuleRestriction P.coefficients.l P.extension
          (j i).left).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        integralScalarTowerFunctor P.coefficients.l P.extension L ι (Xi i).left,
      ∀ (T : CochainComplex (scalarReductionSource P.coefficients.l P.extension X.left) ℤ)
        (n : ℕ) (p : ℤ) (U : (Xi i).left.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf P.coefficients.l L (Xi i).left n).obj.obj U)
        (x : (T.X p).val.obj ((clopenSiteInclusion (j i).left).op.obj U)),
        ((((β.hom.app T).app (op n)).f p).val.app U)
          (integralScalarTensorSection P.coefficients.l P.extension L ι X.left n
            (T.X p) ((clopenSiteInclusion (j i).left).op.obj U)
            ((clopenConstantMap (j i).left (CommRingCat.of
              (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l L
                (n + 1))))).hom.app U s) x) =
          integralScalarTensorSection P.coefficients.l P.extension L ι (Xi i).left n
            ((clopenIntegralModuleRestriction P.coefficients.l P.extension (j i).left).obj (T.X p))
            U s x := by
  sorry

end PurityFiniteSetting
end WeilConjectures
