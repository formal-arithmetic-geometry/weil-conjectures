/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.Paper.ProperHeartBoundTorsion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import all Sheaf.Paper.CoefficientHeartLisseExtensionConstructible
import all Sheaf.Paper.QcqsIntegralFiniteModelCompleteness
import Sheaf.Paper.PrincipalReductionConeCalculus
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsProperties
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The integral lattice bound for proper morphisms

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-proper-heart-bound,
`sk-lem-proper-heart-bound-lattice.md` and its proof
(blueprint: det-proper-heart-bound-lattice).

The coefficient ring is the pulled-back continuous condensed valuation ring, and the
extension by zero is the already recorded composite of open extension and closed direct image.
Cohomology is taken on the underlying abelian sheaf, after canonical pro-etale inverse image
along the projection from the fibre product. This is restriction to the slice site.
The integer fibre bound retains the empty-fibre case when the bound is negative.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem exact_derived_preserves_products
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{v} A] [HasDerivedCategory.{w} B]
    [HasCountableProducts A] [CountableAB4Star A]
    [HasCountableProducts B] [CountableAB4Star B]
    [HasCountableProducts (DerivedCategory A)]
    [HasCountableProducts (DerivedCategory B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F] :
    PreservesLimitsOfShape (Discrete ℕ) F.mapDerivedCategory := by
  classical
  have hQA := (derivedCategory_countableProducts_properties A).1
  have hQB := (derivedCategory_countableProducts_properties B).1
  have hQB' (C : ℕ → CochainComplex B ℤ) :
      PreservesLimit (Discrete.functor C) (DerivedCategory.Q (C := B)) :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) (hQB ℕ C).some
  let := hQB'
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := B)) :=
    preservesLimitsOfShape_of_discrete _
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  have h (K : ℕ → DerivedCategory A) :
      PreservesLimit (Discrete.functor K) F.mapDerivedCategory := by
    let C := fun n ↦ DerivedCategory.Q.objPreimage (K n)
    let e : Discrete.functor C ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
      Discrete.natIso (fun n ↦ DerivedCategory.Q.objObjPreimageIso (K n.as))
    have : PreservesLimit (Discrete.functor C ⋙ DerivedCategory.Q)
        F.mapDerivedCategory :=
      preservesLimit_of_preserves_limit_cone (hQA ℕ C).some
        (isLimitOfPreserves (DerivedCategory.Q ⋙ F.mapDerivedCategory) (limit.isLimit _))
    exact preservesLimit_of_iso_diagram F.mapDerivedCategory e
  let := h
  exact preservesLimitsOfShape_of_discrete _

private theorem roos_of_iso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : ℕ → DerivedCategory A) [HasProduct K]
    (t : ∀ n, K (n + 1) ⟶ K n) {M N : DerivedCategory A}
    (hM : IsDerivedLimit t M) (e : M ≅ N) : IsDerivedLimit t N := by
  obtain ⟨p, δ, hT⟩ := hM
  refine ⟨e.inv ≫ p, δ ≫ (shiftFunctor _ (1 : ℤ)).map e.hom, ?_⟩
  exact CategoryTheory.Pretriangulated.isomorphic_distinguished _ hT _
    (CategoryTheory.Pretriangulated.Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp))

private theorem homology_product_zero
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : ℕ → DerivedCategory A) [HasProduct K] (i : ℤ)
    [PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor A i)]
    (h : ∀ n, IsZero ((DerivedCategory.homologyFunctor A i).obj (K n))) :
    IsZero ((DerivedCategory.homologyFunctor A i).obj (∏ᶜ K)) := by
  exact (isLimitOfPreserves (DerivedCategory.homologyFunctor A i)
    (limit.isLimit (Discrete.functor K))).isZero_pt
      (Functor.isZero _ (fun n ↦ h n.as))

private theorem lattice_complete
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    {S Sbar X : Scheme.{u}} [IsNoetherian X]
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) [IsClosedImmersion i]
    (L : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) S)
    (hL : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) L) :
    IsDerivedComplete ℓ E X ((DerivedCategory.singleFunctor _ 0).obj
      ((torsionLocallyClosedExtension ℓ E j i).obj L)) := by
  have : TopologicalSpace.NoetherianSpace Sbar := i.isEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace S := j.isEmbedding.isInducing.noetherianSpace
  apply complete_sheaf
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  apply stratified_closedPush
  apply stratified_openExtension
  apply stratified_of_finiteModel
  exact lisse_finiteModel _ _ L hL

private theorem reduction_level_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) (K : DerivedCategory (AdicCompletion.Modules ℓ E X)) (n : ℕ) :
    Nonempty (AdicCompletion.integralLevel ℓ E X K n ≅
      (DerivedNakayama.reductionFunctor ℓ E X (n + 1)).obj K) := by
  obtain ⟨d, hd, D, hobj, χ, t, j, sD, sR, κR, Φ,
    hχ, hmap, ht, hj, hcompat, hqi, hexact, hrest⟩ :=
    PrincipalReduction.principal_reduction_cone_calculus ℓ E X
  obtain ⟨d', hd', r, hr, i, q, hi, hq, hres⟩ :=
    DerivedNakayama.derived_nakayama_resolution ℓ E
  have hdd : d' = d := by
    let := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
    apply Mod.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply AddCommGrpCat.hom_ext
    ext a
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    exact (hd' S a s).trans (hd S a s).symm
  subst d'
  let M := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj M ≅ K := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨ec⟩ := (hres X (n + 1) (by omega)).2.1
  refine ⟨((PrincipalReduction.reductionFunctor ℓ E X n).mapIso e).symm ≪≫
    ((κR n).app M).symm ≪≫ ?_ ≪≫
    (DerivedNakayama.reductionFunctor ℓ E X (n + 1)).mapIso e⟩
  exact eqToIso (congrArg DerivedCategory.Q.obj (hobj n M)) ≪≫ (ec.app M).symm

private theorem map_roos
    {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{v} A]
    [Category* B] [Abelian B] [HasDerivedCategory.{w} B]
    (Φ : DerivedCategory A ⥤ DerivedCategory B) [Φ.Additive] [Φ.CommShift ℤ]
    [Φ.IsTriangulated]
    (K : ℕ → DerivedCategory A) [HasProduct K]
    [HasProduct (fun n ↦ Φ.obj (K n))]
    [PreservesLimit (Discrete.functor K) Φ]
    (t : ∀ n, K (n + 1) ⟶ K n) (M : DerivedCategory A)
    (hM : IsDerivedLimit t M) :
    IsDerivedLimit (K := fun n ↦ Φ.obj (K n))
      (fun n ↦ Φ.map (t n))
      (Φ.obj M) := by
  let e := PreservesProduct.iso Φ K
  obtain ⟨p, δ, hT⟩ := hM
  have he (n : ℕ) : e.hom ≫ Pi.π _ n = Φ.map (Pi.π K n) := by simp [e]
  have ht : Φ.map (towerTransitionEndomorphism t) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n ↦ Φ.map (t n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Pi.lift_π, Functor.map_sub]
    rw [← Category.assoc, he, ← Functor.map_comp]
    rw [← Functor.map_comp, Pi.lift_π, Category.id_comp, Functor.map_comp]
  refine ⟨Φ.map p ≫ e.hom,
    e.inv ≫ Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M, ?_⟩
  exact CategoryTheory.Pretriangulated.isomorphic_distinguished _
    (Φ.map_distinguished _ hT) _
    (CategoryTheory.Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm
      (by change (Φ.map p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ Φ.map p; simp)
      (by
        change towerTransitionEndomorphism (fun n ↦ Φ.map (t n)) ≫ e.inv =
          e.inv ≫ Φ.map (towerTransitionEndomorphism t)
        apply (cancel_mono e.hom).1
        simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Iso.inv_hom_id_assoc] using congrArg (fun z ↦ e.inv ≫ z) ht.symm)
      (by
        change (e.inv ≫ Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M) ≫
          (shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
            e.inv ≫ (Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M)
        simp))

private theorem inverseImage_products {T X : Scheme.{u}} (r : T ⟶ X) [WeaklyEtale r] :
    PreservesLimitsOfShape (Discrete ℕ) (upperStar Ab.{u + 1} r) := by
  let F := localizationRestriction Ab.{u + 1} r inferInstance
  have : PreservesLimitsOfShape (Discrete ℕ) F := by
    dsimp only [F, localizationRestriction]
    infer_instance
  exact preservesLimitsOfShape_of_natIso
    (upperStarIsoLocalizationRestriction Ab.{u + 1} r inferInstance).symm

private theorem sections_products (T : Scheme.{u}) :
    PreservesLimitsOfShape (Discrete ℕ) (rightDerivedGlobalSections Ab.{u + 1} T) := by
  let : HasSheafify (Scheme.ProEt.topology T) Ab.{u + 1} :=
    inferInstance
  let : Abelian.HasKInjectiveResolutions
      (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}
  let G := rightDerivedGlobalSections Ab.{u + 1} T
  let adj : Functor.mapDerivedCategory.{u + 1, u + 1}
      (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ⊣ G :=
    Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (constantSheafΓAdj (Scheme.ProEt.topology T) Ab.{u + 1})
  have : G.IsRightAdjoint := adj.isRightAdjoint
  infer_instance

/-- For an integral lisse finite free lattice on a locally closed finite-type stratum,
cohomology over an affine weakly contractible pro-etale base change vanishes above `2d+1`.
There is no finiteness or Noetherian assumption on that base change.
Source: blueprint main-20261015, sk-lem-proper-heart-bound-lattice, Completeness, Sections
and Milnor paragraphs; Stacks Tags 09BM, 09BP, 0D6K, 07KY and 07KW
(blueprint: det-proper-heart-bound-lattice).

Proof:
1. Finite local models and open/closed extension make the lattice extension constant-model
   constructible on X. The completeness theorem for such sheaves identifies its degree-zero
   complex with the canonical Roos limit of its derived reductions.
2. Forget the coefficient action and restrict the underlying abelian sheaf to X_V. Both
   functors are exact and preserve countable products. Repleteness and the generic derived
   product comparison show that their derived functors preserve countable products as well.
3. Derived global sections preserve products by the derived constant-sheaf adjunction.
   Apply the composite triangulated functor to the Roos triangle. Its product comparison
   respects the transition endomorphism, as checked after each product projection.
4. If d is negative, every ordinary fibre has dimension at most bottom, by invariance of
   dimension under field extension. A point of X would give a nonempty fibre of dimension
   at least zero. Hence X is empty and the underlying abelian sheaf is zero.
5. For nonnegative d, principal cone calculus identifies each canonical integral level
   with the reduction in properHeartBoundTorsion. That theorem identifies it with the
   locally closed extension of the quotient lattice and kills its homology above 2d.
   These comparisons are used separately at each level; no tower compatibility is needed.
6. Homology commutes with countable products in D(Ab). For q > 2d+1, the two product
   vertices of the Roos triangle have zero homology in degrees q-1 and q. The homology
   exact sequence therefore kills H^q of its limit, and the degree-zero comparisons
   identify that group with the cohomology object in the conclusion. This is the
   zero-outer-terms case of Milnor, using its defining triangle directly. -/
theorem properHeartBoundLattice
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (k : Type u) [Field k] (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y S Sbar : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (V : Y.ProEt) [IsAffine V.left]
    (hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V)
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) [IsClosedImmersion i]
    [(j ≫ i).IsOver (Spec (.of k))]
    (L : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) S)
    (hL : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) L)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      ((rightDerivedGlobalSections Ab.{u + 1} (pullback p V.hom)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Scheme.proEtaleSheafInverseImage (pullback.fst p V.hom) Ab.{u + 1}).obj
            (((torsionLocallyClosedExtension ℓ E j i).obj L).X))))) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  let M := (torsionLocallyClosedExtension ℓ E j i).obj L
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  let r := pullback.fst p V.hom
  let U := upperStar Ab.{u + 1} r
  let F := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (AdicCompletion.ring ℓ E X)
  let Γ := rightDerivedGlobalSections Ab.{u + 1} (pullback p V.hom)
  let Φ : DerivedCategory (AdicCompletion.Modules ℓ E X) ⥤ DerivedCategory Ab.{u + 1} :=
    F.mapDerivedCategory.{u + 1, u + 1} ⋙ U.mapDerivedCategory.{u + 1, u + 1} ⋙ Γ
  have : CountableAB4Star (AdicCompletion.Modules ℓ E X) :=
    .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
      Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  have (T : Scheme.{u}) : CountableAB4Star (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
    .of_epi_π_app_zero Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat
  have : Γ.Additive := by dsimp [Γ, rightDerivedGlobalSections]; infer_instance
  let : Γ.CommShift ℤ := by dsimp [Γ, rightDerivedGlobalSections]; infer_instance
  have : Γ.IsTriangulated := by dsimp [Γ, rightDerivedGlobalSections]; infer_instance
  have : HasCountableProducts Ab.{u + 1} := ⟨fun J _ ↦ inferInstance⟩
  have : CountableAB4Star Ab.{u + 1} :=
    ⟨fun J _ ↦ HasExactLimitsOfShape.of_domain_equivalence Ab.{u + 1}
      (Discrete.equivalence (Equiv.ulift : ULift.{u + 1} J ≃ J))⟩
  have : HasCountableProducts (DerivedCategory.{u + 1} Ab.{u + 1}) :=
    derivedCategory_hasCountableProducts.{u + 1, u + 1, u + 2} Ab.{u + 1}
  have : HasCountableProducts
      (DerivedCategory.{u + 1} (AdicCompletion.Modules ℓ E X)) :=
    derivedCategory_hasCountableProducts.{u + 1, u + 1, u + 2} _
  have (T : Scheme.{u}) : HasCountableProducts
      (DerivedCategory.{u + 1} (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})) :=
    derivedCategory_hasCountableProducts.{u + 1, u + 1, u + 2} _
  have : PreservesLimitsOfShape (Discrete ℕ) F.mapDerivedCategory.{u + 1, u + 1} :=
    exact_derived_preserves_products F
  have := inverseImage_products r
  have : PreservesLimitsOfShape (Discrete ℕ) U.mapDerivedCategory.{u + 1, u + 1} :=
    exact_derived_preserves_products U
  have := sections_products (pullback p V.hom)
  have : PreservesLimitsOfShape (Discrete ℕ) Φ := inferInstance
  have hK := lattice_complete ℓ E j i L hL
  obtain ⟨P, hP, ⟨eP⟩, hPi⟩ := hK
  have hcomp : IsIso (AdicCompletion.completionMap ℓ E X K P eP) := by
    dsimp only [AdicCompletion.completionMap]
    infer_instance
  obtain ⟨c, δ, hT, _⟩ := AdicCompletion.roos_isDerivedLimit ℓ E X K P hP eP
  have hlim : IsDerivedLimit (AdicCompletion.integralStep ℓ E X K) K :=
    roos_of_iso _ _ ⟨c, δ, hT⟩
      (asIso (AdicCompletion.completionMap ℓ E X K P eP)).symm
  have hlim' := map_roos Φ _ (AdicCompletion.integralStep ℓ E X K) K hlim
  have hφ (N : AdicCompletion.Modules ℓ E X) :
      Φ.obj ((DerivedCategory.singleFunctor _ 0).obj N) ≅
        Γ.obj ((DerivedCategory.singleFunctor _ 0).obj (U.obj N.X)) :=
    Γ.mapIso (U.mapDerivedCategory.{u + 1, u + 1}.mapIso
      ((F.mapDerivedCategorySingleFunctor 0).app N) ≪≫
        (U.mapDerivedCategorySingleFunctor 0).app N.X)
  by_cases hdneg : d < 0
  · have hX : IsEmpty X := by
      constructor
      intro x
      let y := p x
      have he := topologicalKrullDim_pullback_eq_of_field
        (k := Y.residueField y) (pullback.snd p (Y.fromSpecResidueField y))
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))))
      have hi := IsHomeomorph.topologicalKrullDim_eq _
        (pullbackLeftPullbackSndIso p (Y.fromSpecResidueField y)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (Y.residueField y)
              (AlgebraicClosure (Y.residueField y)))))).hom.homeomorph.isHomeomorph
      have hb : topologicalKrullDim (p.fiber y) ≤ ⊥ := by
        simpa only [Scheme.Hom.fiber, if_pos hdneg] using
          (he.symm.trans hi).le.trans (hd y)
      let z : p.fiber y := (p.fiberHomeo y).symm ⟨x, rfl⟩
      have : Nonempty (TopologicalSpace.IrreducibleCloseds (p.fiber y)) :=
        ⟨⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
      have hn : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (p.fiber y) :=
        Order.krullDim_nonneg
      exact (not_le_of_gt (WithBot.bot_lt_coe 0)) (hn.trans hb)
    have hzero : IsZero M.X := by
      apply Sheaf.isZero_of_isZero_obj
      intro W
      have : IsEmpty W.unop.left :=
        ⟨fun x ↦ hX.false (W.unop.hom x)⟩
      exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X W.unop).isZero
    exact (DerivedCategory.homologyFunctor Ab.{u + 1} q).map_isZero
      (Γ.map_isZero ((DerivedCategory.singleFunctor _ 0).map_isZero (U.map_isZero hzero)))
  have hdNat (y : Y) : topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d.toNat : WithBot ℕ∞) := by
    simpa only [if_neg hdneg] using hd y
  have hdcast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hlevel (n : ℕ) (z : ℤ) (hz : 2 * d < z) :
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} z).obj
        (Φ.obj (AdicCompletion.integralLevel ℓ E X K n))) := by
    obtain ⟨ered⟩ := (properHeartBoundTorsion ℓ E k hchar hell p d.toNat hdNat V hV j i
      (n + 1) (by omega)).1
    have hvan := ((properHeartBoundTorsion ℓ E k hchar hell p d.toNat hdNat V hV j i
      (n + 1) (by omega)).2 ⟨L, hL⟩).2 z (by simpa only [hdcast] using hz)
    let ered' := Φ.mapIso ((reduction_level_iso ℓ E X K n).some ≪≫ ered.app ⟨L, hL⟩) ≪≫
      hφ ((torsionLocallyClosedExtension ℓ E j i).obj
        ((torsionQuotient ℓ E S (n + 1)).obj L))
    exact hvan.of_iso ((DerivedCategory.homologyFunctor Ab.{u + 1} z).mapIso ered')
  obtain ⟨c', δ', hT'⟩ := hlim'
  let B : ℕ → DerivedCategory.{u + 1} Ab.{u + 1} :=
    fun n ↦ Φ.obj (AdicCompletion.integralLevel ℓ E X K n)
  have hzero (z : ℤ) (hz : 2 * d < z) :
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} z).obj (∏ᶜ B)) := by
    have := (derivedCategory_countableProducts_properties.{0, u + 1, u + 1, u + 2} Ab.{u + 1}).2 ℕ z
    exact homology_product_zero (A := Ab.{u + 1}) B z (fun n ↦ hlevel n z hz)
  have hz : IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj (Φ.obj K)) :=
    (DerivedCategory.HomologySequence.exact₁
      (CategoryTheory.Pretriangulated.Triangle.mk c' _ δ') hT' (q - 1) q (by omega)
      ).isZero_of_both_isZero (hzero (q - 1) (by omega)) (hzero q (by omega))
  exact hz.of_iso ((DerivedCategory.homologyFunctor Ab.{u + 1} q).mapIso (hφ M)).symm


end AlgebraicGeometry.ProEtale
