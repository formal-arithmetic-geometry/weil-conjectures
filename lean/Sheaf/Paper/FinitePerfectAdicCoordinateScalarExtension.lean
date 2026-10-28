/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.FinitePerfectAdicMarkedOrigin
public import Sheaf.Paper.DerivedNormalizationArrows
import Sheaf.Paper.BoundedConstructibleTower
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import all Sheaf.Paper.WitnessCompatibility
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Scalar extension of the actual finite quotient coordinates

Source: Stacks Project, Tags 06YY, 0D6D, 03CY and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

-- The scalar mate is computed below from the flat-resolution API, so this module
-- does not import the downstream local-systems theorem.
open AlgebraicGeometry.ProEtale

private theorem pro_flat (A : Type (t + 1)) [CommRing A]
    {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{t + 1} A) f).PreservesFlat := by
  have := MorphismProperty.Over.representablyFlat_pullback @WeaklyEtale f
  refine ⟨fun hF ↦ ?_⟩
  exact flat_pullback_of_local_relations (G := MorphismProperty.Over.pullback
    @WeaklyEtale ⊤ f) (Scheme.ProEt.coverPreserving_overPullback f) hF

private theorem pro_ordinary_iso
    {A B : Type (t + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{t}} (f : X ⟶ Y) :
    IsIso (((mateEquiv (scalarAdjunction (Scheme.ProEt.topology Y) a)
      (scalarAdjunction (Scheme.ProEt.topology X) a)).symm
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a f).hom)).natTrans) := by
  apply isIso_left_mate_of_iterated
    (scalarAdjunction (Scheme.ProEt.topology Y) a)
    (scalarAdjunction (Scheme.ProEt.topology X) a)
    (upperStarLowerStarAdjunction (ModuleCat.{t + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{t + 1} B) f)
  have h := mate_of_conjugate
    (upperStarLowerStarAdjunction (ModuleCat.{t + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{t + 1} A) f)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) a)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) a)
    (Iso.refl _) (show lowerStar (ModuleCat.{t + 1} B) f ⋙
      Sheaf.restrictScalars (Scheme.ProEt.topology Y) a ⟶
      Sheaf.restrictScalars (Scheme.ProEt.topology X) a ⋙
        lowerStar (ModuleCat.{t + 1} A) f from 𝟙 _) (by
      ext F V x
      simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj,
        Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.id_app,
        Category.id_comp]
      exact congrArg (fun k ↦ k.hom x)
        ((ModuleCat.restrictCoextendScalarsAdj.{t + 1, t + 1, t + 1} a).right_triangle_components
          _))
  change (mateEquiv _ _ (TwoSquare.mk _ _ _ _
    (upperStarRestrictScalarsIso a f).hom)).natTrans = _ at h
  rw [h]
  infer_instance
-- Instantiate the normalized flat-resolution comparison.
private theorem pro_computed_iso
    {A B : Type (t + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{t}} (f : X ⟶ Y) :
    IsIso (((mateEquiv
      (scalarDerivedAdjunctionData (Scheme.ProEt.topology Y) a).adjunction
      (scalarDerivedAdjunctionData (Scheme.ProEt.topology X) a).adjunction).symm
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso
          (upperStarRestrictScalarsIso a f)).hom)).natTrans) := by
  have := pro_flat A f
  have : IsIso (((mateEquiv
      (scalarAdjunction (Scheme.ProEt.topology Y) a)
      (scalarAdjunction (Scheme.ProEt.topology X) a)).symm
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a f).symm.inv)).natTrans) := by
    simpa only [Iso.symm_inv] using pro_ordinary_iso a f
  have h := derived_mate_isIso_of_flat
    (A := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{t + 1} A))
    (B := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{t + 1} B))
    (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{t + 1} A))
    (D := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{t + 1} B))
    (scalarAdjunction (Scheme.ProEt.topology Y) a)
    (scalarAdjunction (Scheme.ProEt.topology X) a)
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology Y) a)
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology X) a)
    (upperStar (ModuleCat.{t + 1} A) f)
    (upperStar (ModuleCat.{t + 1} B) f)
    (upperStarRestrictScalarsIso a f).symm
  have hs : (Functor.mapDerivedCategoryNatIso
      (upperStarRestrictScalarsIso a f).symm).inv =
      (Functor.mapDerivedCategoryNatIso (upperStarRestrictScalarsIso a f)).hom := by
    simpa only [Iso.symm_symm_eq] using
      (Functor.mapDerivedCategoryNatIso_symm (upperStarRestrictScalarsIso a f).symm).symm
  simpa only [Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, hs, Category.assoc] using h

private theorem coordinate_scalar_mate_isIso
    {B D : Type (t + 1)} [CommRing B] [CommRing D]
    (q : B →+* D) {X Y : Scheme.{t}} (f : X ⟶ Y) :
    IsIso (((mateEquiv
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (ProEt.topology Y) q))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (ProEt.topology X) q))).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
        (ProEtale.upperStarRestrictScalarsIso q f)).hom)).natTrans) := by
  have := pro_computed_iso q f
  exact isIso_left_mate_change_adjunction
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (ProEt.topology Y) q))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (ProEt.topology X) q))
    (scalarDerivedAdjunctionData (ProEt.topology Y) q).adjunction
    (scalarDerivedAdjunctionData (ProEt.topology X) q).adjunction
    (Functor.mapDerivedCategorySquareIso (ProEtale.upperStarRestrictScalarsIso q f)).hom

private def scalarEncoding (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) :=
  pbcRestrict φ ⋙ proEtaleModuleRestriction X B

private instance scalarEncoding_equivalence (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) [IsIso φ] :
    (scalarEncoding X B R φ).IsEquivalence := by
  have : (pbcRestrict φ).IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence X
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso (asIso φ))).functor.IsEquivalence
  have := proEtaleModuleRestriction_isEquivalence X B
  unfold scalarEncoding
  infer_instance

private instance scalarEncoding_additive (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) : (scalarEncoding X B R φ).Additive := by
  have := proEtaleModuleRestriction_isEquivalence X B
  have : (proEtaleModuleRestriction X B).Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold scalarEncoding
  infer_instance

private def scalarEncodingSquare (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D] (q : B →+* D)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : adicConstantRing X B ⟶ R) (ψ : adicConstantRing X D ⟶ S)
    (p : R ⟶ S) (h : adicConstantMap X q ≫ ψ = φ ≫ p) :
    pbcRestrict p ⋙ scalarEncoding X B R φ ≅
      scalarEncoding X D S ψ ⋙ sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{t + 1} (RingHom.ulift.{t + 1, t + 1} q)) := by
  have hs (U : X.ProEtᵒᵖ) (a : ULift.{t + 1} B) :
      p.hom.app U (φ.hom.app U ((proEtaleModuleScalarUnit X B).app U a)) =
        ψ.hom.app U ((proEtaleModuleScalarUnit X D).app U
          ((RingHom.ulift.{t + 1, t + 1} q) a)) := by
    have hu := congrArg (fun k ↦ (k.app U).hom a)
      (toSheafify_naturality (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom (RingHom.ulift.{t + 1, t + 1} q))))
    have hh := congrArg (fun k ↦ k.hom.app U ((proEtaleModuleScalarUnit X B).app U a)) h
    change ψ.hom.app U ((adicConstantMap X q).hom.app U
      ((proEtaleModuleScalarUnit X B).app U a)) =
      p.hom.app U (φ.hom.app U ((proEtaleModuleScalarUnit X B).app U a)) at hh
    change (proEtaleModuleScalarUnit X D).app U ((RingHom.ulift.{t + 1, t + 1} q) a) =
      (adicConstantMap X q).hom.app U ((proEtaleModuleScalarUnit X B).app U a) at hu
    rw [← hh, ← hu]
  let F := pbcRestrict p ⋙ scalarEncoding X B R φ
  let G := scalarEncoding X D S ψ ⋙ sheafCompose (ProEt.topology X)
    (ModuleCat.restrictScalars.{t + 1} (RingHom.ulift.{t + 1, t + 1} q))
  let eU (N : pbcModules X S) (U : X.ProEtᵒᵖ) :
      ((F.obj N).obj.obj U) ≃ₗ[ULift.{t + 1} B] ((G.obj N).obj.obj U) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ by
        change p.hom.app U (φ.hom.app U ((proEtaleModuleScalarUnit X B).app U a)) •
            (show N.val.obj U from x) =
          ψ.hom.app U ((proEtaleModuleScalarUnit X D).app U
            ((RingHom.ulift.{t + 1, t + 1} q) a)) • (show N.val.obj U from x)
        rw [hs] }
  let e (N : pbcModules X S) :
      ((pbcRestrict p ⋙ scalarEncoding X B R φ).obj N).obj ≅
        ((scalarEncoding X D S ψ ⋙ sheafCompose (ProEt.topology X)
          (ModuleCat.restrictScalars.{t + 1} (RingHom.ulift.{t + 1, t + 1} q))).obj N).obj :=
    NatIso.ofComponents (fun U ↦ (eU N U).toModuleIso) (by intros; ext x; rfl)
  exact NatIso.ofComponents (fun N ↦
    { hom := ⟨(e N).hom⟩
      inv := ⟨(e N).inv⟩
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl }) (by intros; ext U x; rfl)

/-- Extending the larger finite quotient coordinates to the smaller coefficient ring
recovers the smaller actual quotient coordinates.

Source: Stacks Project, Tag 06YY, composition of derived pullback (0D6D), the
constant-scalar module equivalence (03CY), and the quotient tower in Tag 09C6.
(blueprint: new-g3-finite-perfect-adic-coordinate-scalar-extension).

Proof: derived extension along the completed projection at level n+1 followed by
extension along the consecutive quotient map is naturally isomorphic to extension
along the completed projection at n. The projections compose by the limit-cone
identity. Transport this balancing isomorphism along the supplied isomorphisms phi;
their compatibility with consecutive quotients identifies the resulting ring map
with the constant quotient homomorphism. Restriction to constant scalars is an exact
equivalence. Its scalar-restriction square therefore has invertible adjunction mate.
Inverse image to the chart also has invertible scalar mate, computed on flat K-flat
resolutions by the ordinary balanced-tensor identity. Their composite identifies
scalar extension of the specified quotient coordinates with the specified smaller
coordinates. Uniqueness of left adjoints identifies any supplied L and adjunction
with this extension. No boundedness, nonempty chart, nonzero ring or flatness of the
quotient homomorphism is used. -/
theorem finitePerfectAdic_coordinate_scalar_extension
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n))
    (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale) (n : ℕ)
    (L : DerivedCategory (Sheaf (ProEt.topology V.left)
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) ) ⥤
      DerivedCategory (Sheaf (ProEt.topology V.left)
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))))
    (adj : L ⊣ normalizationRestrict (ProEt.topology V.left)
      (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))) :
    Nonempty (L.obj (finitePerfectAdicQuotientCoordinates X d φ M V (n + 1)) ≅
      finitePerfectAdicQuotientCoordinates X d φ M V n) := by
  let B := A ⧸ d.ideal ^ (n + 1 + 1)
  let D := A ⧸ d.ideal ^ (n + 1)
  let q₀ : B →+* D := Ideal.Quotient.factorPowSucc d.ideal (n + 1)
  let q := RingHom.ulift.{t + 1, t + 1} q₀
  let p := completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)
  have := hφ (n + 1)
  have := hφ n
  let E := scalarEncoding X B (completedAdicFiniteCommRing X d (n + 1)) (φ (n + 1))
  let E' := scalarEncoding X D (completedAdicFiniteCommRing X d n) (φ n)
  let G := ProEtale.pbcFixedScalarExtension (ProEt.topology X) q
  let H := ProEtale.pbcFixedScalarExtension (ProEt.topology V.left) q
  let aG := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (ProEt.topology X) q)
  let aH := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (ProEt.topology V.left) q)
  let a := pbcDerivedScalarAdjunction p
  let s : pbcDerivedRestrict p ⋙ E.mapDerivedCategory ≅
      E'.mapDerivedCategory ⋙ normalizationRestrict (ProEt.topology X) q :=
    Functor.mapDerivedCategorySquareIso
      (scalarEncodingSquare X q₀ (φ (n + 1)) (φ n) p (hcompat.1 n))
  have : IsIso ((mateEquiv a aG).symm s.hom).natTrans :=
    isIso_inverseMate_of_equivalences a aG s
  let b := asIso ((mateEquiv a aG).symm s.hom).natTrans
  let Q := (completedAdicQuotientReduction X d (n + 1)).obj M
  let v : G.obj (E.mapDerivedCategory.obj Q) ≅
      E'.mapDerivedCategory.obj ((completedAdicQuotientReduction X d n).obj M) :=
    b.app Q ≪≫ E'.mapDerivedCategory.mapIso
      (pbcReductionNormalization (completedAdicCommProjection X d (n + 1)) p
        (completedAdicCommProjection X d n)
        (completedAdicCommProjection_comp X d (n + 1) n (Nat.le_succ n)) M)
  let F := ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B)) V.hom
  let F' := ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} D)) V.hom
  let s' := Functor.mapDerivedCategorySquareIso
    (ProEtale.upperStarRestrictScalarsIso q V.hom)
  have : IsIso ((mateEquiv aG aH).symm s'.hom).natTrans :=
    coordinate_scalar_mate_isIso q V.hom
  let b' := asIso ((mateEquiv aG aH).symm s'.hom).natTrans
  let fac : E.mapDerivedCategory ⋙ F.mapDerivedCategory ≅
      (finiteCoefficientSliceRestriction X B (completedAdicFiniteCommRing X d (n + 1))
        (φ (n + 1)) V).mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso E F).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (Functor.isoWhiskerLeft E (ProEtale.upperStarIsoLocalizationRestriction
          (ModuleCat.{t + 1} (ULift.{t + 1} B)) V.hom inferInstance))
  let fac' : E'.mapDerivedCategory ⋙ F'.mapDerivedCategory ≅
      (finiteCoefficientSliceRestriction X D (completedAdicFiniteCommRing X d n)
        (φ n) V).mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso E' F').symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (Functor.isoWhiskerLeft E' (ProEtale.upperStarIsoLocalizationRestriction
          (ModuleCat.{t + 1} (ULift.{t + 1} D)) V.hom inferInstance))
  exact ⟨(adj.leftAdjointUniq aH).app _ ≪≫ H.mapIso (fac.app Q).symm ≪≫
    b'.app (E.mapDerivedCategory.obj Q) ≪≫ F'.mapDerivedCategory.mapIso v ≪≫
    fac'.app ((completedAdicQuotientReduction X d n).obj M)⟩

end AlgebraicGeometry.Scheme
