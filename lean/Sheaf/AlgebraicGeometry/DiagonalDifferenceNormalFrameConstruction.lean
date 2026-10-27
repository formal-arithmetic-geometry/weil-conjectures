/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameData
import all Sheaf.Paper.ChartNormalDifferential
import all Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence
import Sheaf.AlgebraicGeometry.ConormalConeHomExt
import Sheaf.AlgebraicGeometry.EtaleCoordinateDifferentialBasis
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexExact
import WeilConjectures.AlgebraicGeometry.Modules.DifferentialsSections
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexLocus

/-! # Assembly of the canonical diagonal normal frame

Source: orientation chart proof, Step 2; Stacks 0632 and 08S2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.DiagonalDifferenceReesFrame

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalized_unique {S W : Scheme.{u}} (s : S ⟶ W)
    [IsClosedImmersion s] (q q' : s.ker.normalCone ≅ PurityNormalBundle.normalCone s)
    (hq : ReesConeNormalized s q) (hq' : ReesConeNormalized s q') : q.hom = q'.hom := by
  have : IsAffineHom (PurityNormalBundle.projection s) :=
    (PurityNormalBundle.over s).property
  apply conormalCone_hom_ext s (PurityNormalBundle.projection s) (coneAlgebraIso s)
    (Scheme.Hom.purityNormalProjection s) q.hom q'.hom hq.1 hq'.1
  intro A b
  let B : W.AffineZariskiSite := ⟨A.1, A.2⟩
  apply (ConcreteCategory.bijective_of_isIso (reesSectionsIso s B).hom).1
  rw [reesSectionsIso_hom]
  simp only [CommRingCat.comp_apply]
  apply congrArg (Scheme.ΓSpecIso _).hom
  have hb : (ConormalGradedAlgebra.powerInclusion s 1).val.app (op A.1) b ∈
      s.ker.siteIdeal B := by
    obtain ⟨hb, _⟩ := ((ConormalGradedAlgebra.presentation s).affineChart A).choose_spec 1 b
    simpa using hb
  have hB (r : s.ker.normalCone ≅ PurityNormalBundle.normalCone s)
      (hr : ReesConeNormalized s r) :
      ⊤ ≤ (reesConeChart s B ≫ r.hom) ⁻¹ᵁ
        (PurityNormalBundle.projection s ⁻¹ᵁ (s ⁻¹ᵁ A.1)) := by
    rw [← Scheme.Hom.comp_preimage, Category.assoc, hr.1]
    exact reesChart_preimage s B
  have he := (hq.2.2 B b hb (hB q hq)).trans (hq'.2.2 B b hb (hB q' hq')).symm
  have hcomp (r : s.ker.normalCone ≅ PurityNormalBundle.normalCone s)
      (hr : ReesConeNormalized s r) := Scheme.Hom.appLE_comp_appLE
        (reesConeChart s B) r.hom
        (PurityNormalBundle.projection s ⁻¹ᵁ (s ⁻¹ᵁ A.1))
        (Scheme.Hom.purityNormalProjection s ⁻¹ᵁ (s ⁻¹ᵁ A.1)) ⊤
        (by rw [← Scheme.Hom.comp_preimage r.hom (PurityNormalBundle.projection s), hr.1])
        (reesChart_preimage s B)
  rw [← hcomp q hq, ← hcomp q' hq'] at he
  dsimp only [B] at he ⊢
  exact he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem signed_conormal {U V : Scheme.{u}} (h : U ⟶ V) [IsSeparated h] :
    ∃ e : ConormalGradedAlgebra.piece (pullback.diagonal h) 1 ≅ h.relativeDifferentials,
      ∀ a : Γ(U, ⊤),
        ∃ b : (ConormalGradedAlgebra.power (pullback.diagonal h) 1).val.obj (op ⊤),
          (ConormalGradedAlgebra.powerInclusion (pullback.diagonal h) 1).val.app (op ⊤) b =
            (pullback.snd h h).appTop a - (pullback.fst h h).appTop a ∧
          e.hom.val.app (op ((pullback.diagonal h) ⁻¹ᵁ ⊤))
              (ConormalGradedAlgebra.representative (pullback.diagonal h) 1 ⊤ b) =
            h.relativeDifferentials.val.map (homOfLE le_top).op
              (h.relativeDifferentialsDerivation.d (X := op ⊤) a) := by
  obtain ⟨ω, hω⟩ := ChartNormalDifferential.differenceIdentification h
  refine ⟨ω.symm, fun a ↦ ?_⟩
  obtain ⟨b, hb⟩ : ∃ b :
      (ConormalGradedAlgebra.power (pullback.diagonal h) 1).val.obj (op ⊤),
      (ConormalGradedAlgebra.powerInclusion (pullback.diagonal h) 1).app ⊤ b =
        (pullback.snd h h).appTop a - (pullback.fst h h).appTop a := by
    let δ := pullback.diagonal h
    let φ := SheafOfModules.unitToPushforwardObjUnit δ.toRingCatSheafHom
    let f := (pullback.snd h h).appTop a - (pullback.fst h h).appTop a
    have hf : φ.val.app (op ⊤) f = 0 := by
      change δ.appTop f = 0
      rw [map_sub]
      change δ.appTop ((pullback.snd h h).appTop a) -
        δ.appTop ((pullback.fst h h).appTop a) = 0
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        pullback.diagonal_snd, pullback.diagonal_fst]
      simp
    have hf' : f ∈ Set.range
        ((SheafOfModules.evaluation (pullback h h).ringCatSheaf (op ⊤)).map
          (kernel.ι φ)) := by
      rw [Scheme.Modules.range_map_kernelι]
      exact hf
    obtain ⟨b, hb⟩ := hf'
    obtain ⟨e, he⟩ := ChartNormalDifferential.idealKernelIso δ
    refine ⟨e.inv.app ⊤ b, ?_⟩
    have hh : e.inv ≫ δ.ker.toModulesι = kernel.ι φ := by
      rw [← he, Iso.inv_hom_id_assoc]
    exact (congrArg (fun m ↦ m.app ⊤ b) hh).trans hb
  have hb' : (ConormalGradedAlgebra.powerInclusion (pullback.diagonal h) 1).app ⊤ b =
      (pullback.snd h h).appLE ⊤ ⊤ le_top a -
        (pullback.fst h h).appLE ⊤ ⊤ le_top a := by
    simpa [Scheme.Hom.appLE_top_top, Scheme.Hom.preimage_top, inf_top_eq] using hb
  have hd := hω ⊤ ⊤ le_top le_top (by simp) a b hb'
  have hd' : ω.hom.val.app (op ⊤)
      (h.relativeDifferentialsDerivation.d (X := op ⊤) a) =
        ConormalGradedAlgebra.representative (pullback.diagonal h) 1 ⊤ b := by
    simpa using hd
  refine ⟨b, hb, ?_⟩
  simpa using (show ω.inv.val.app (op ⊤)
      (ConormalGradedAlgebra.representative (pullback.diagonal h) 1 ⊤ b) =
        h.relativeDifferentialsDerivation.d (X := op ⊤) a from by
    rw [← hd']
    exact congrArg (fun f ↦ f.val.app (op ⊤)
      (h.relativeDifferentialsDerivation.d (X := op ⊤) a)) ω.hom_inv_id)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem framed_spectrum {S W : Scheme.{u}} [IsAffine S] (s : S ⟶ W)
    [IsClosedImmersion s] [IsIso (ConormalGradedAlgebra.symmetricComparison s)]
    (d : ℕ) (e : SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin d)) ≅
      ConormalGradedAlgebra.piece s 1) :
    ∃ n : PurityNormalBundle.normalCone s ≅ AffineSpace (ULift.{u} (Fin d)) S,
      n.hom ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = PurityNormalBundle.projection s ∧
      PurityNormalBundle.zeroSection s ≫ n.hom =
        AffineSpace.zeroSection (ULift.{u} (Fin d)) S ∧
      ∀ (T : S.Opens) (i : ULift.{u} (Fin d)),
        n.hom.appLE ⊤ (PurityNormalBundle.projection s ⁻¹ᵁ T) (by simp)
            (AffineSpace.coord S i) =
          (coneAlgebraIso s).hom.right.hom.app (op T)
            (((ConormalGradedAlgebra.presentation s).inclusion 1).val.app (op T)
              (e.hom.val.app (op T)
                ((SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app (op T)
                  (1 : Γ(S, T))))) := by
  classical
  let b : Module.Basis (ULift.{u} (Fin d)) Γ(S, ⊤)
      Γ(ConormalGradedAlgebra.piece s 1, ⊤) :=
    Module.Basis.ofEquivFun ((appLinearEquivOfIso e ⊤).symm.trans
      (freeSectionsEquivOpens ⊤ (ULift.{u} (Fin d))))
  let α := asIso (ConormalGradedAlgebra.symmetricComparison s) ≪≫ coneAlgebraIso s
  let p := PurityNormalBundle.projection s
  have : IsAffineHom p := (PurityNormalBundle.over s).property
  have : IsAffine (PurityNormalBundle.normalCone s) := isAffine_of_isAffineHom p
  let z (T : S.Opens) (i : ULift.{u} (Fin d)) :=
    e.hom.val.app (op T) ((SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app
      (op T) (1 : Γ(S, T)))
  let v (i : ULift.{u} (Fin d)) : Γ(PurityNormalBundle.normalCone s, ⊤) :=
    (α.hom.right.hom.app (op ⊤)) ((SymmetricAlgebraSheaf.inclusion
      (ConormalGradedAlgebra.piece s 1)).val.app (op ⊤) (z ⊤ i))
  let n := AffineSpace.homOfVector p v
  have hn : n ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = p :=
    AffineSpace.homOfVector_over p v
  have hb (i : ULift.{u} (Fin d)) : b i = z ⊤ i := by
    have hb := congrFun (Module.Basis.coe_ofEquivFun
      ((appLinearEquivOfIso e ⊤).symm.trans
        (freeSectionsEquivOpens ⊤ (ULift.{u} (Fin d))))) i
    rw [hb]
    change e.hom.val.app (op ⊤)
      ((freeSectionsEquivOpens ⊤ (ULift.{u} (Fin d))).symm (Pi.single i 1)) = _
    congr 1
    apply (freeSectionsEquivOpens ⊤ (ULift.{u} (Fin d))).injective
    rw [LinearEquiv.apply_symm_apply]
    ext j
    change (Pi.single i 1 : ULift.{u} (Fin d) → Γ(S, ⊤)) j =
      Hom.app (freeπ (X := S) j) ⊤
        (Hom.app (SheafOfModules.ιFree (R := S.ringCatSheaf) i) ⊤ (1 : Γ(S, ⊤)))
    rw [freeπ_app_ιFree_app_opens]
    simp [Pi.single_apply, eq_comm]
  have hq : (ConormalGradedAlgebra.piece s 1).IsQuasicoherent :=
    (ConormalGradedAlgebra.presentation s).pieceQuasicoherent 1
  have hσ : IsIso (CommRingCat.ofHom (SymmetricAlgebraSheaf.sectionMap
      (ConormalGradedAlgebra.piece s 1) (op ⊤))) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ((quasiCoherentSymmetricAlgebra_affine_comparison S
        (ConormalGradedAlgebra.piece s 1)).2 ⟨⊤, isAffineOpen_top S⟩)
  let φ : CommRingCat.of (MvPolynomial (ULift.{u} (Fin d)) Γ(S, ⊤)) ≅
      Γ(PurityNormalBundle.normalCone s, ⊤) :=
    (SymmetricAlgebra.equivMvPolynomial b).symm.toRingEquiv.toCommRingCatIso ≪≫
      asIso (CommRingCat.ofHom (SymmetricAlgebraSheaf.sectionMap
        (ConormalGradedAlgebra.piece s 1) (op ⊤))) ≪≫
      asIso (α.hom.right.hom.app (op ⊤))
  have hφX (i : ULift.{u} (Fin d)) : φ.hom (MvPolynomial.X i) = v i := by
    change α.hom.right.hom.app (op ⊤) (SymmetricAlgebraSheaf.sectionMap _ _
      ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.X i))) = _
    rw [SymmetricAlgebra.equivMvPolynomial_symm_X, hb]
    rfl
  have hφC (a : Γ(S, ⊤)) : φ.hom (MvPolynomial.C a) = p.appTop a := by
    change α.hom.right.hom.app (op ⊤) (SymmetricAlgebraSheaf.sectionMap _ _
      ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.C a))) = _
    rw [show (MvPolynomial.C a) = algebraMap Γ(S, ⊤) _ a from rfl,
      AlgEquiv.commutes]
    exact congrArg (fun t ↦ t.hom.app (op ⊤) a) (Under.w α.hom)
  let nP := n ≫ (AffineSpace.isoOfIsAffine (ULift.{u} (Fin d)) S).hom
  have hnP : nP.specStructureMap ⊤ = φ.hom := by
    simp only [nP, Scheme.Hom.specStructureMap, Scheme.Hom.appLE_top_top,
      Scheme.Hom.comp_appTop, AffineSpace.isoOfIsAffine_hom_appTop,
      Category.assoc, Iso.inv_hom_id_assoc]
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext'
    · ext a
      change n.appTop ((MvPolynomial.eval₂Hom
        (AffineSpace (ULift.{u} (Fin d)) S ↘ S).appTop.hom
        (AffineSpace.coord S)) (MvPolynomial.C a)) = φ.hom (MvPolynomial.C a)
      rw [MvPolynomial.eval₂Hom_C]
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hn]
      exact (hφC a).symm
    · intro i
      change n.appTop ((MvPolynomial.eval₂Hom
        (AffineSpace (ULift.{u} (Fin d)) S ↘ S).appTop.hom (AffineSpace.coord S))
        (MvPolynomial.X i)) = _
      rw [MvPolynomial.eval₂Hom_X', AffineSpace.homOfVector_appTop_coord]
      exact (hφX i).symm
  have : IsIso (Spec.map (nP.specStructureMap ⊤)) := by rw [hnP]; infer_instance
  have : IsIso nP := by
    have : IsIso ((isAffineOpen_top (PurityNormalBundle.normalCone s)).fromSpec ≫ nP) := by
      rw [nP.fromSpec_comp_eq_specMap (isAffineOpen_top _)]
      infer_instance
    have : IsIso (isAffineOpen_top (PurityNormalBundle.normalCone s)).fromSpec := by
      rw [IsAffineOpen.fromSpec_top]
      infer_instance
    exact IsIso.of_isIso_comp_left (isAffineOpen_top _).fromSpec nP
  have : IsIso n := IsIso.of_isIso_comp_right n
    (AffineSpace.isoOfIsAffine (ULift.{u} (Fin d)) S).hom
  refine ⟨asIso n, hn, ?_, ?_⟩
  · change PurityNormalBundle.zeroSection s ≫ n = _
    apply AffineSpace.hom_ext
    · rw [Category.assoc, hn, (PurityNormalBundle.zeroSection_spec s).1,
        AffineSpace.zeroSection_over]
    · intro i
      change (PurityNormalBundle.zeroSection s).appTop
        ((AffineSpace.homOfVector p v).appTop (AffineSpace.coord S i)) =
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) S).appTop (AffineSpace.coord S i)
      rw [AffineSpace.homOfVector_appTop_coord, AffineSpace.zeroSection_appTop_coord]
      have hv := ChartNormalDifferential.normalZero_app s ⊤
        ((ConormalGradedAlgebra.symmetricComparison s).right.hom.app (op ⊤)
          ((SymmetricAlgebraSheaf.inclusion _).val.app (op ⊤) (z ⊤ i)))
      have hgen := (ConormalGradedAlgebra.presentation s).symmetricComparison.exists.choose_spec
        ⊤ (z ⊤ i)
      change (ConormalGradedAlgebra.symmetricComparison s).right.hom.app (op ⊤)
        ((SymmetricAlgebraSheaf.inclusion _).val.app (op ⊤) (z ⊤ i)) = _ at hgen
      rw [hgen] at hv
      have hz := congrArg (fun t ↦ t.val.app (op ⊤) (z ⊤ i))
        (ChartNormalDifferential.augmentation_inclusion s)
      change (ConormalGradedAlgebra.augmentation s).right.hom.app (op ⊤)
        (((ConormalGradedAlgebra.presentation s).inclusion 1).val.app (op ⊤) (z ⊤ i)) = 0
        at hz
      rw [hz] at hv
      change (PurityNormalBundle.zeroSection s).appTop
        ((coneAlgebraIso s).hom.right.hom.app (op ⊤)
          ((ConormalGradedAlgebra.symmetricComparison s).right.hom.app (op ⊤)
            ((SymmetricAlgebraSheaf.inclusion _).val.app (op ⊤) (z ⊤ i)))) = 0
      rw [hgen]
      rw [show coneAlgebraIso s = ChartNormalDifferential.normalAlgebraIso s from rfl]
      convert! hv using 1
      simp only [Scheme.Hom.preimage_top, Scheme.Hom.appLE_top_top]
      rfl
  · intro T i
    change n.appLE ⊤ (p ⁻¹ᵁ T) (by simp) (AffineSpace.coord S i) = _
    have hnc : n.appLE ⊤ (p ⁻¹ᵁ T) (by simp) (AffineSpace.coord S i) =
        (PurityNormalBundle.normalCone s).presheaf.map (homOfLE le_top).op (v i) := by
      rw [← Scheme.Hom.appLE_map (e := by simp), Scheme.Hom.appLE_top_top,
        CommRingCat.comp_apply]
      exact congrArg ((PurityNormalBundle.normalCone s).presheaf.map (homOfLE le_top).op)
        (AffineSpace.homOfVector_appTop_coord p v i)
    rw [hnc]
    
    have hz : (ConormalGradedAlgebra.piece s 1).val.map
        (homOfLE (le_top : T ≤ ⊤)).op (z ⊤ i) = z T i := by
      unfold z
      rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
      congr 2
      exact map_one ((S.presheaf.map (homOfLE (le_top : T ≤ ⊤)).op).hom)
    have ha := congrArg (fun f ↦ f ((SymmetricAlgebraSheaf.inclusion
      (ConormalGradedAlgebra.piece s 1)).val.app (op ⊤) (z ⊤ i)))
      (α.hom.right.hom.naturality (homOfLE (le_top : T ≤ ⊤)).op)
    simp only [CommRingCat.comp_apply] at ha
    have hnat : (PurityNormalBundle.normalCone s).presheaf.map
        (homOfLE (le_top : p ⁻¹ᵁ T ≤ ⊤)).op (v i) =
        α.hom.right.hom.app (op T)
          ((SymmetricAlgebraSheaf.algebra (ConormalGradedAlgebra.piece s 1)).right.obj.map
            (homOfLE (le_top : T ≤ ⊤)).op
              ((SymmetricAlgebraSheaf.inclusion _).val.app (op ⊤) (z ⊤ i))) := by
      convert! ha.symm using 1
    rw [hnat]
    have hi := PresheafOfModules.naturality_apply
      (SymmetricAlgebraSheaf.inclusion (ConormalGradedAlgebra.piece s 1)).val
      (homOfLE (le_top : T ≤ ⊤)).op (z ⊤ i)
    change (SymmetricAlgebraSheaf.inclusion _).val.app (op T)
      ((ConormalGradedAlgebra.piece s 1).val.map (homOfLE (le_top : T ≤ ⊤)).op
        (z ⊤ i)) = _ at hi
    rw [hz] at hi
    have hi' : ((SymmetricAlgebraSheaf.algebra (ConormalGradedAlgebra.piece s 1)).right.obj.map
        (homOfLE (le_top : T ≤ ⊤)).op)
        ((SymmetricAlgebraSheaf.inclusion _).val.app (op ⊤) (z ⊤ i)) =
        (SymmetricAlgebraSheaf.inclusion _).val.app (op T) (z T i) := by
      exact hi.symm
    rw [hi']
    have hgen := (ConormalGradedAlgebra.presentation s).symmetricComparison.exists.choose_spec
      T (z T i)
    change (ConormalGradedAlgebra.symmetricComparison s).right.hom.app (op T)
      ((SymmetricAlgebraSheaf.inclusion _).val.app (op T) (z T i)) = _ at hgen
    exact congrArg ((coneAlgebraIso s).hom.right.hom.app (op T)) hgen

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem symmetric_of_zero {S : Scheme.{u}} (M : S.Modules) (hM : IsZero M) :
    Nonempty (SymmetricAlgebraSheaf.algebra M ≅ Under.mk (𝟙 S.sheaf)) := by
  let a := VectorBundleZeroSection.augmentation S M
  let b : (Under.mk (𝟙 S.sheaf) : S.CommAlgebraSheaf) ⟶
      SymmetricAlgebraSheaf.algebra M :=
    Under.homMk (SymmetricAlgebraSheaf.algebra M).hom (by simp)
  have hab : a ≫ b = 𝟙 _ := by
    apply ExistsUnique.unique (exists_quasiCoherentSymmetricAlgebra_core S M
      (SymmetricAlgebraSheaf.algebra M) (SymmetricAlgebraSheaf.inclusion M))
    · intro T x
      have hx : x = 0 := by
        exact congrArg (fun f ↦ Hom.app f T x) (hM.eq_of_src (𝟙 M) 0)
      rw [hx]
      simp
    · intro T x
      rfl
  have hba : b ≫ a = 𝟙 _ := by
    apply Under.UnderMorphism.ext
    exact (Under.w a).trans (by simp)
  exact ⟨⟨a, b, hab, hba⟩⟩

/-- The coordinate-difference chart canonically assembles the ordered conormal and normal
frames. The proof composes the existing difference-identification, affine differential-frame,
symmetric-comparison, relative-Spec, and normalized-Rees declarations; the displayed
section formulas uniquely determine every field. Rank zero uses the empty free module and
its unit symmetric algebra. Source: orientation chart proof, Step 2
(blueprint: lem-pur-diagonal-difference-normal-frame). -/
theorem normal_frame_exists (k : Type u) [Field k]
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (aU : U ⟶ Spec (.of k)) (aV : V ⟶ Spec (.of k))
    [LocallyOfFiniteType aU] [LocallyOfFiniteType aV]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [SmoothOfRelativeDimension d h]
    (hk : h ≫ aV = aU)
    (c : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale c]
    (hc : c ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    Nonempty (NormalFrame d h (fun i ↦ c.appTop (AffineSpace.coord V i))) := by
  have := LocallyOfFiniteType.isLocallyNoetherian aU
  have : IsNoetherian U := {}
  have : LocallyOfFiniteType (h ≫ aV) := hk.symm ▸ inferInstance
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h aV
  have : QuasiCompact h := inferInstance
  have hs := ChartNormalDifferential.diagonalSymmetric d h
  obtain ⟨ω, hω⟩ := signed_conormal h
  obtain ⟨e, he⟩ := coordinate_differential_frame d h c hc
  obtain ⟨n, hn, hz, hv⟩ := framed_spectrum (pullback.diagonal h) d (e ≪≫ ω.symm)
  have hzero (hd : d = 0) : IsZero (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) := by
    subst d
    exact (isZero_free_of_isEmpty (X := U) (ULift.{u} (Fin 0))).of_iso (e ≪≫ ω.symm).symm
  exact ⟨{
    symmetric := hs
    conormal := ω
    sign := hω
    differentialFrame := e
    differentialFrame_value := he
    normal := n
    normal_over := hn
    normal_zero := hz
    normal_coordinate := hv
    comparison_independent := fun q q' hq hq' ↦
      congrArg (· ≫ n.hom) (normalized_unique _ q q' hq hq')
    rank_zero_conormal := hzero
    rank_zero_symmetric := fun hd ↦ symmetric_of_zero _ (hzero hd) }⟩

end AlgebraicGeometry.DiagonalDifferenceReesFrame
