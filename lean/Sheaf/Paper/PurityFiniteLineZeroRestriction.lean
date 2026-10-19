/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.PurityRankOneSectionData
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
/-!
# Degree-zero restriction for the finite Tate line

Source: Milne, Lectures on Etale Cohomology, Sections 14 and 16; blueprint
sk-prop-a1-kummer, Degrees 0 and 1.
(blueprint: lem-pur-finite-line-zero-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme
private noncomputable def zmodScalarExtensionIso
    (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ModuleCat.extendScalars (finiteEtaleTwistScalar N A hA) ≅
      forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
        ModuleCat.extendScalarsAddCommGrp A := by
  let f := finiteEtaleTwistScalar N A hA
  let adj := ModuleCat.extendScalarsAddCommGrpAdj A
  let e (M : ModuleCat.{u + 1} (ZMod N)) (P : ModuleCat.{u + 1} A) :
      ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).obj M ⟶
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat).obj P) ≃
        (M ⟶ (ModuleCat.restrictScalars f).obj P) :=
    { toFun := fun g ↦ ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars f).obj P)
        (AddMonoidHom.toZModLinearMap N (M := M)
          (M₁ := (ModuleCat.restrictScalars f).obj P) g.hom)
      invFun := fun g ↦ AddCommGrpCat.ofHom g.hom.toAddMonoidHom
      left_inv := fun g ↦ rfl
      right_inv := fun g ↦ by ext; rfl }
  let adj' : (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
      ModuleCat.extendScalarsAddCommGrp A) ⊣ ModuleCat.restrictScalars f :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun M P ↦ (adj.homEquiv _ _).trans (e M P)
        homEquiv_naturality_left_symm := by
          intro M' M P g k
          change (adj.homEquiv _ _).symm
            ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).map g ≫
              (e M P).symm k) = _
          exact adj.homEquiv_naturality_left_symm _ _
        homEquiv_naturality_right := by
          intro M P P' g k
          change e M P' (adj.homEquiv _ _ (g ≫ k)) = _
          rw [adj.homEquiv_naturality_right]
          rfl }
  exact (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} f).leftAdjointUniq adj'

/-- The published finite twist line is the existing abelian-sheaf scalar extension. -/
private noncomputable def finiteEtaleLineAbIso
    (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    finiteEtaleTateLine T N A hA ≅
      (AlgebraicGeometry.Etale.extendScalars A T).obj (T.rootsOfUnitySheaf N) :=
  (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
    (Functor.isoWhiskerLeft (finiteEtaleMuModulePresheaf T N)
      (zmodScalarExtensionIso N A hA))


private def finiteEtaleLineConstantIso (Ω : Type u) [Field Ω]
    (n : ℕ) [NeZero n] (ζ : Ω) (hζ : IsPrimitiveRoot ζ n)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of Ω))
    (A : Type (u + 1)) [CommRing A] (hA : (n : A) = 0) :
    finiteEtaleTateLine X n A hA ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) :=
  finiteEtaleLineAbIso X n A hA ≪≫
    (Etale.extendScalars A X).mapIso (X.constantZModIsoRootsOfUnitySheaf n f hζ).symm ≪≫
    Etale.extendScalarsConstantZModIso X hA

end AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting.RankOne

private theorem constant_restriction_isIso {X : Scheme.{u}}
    (A : Type (u + 1)) [CommRing A] (M : ModuleCat.{u + 1} A)
    {V W : X.Etale} [ConnectedSpace V.left] [ConnectedSpace W.left] (j : W ⟶ V) :
    IsIso (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M).obj.map j.op) := by
  change IsIso ((sheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj M)).map j.op)
  let σ := toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)
  have hv : IsIso (σ.app (op V)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨X.injective_toSheafify_app_of_nonempty M V,
      X.surjective_toSheafify_app_of_connectedSpace M V⟩
  have hw : IsIso (σ.app (op W)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨X.injective_toSheafify_app_of_nonempty M W,
      X.surjective_toSheafify_app_of_connectedSpace M W⟩
  have h := σ.naturality j.op
  have he : σ.app (op V) ≫
      (sheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).map j.op =
      σ.app (op W) := by simpa using h.symm
  exact IsIso.of_isIso_fac_left he

private theorem lines_connected (Ω : Type u) [Field Ω] :
    ConnectedSpace (Line (Spec (CommRingCat.of Ω))) ∧
    ConnectedSpace (Punctured (Spec (CommRingCat.of Ω))) := by
  let S := Spec (CommRingCat.of Ω)
  have : IrreducibleSpace (Line S) :=
    inferInstanceAs (IrreducibleSpace (AffineSpace (ULift.{u} (Fin 1)) S))
  have hc : coordinate S ≠ 0 := by
    intro h
    have hh := congrArg
      (fun a ↦ (AffineSpace.homOfVector (𝟙 S)
        (fun _ : ULift.{u} (Fin 1) ↦ (1 : Γ(S, ⊤)))).appTop a) h
    change (AffineSpace.homOfVector (𝟙 S) _).appTop (AffineSpace.coord S _) = _ at hh
    simp only [AffineSpace.homOfVector_appTop_coord, map_zero] at hh
    exact one_ne_zero hh
  have : IsReduced (Line S) :=
    inferInstanceAs (IsReduced (AffineSpace (ULift.{u} (Fin 1)) S))
  have hn : ((Line S).basicOpen (coordinate S) : Set (Line S)).Nonempty := by
    by_contra h
    have hbot := (TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp h
    exact hc ((basicOpen_eq_bot_iff _).mp hbot)
  have : Nonempty (Punctured S) := hn.to_subtype
  have : IrreducibleSpace (Punctured S) := (openImmersion S).isOpenEmbedding.irreducibleSpace
  exact ⟨inferInstance, inferInstance⟩


private theorem finiteEtale_restriction_isIso (Ω : Type u) [Field Ω]
    (n : ℕ) [NeZero n] (ζ : Ω) (hζ : IsPrimitiveRoot ζ n)
    (A : Type (u + 1)) [CommRing A] (hA : (n : A) = 0) :
    IsIso ((Scheme.finiteEtaleTateLine (Line (Spec (CommRingCat.of Ω))) n A hA).obj.map
      (restriction (Spec (CommRingCat.of Ω))).op) := by
  let S := Spec (CommRingCat.of Ω)
  let X := Line S
  obtain ⟨hX, hU⟩ := lines_connected Ω
  have : ConnectedSpace (Scheme.Etale.mk (𝟙 X)).left := hX
  have : ConnectedSpace (openObject S).left := hU
  let e := Scheme.finiteEtaleLineConstantIso Ω n ζ hζ X (lineProjection S) A hA
  have : IsIso (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)).obj.map (restriction S).op) :=
    constant_restriction_isIso A (ModuleCat.of A A) (restriction S)
  have he (W : X.Etaleᵒᵖ) : IsIso (e.hom.hom.app W) := by
    change IsIso (((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
      e).hom.app W)
    infer_instance
  exact IsIso.of_isIso_fac_right (e.hom.hom.naturality (restriction S).op)

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_zero_isIso_iff
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {W V : C} (j : W ⟶ V) (M : Sheaf J (ModuleCat.{u + 1} A)) :
    IsIso ((NatTrans.rightDerived (F := sections J A V) (G := sections J A W)
      ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) 0).app M) ↔
      IsIso (M.obj.map j.op) := by
  let F := sections J A V
  let G := sections J A W
  let α : F ⟶ G := (sheafSections J (ModuleCat.{u + 1} A)).map j.op
  let P := injectiveResolution M
  let φ := (NatTrans.mapHomologicalComplex α (.up ℕ)).app P.cocomplex
  have hc : α.app M ≫ P.toRightDerivedZero' G =
      P.toRightDerivedZero' F ≫ HomologicalComplex.cyclesMap φ 0 := by
    apply (cancel_mono (HomologicalComplex.iCycles _ 0)).mp
    rw [Category.assoc, InjectiveResolution.toRightDerivedZero'_comp_iCycles,
      Category.assoc, HomologicalComplex.cyclesMap_i,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
    exact (α.naturality (P.ι.f 0)).symm
  have h : α.app M ≫ G.toRightDerivedZero.app M =
      F.toRightDerivedZero.app M ≫ (NatTrans.rightDerived α 0).app M := by
    rw [P.toRightDerivedZero_eq F, P.toRightDerivedZero_eq G,
      P.rightDerived_app_eq α 0]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change α.app M ≫ P.toRightDerivedZero' G ≫
        ((G.mapHomologicalComplex _).obj P.cocomplex).homologyπ 0 ≫
          (P.isoRightDerivedObj G 0).inv =
      P.toRightDerivedZero' F ≫
        ((F.mapHomologicalComplex _).obj P.cocomplex).homologyπ 0 ≫
          HomologicalComplex.homologyMap φ 0 ≫ (P.isoRightDerivedObj G 0).inv
    rw [HomologicalComplex.homologyπ_naturality_assoc, ← Category.assoc, hc,
      Category.assoc]
  change IsIso ((NatTrans.rightDerived α 0).app M) ↔ IsIso (α.app M)
  rw [← isIso_comp_left_iff (F.toRightDerivedZero.app M), ← h,
    isIso_comp_right_iff]


/-- Actual derived degree-zero restriction on the finite Tate line is an isomorphism.
Source: Milne, Sections 14 and 16; blueprint sk-prop-a1-kummer, Degrees 0 and 1.
(blueprint: lem-pur-finite-line-zero-restriction).

Proof: choose a primitive ell^N-th root over the algebraically closed field. Scalar extension
of its roots-of-unity trivialization identifies the actual finite Tate line with the constant
A-sheaf. This works for all A annihilated by ell^N, including the zero ring. Both line schemes
are connected: the affine line is integral and its coordinate basic open is nonempty, since
the section with coordinate one proves that the coordinate is nonzero. On a connected etale
object, constant-sheaf sections are precisely the constant sections. Naturality of the
sheafification unit identifies restriction with the identity on their labels, so it is an
isomorphism. Transport this through the Tate-line trivialization. Finally use the natural
isomorphisms from a left-exact sections functor to its zeroth right derived functor; their
naturality is checked on the actual injective-resolution cycles. -/
theorem finite_line_zero_restriction (A : Type (u + 1)) [CommRing A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (hℓΩ : IsUnit (ℓ : Ω))
    (hA : ((ℓ ^ N : ℕ) : A) = 0) :
    let S := Spec (CommRingCat.of Ω)
    let X := Line S
    let F := Scheme.finiteEtaleTateSheaf A (ℓ ^ N) X hA 1
    IsIso ((NatTrans.rightDerived
      (F := sections X.smallEtaleTopology A (Scheme.Etale.mk (𝟙 X)))
      (G := sections X.smallEtaleTopology A (openObject S))
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        (restriction S).op) 0).app F) := by
  have : NeZero (ℓ ^ N) := ⟨ne_of_gt (pow_pos hℓ.pos N)⟩
  have : NeZero ((ℓ ^ N : ℕ) : Ω) := ⟨by
    simpa only [Nat.cast_pow] using (hℓΩ.pow N).ne_zero⟩
  obtain ⟨_, _, ζ, hζ, _⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} Ω (ℓ ^ N)
  apply (restriction_zero_isIso_iff _ A _ _).mpr
  exact finiteEtale_restriction_isIso Ω (ℓ ^ N) ζ hζ A hA

end WeilConjectures.PurityFiniteSetting.RankOne
