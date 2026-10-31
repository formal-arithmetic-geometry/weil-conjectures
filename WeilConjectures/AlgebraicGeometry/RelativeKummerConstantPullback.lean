/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeKummerStrictLocalInvariance
import WeilConjectures.AlgebraicGeometry.Sites.TorsorPullback
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback

/-! # Pullback of the normalized Kummer constant section

Source: blueprint latest, relative Kummer calculation, Step 2; Stacks Tags 03PK
and 01EZ (blueprint: new-pur-relative-kummer-constant-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Etale
open Scheme

private theorem additiveConstantUnit_apply {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (M : AddCommGrpCat.{u + 1}) (V : Y.Etale) (m : M) :
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _
    ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app M))).hom.app (op V)
      ((CategoryTheory.toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
        M)).app
        (op V) m) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj
        M)).app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V)) m := by
  let adjY := constantSheafAdj Y.smallEtaleTopology (AddCommGrpCat.{u + 1}) terminalIsTerminal
  let adjZ := constantSheafAdj Z.smallEtaleTopology (AddCommGrpCat.{u + 1}) terminalIsTerminal
  let e := Etale.lowerStarCompSheafSectionsTerminalIso (AddCommGrpCat.{u + 1}) g
  let adj := Etale.upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) g
  have key : (adjY.unit.app M ≫ ((sheafSections
    Y.smallEtaleTopology _).obj (op (⊤_ Y.Etale))).map
      (adj.unit.app ((constantSheaf Y.smallEtaleTopology _).obj M)) ≫ e.hom.app _) ≫
      ((sheafSections Z.smallEtaleTopology _).obj (op (⊤_ Z.Etale))).map
        ((upperStarConstantSheafIso (AddCommGrpCat.{u + 1}) g).hom.app M) = adjZ.unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app ((adjY.comp adj).ofNatIsoRight e) adjZ
      M
  have h := congr(($key).hom m)
  -- constant sections are compatible with restriction
  have hts {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) [HasWeakSheafify J
      (AddCommGrpCat.{u + 1})] {U W : C} (f : U ⟶ W) :
      (sheafify J ((Functor.const Cᵒᵖ).obj M)).map f.op
        ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op W) m) =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) m :=
    (congr(($((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).naturality
      f.op)).hom m)).symm
  let θ := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _
    ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app M))
  let F := MorphismProperty.Over.pullback @Etale ⊤ g
  let i := (PreservesTerminal.iso g.Etale)
  let G := (constantSheaf Z.smallEtaleTopology (AddCommGrpCat.{u + 1})).obj M
  let x := (CategoryTheory.toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
    M)).app
    (op (⊤_ Y.Etale)) m
  have h₁ : G.obj.map i.op.symm.hom (θ.hom.app (op (⊤_ Y.Etale)) x) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj
        M)).app
        (op (⊤_ Z.Etale)) m :=
    (NatTrans.naturality_apply ((upperStarConstantSheafIso (AddCommGrpCat.{u + 1}) g).hom.app
      M).hom
      i.op.symm.hom _).symm.trans h
  have hT : θ.hom.app (op (⊤_ Y.Etale)) x =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj
        M)).app
        (op (F.obj (⊤_ Y.Etale))) m := by
    have h₂ := congrArg (G.obj.map i.op.hom) h₁
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.symm_hom, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.id_apply] at h₂
    exact h₂.trans (hts Z.smallEtaleTopology i.hom)
  have hn := NatTrans.naturality_apply θ.hom (terminal.from V).op x
  rw [← hts Y.smallEtaleTopology (terminal.from V)]
  refine hn.trans ?_
  change G.obj.map (F.map (terminal.from V)).op (θ.hom.app (op (⊤_ Y.Etale)) x) = _
  rw [hT]
  exact hts Z.smallEtaleTopology _


private theorem generator_map (T : Scheme.{u}) (m : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0)
    {W V : T.Etaleᵒᵖ} (f : W ⟶ V) (a : A)
    (z : (T.rootsOfUnitySheaf m).obj.obj W) :
    (Scheme.finiteEtaleTateLine T m A hA).obj.map f
        (Scheme.finiteEtaleTateOneGenerator A m T hA W a z) =
      Scheme.finiteEtaleTateOneGenerator A m T hA V a
        ((T.rootsOfUnitySheaf m).obj.map f z) := by
  unfold Scheme.finiteEtaleTateOneGenerator
  exact (ConcreteCategory.congr_hom
    ((toSheafify T.smallEtaleTopology
      (Scheme.finiteEtaleMuModulePresheaf T m ⋙
        ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar m A hA))).naturality f)
      (a ⊗ₜ[ZMod m, Scheme.finiteEtaleTwistScalar m A hA]
        (show Scheme.finiteEtaleMuModuleObj T m W from z))).symm

private theorem abelianPullback_transpose (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {X Y : Scheme.{u}} (v : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
        (relativeKummerAbelianPullback A m hm hA v hY hX) =
      (RawModuleScalarComparison.forget A Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
          ((Scheme.finiteEtaleTwistPullbackData A m hm hA).c v hY hX 1).hom) := by
  rw [relativeKummerAbelianPullback, Adjunction.homEquiv_naturality_right]
  dsimp only [RawModuleScalarComparison.pullbackIso, Iso.symm_inv,
    moduleAbelianUpperStarIso, asIso_hom, moduleAbelianUpperStarComparison]
  erw [Equiv.apply_symm_apply]
  rfl

private theorem root_constant_square (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {k : Type u} [Field k] {ζ : k} (hζ : IsPrimitiveRoot ζ m)
    {X Y : Scheme.{u}} (v : X ⟶ Y) (p : Y ⟶ Spec (.of k))
    (hY : IsUnit (m : Γ(Y, ⊤))) :
    letI : NeZero m := ⟨ne_of_gt hm⟩
    (upperStar AddCommGrpCat.{u + 1} v).map
        (Y.constantZModIsoRootsOfUnitySheaf m p hζ).hom ≫
      ((Scheme.finiteEtaleTwistPullbackData A m hm hA).r v hY).hom =
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} v).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))) ≫
      (X.constantZModIsoRootsOfUnitySheaf m (v ≫ p) hζ).hom := by
  let : NeZero m := ⟨ne_of_gt hm⟩
  have hr : ((Scheme.finiteEtaleTwistPullbackData A m hm hA).r v hY).hom =
      Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf m v := by
    apply (cancel_mono (kernel.ι (m • 𝟙 X.gmSheaf))).1
    exact ((Scheme.finiteEtaleTwistPullbackData A m hm hA).laws.2.1 v hY).symm.trans
      (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι m v).symm
  rw [hr]
  simp only [Scheme.constantZModIsoRootsOfUnitySheaf, asIso_hom]
  rw [Scheme.upperStar_map_constantZModToRootsOfUnitySheaf_comp]
  congr 2
  apply Units.ext
  change v.appTop _ = _
  rw [IsUnit.unit_spec, IsUnit.unit_spec]
  change (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop) ≫ v.appTop) ζ = _
  rw [Category.assoc, ← Scheme.Hom.comp_appTop]

/-- Pullback of the normalized degree-zero constant class along any morphism over k.
Source: blueprint latest, prop-pur-gm-relative-kummer.proof.md, Step 2;
Stacks Tags 03PK and 01EZ (blueprint: new-pur-relative-kummer-constant-pullback).

Proof: Compute the degree-zero cohomology pullback using the section comparison for
chosen terminal etale objects. The transpose of the abelian coefficient comparison is
the underlying module transpose, by the inverse-image/scalar-forgetting comparison.
The pure-tensor law for the finite-twist comparison therefore identifies the result
with the tensor of a and the pulled-back primitive root. After the monic inclusion of
roots into Gm, the root comparison agrees with ordinary pullback of the constant root:
the constant-root square follows from upperStar_map_constantZModToRootsOfUnitySheaf_comp.
The constant inverse-image comparison preserves each label, as follows from the two
constant-sheaf/terminal-section adjunction units and their uniqueness comparison.
Finally naturality of sheafification and the root trivialization along the unique map
from the chosen terminal object identifies this tensor with the specified constant
on X. This argument allows nonconnected and empty schemes and the zero coefficient ring.
-/
theorem relativeKummer_constant_pullback
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {k : Type u} [Field k] {ζ : k} (hζ : IsPrimitiveRoot ζ m)
    {X Y : Scheme.{u}} (v : X ⟶ Y) (p : Y ⟶ Spec (.of k))
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (a : A) :
    relativeKummerCohomologyPullback A m hm hA v hY hX 0
        (relativeKummerConstant A m hm hA hζ Y p a) =
      relativeKummerConstant A m hm hA hζ X (v ≫ p) a := by
  let : NeZero m := ⟨ne_of_gt hm⟩
  let hYt := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y
  let hXt := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X
  let e := (hYt.isTerminalObj v.Etale _).from (Scheme.Etale.mk (𝟙 X))
  let c := relativeKummerAbelianPullback A m hm hA v hY hX
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v
  apply (Sheaf.H.equiv₀ _ hXt).injective
  rw [relativeKummerCohomologyPullback]
  dsimp only [relativeKummerMapOnCohomology]
  change Sheaf.H.equiv₀ _ hXt
      (Sheaf.H.map c 0 (cohomologyMap v _ 0
        (relativeKummerConstant A m hm hA hζ Y p a))) = _
  have hc : (adj.homEquiv _ _).symm (adj.homEquiv _ _ c) = c :=
    Equiv.symm_apply_apply _ _
  rw [← hc]
  rw [equiv₀_map_cohomologyMap v (adj.homEquiv _ _ c) _ hXt hYt e]
  rw [relativeKummerConstant, relativeKummerConstant, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  rw [abelianPullback_transpose]
  erw [(Scheme.finiteEtaleTwistPullbackData A m hm hA).laws.2.2.1]
  erw [generator_map]
  congr 1
  let ρY := Y.constantZModIsoRootsOfUnitySheaf m p hζ
  let ρX := X.constantZModIsoRootsOfUnitySheaf m (v ≫ p) hζ
  have hsq := root_constant_square A m hm hA hζ v p hY
  have ht := congrArg ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv
    _ _) hsq
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at ht
  have hz :
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
        ((Scheme.finiteEtaleTwistPullbackData A m hm hA).r v hY).hom).hom.app
          (op (Scheme.Etale.mk (𝟙 Y))))
          (ρY.hom.hom.app _ ((toSheafify Y.smallEtaleTopology
            ((Functor.const Y.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))))).app _ (ULift.up 1))) =
        ρX.hom.hom.app _ ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))))).app
              (op (v.Etale.obj (Scheme.Etale.mk (𝟙 Y)))) (ULift.up 1)) := by
    have hw := ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f => f.hom) ht) (op (Scheme.Etale.mk (𝟙 Y))))
      ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))))).app _ (ULift.up 1))
    change _ = ρX.hom.hom.app _
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
        ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} v).hom.app _)).hom.app _ _) at hw
    rw [additiveConstantUnit_apply] at hw
    exact hw
  rw [hz]
  exact (ConcreteCategory.congr_hom
    (((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))))) ≫ ρX.hom.hom).naturality e.op)
      (ULift.up 1)).symm

end AlgebraicGeometry.Etale
