/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackEquivariant
import Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality

/-!
# Naturality of the Picard identification with étale cohomology

Source: Stacks Project, Cohomology on Sites, Tag 040E, Lemma 21.6.1, and functoriality
of cohomology under pullback (blueprint: lem-sc-h1-gm-pic-pullback).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

private theorem terminal_naturality.{v, w}
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w}) {T S : C}
    (hT : Limits.IsTerminal T) (hS : Limits.IsTerminal S) (x : Sheaf.H F 0) :
    F.obj.map (hT.from S).op (Sheaf.H.equiv₀ F hT x) = Sheaf.H.equiv₀ F hS x := by
  let φ := (sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv _ F
    (Abelian.Ext.addEquiv₀ x)
  change F.obj.map (hT.from S).op (φ.app (op T) (ULift.up (1 : ℤ))) =
    φ.app (op S) (ULift.up (1 : ℤ))
  exact (ConcreteCategory.congr_hom (φ.naturality (hT.from S).op)
    (ULift.up (1 : ℤ))).symm

private theorem torsor_terminal_independent.{v, w}
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt (Sheaf J AddCommGrpCat.{w})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (G : Sheaf J AddCommGrpCat.{w}) {T S : C}
    (hT : Limits.IsTerminal T) (hS : Limits.IsTerminal S) (P : Sheaf.Torsor G) :
    Sheaf.Torsor.classH1 G hT ⟦P⟧ = Sheaf.Torsor.classH1 G hS ⟦P⟧ := by
  let seq := Sheaf.Torsor.injectiveSequence G
  have hs := Sheaf.Torsor.injectiveSequence_shortExact G
  obtain ⟨s, he⟩ := Sheaf.Torsor.exists_equiv_lifts hT hs P
  let s' := seq.X₃.obj.map (hT.from S).op s
  have hm (U : Cᵒᵖ) :
      seq.X₃.obj.map (hS.from U.unop).op s' =
        seq.X₃.obj.map (hT.from U.unop).op s := by
    dsimp [s']
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact congrArg (fun f ↦ seq.X₃.obj.map f.op s) (hT.hom_ext _ _)
  let σ : (Sheaf.Torsor.lifts hT hs s).sheaf ⟶
      (Sheaf.Torsor.lifts hS hs s').sheaf :=
    ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦ ⟨x.1, by
         change seq.g.hom.app U x.1 = _
         rw [hm]
         exact x.2⟩)
       naturality := fun _ _ _ ↦ by ext x; rfl }⟩
  have he' : Sheaf.Torsor.lifts hT hs s ≈ Sheaf.Torsor.lifts hS hs s' :=
    ⟨Sheaf.Torsor.Iso.ofHom σ (fun _ _ _ ↦ Subtype.ext rfl)⟩
  rw [Quotient.sound he, Quotient.sound he', Sheaf.Torsor.classH1_lifts]
  rw [← Quotient.sound he', Sheaf.Torsor.classH1_lifts]
  rw [Sheaf.H.δ_apply, Sheaf.H.δ_apply]
  congr 1
  apply (Sheaf.H.equiv₀ seq.X₃ hS).injective
  rw [AddEquiv.apply_symm_apply, ← terminal_naturality seq.X₃ hT hS]
  rw [AddEquiv.apply_symm_apply]

private theorem classH1_map_of_hom.{v, w}
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt (Sheaf J AddCommGrpCat.{w})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {T : C} (hT : Limits.IsTerminal T) {G G' : Sheaf J AddCommGrpCat.{w}}
    (φ : G ⟶ G') (P : Sheaf.Torsor G) (P' : Sheaf.Torsor G')
    (σ : P.sheaf ⟶ P'.sheaf)
    (hσ : ∀ U a t, σ.hom.app U (P.vadd U a t) =
      P'.vadd U (φ.hom.app U a) (σ.hom.app U t)) :
    Sheaf.H.map φ 1 (Sheaf.Torsor.classH1 G hT ⟦P⟧) =
      Sheaf.Torsor.classH1 G' hT ⟦P'⟧ := by
  symm
  refine Sheaf.Torsor.classH1_eq_map_of_equivariant hT φ P P'
    (fun U ↦ σ.hom.app U) ?_ hσ
  intro U V f t
  exact (NatTrans.naturality_apply σ.hom f t).symm


/-- The canonical Picard identification intertwines tensor pullback with cohomology
pullback followed by the adjoint comparison `u⁻¹ Gₘ → Gₘ`. In degree zero this composite
is pullback of global units. The existential invertibility witness makes the class of
`u*L` well typed without adding an invertibility assumption on the pullback.
The Picard equivalence sends `L` to the class of its étale torsor `Isom(O,L)`, so the
first clause is also precisely the asserted equality of torsor classes.

Source: Stacks Project, Tag 040E (blueprint: lem-sc-h1-gm-pic-pullback).

Proof:
1. By lem-sc-h1-gm-pic and lem-sc-torsor-h1, the class of `L` is represented by
   the étale torsor `T_L = Isom(O_X,L)`.
2. Pullback sends a local generator `s` to `1 ⊗ s`. This is equivariant for the
   comparison of units, since `1 ⊗ fs = c_u(f)(1 ⊗ s)` (def-pc-module-pullback,
   def-weil-pbc-inverse-image). On a trivializing cover this identifies the
   contracted product of `u⁻¹T_L` with `Gₘ,Y` with `T_{u*L}` (Stacks Tag 03AH).
3. The two clauses of lem-sc-etale-torsor-h1-functoriality send torsor classes
   first to inverse-image torsors and then to their contracted products.
   Naturality of cohomology (lem-weil-pbc-cohomology-pullback-functorial) and
   lem-sc-h1-gm-pic therefore identify the composite with `[L] ↦ [u*L]`.
4. By lem-weil-pbc-cohomology-pullback-degree-zero, the degree-zero pullback is
   the adjunction unit on global sections. Composing with the adjoint comparison
   of units gives the map on units induced by `u.appTop`. -/
theorem picard_cohomology_pullback
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k'))]
    [IsCurve (X ↘ Spec (.of k))] [IsCurve (Y ↘ Spec (.of k'))] (u : Y ⟶ X) :
    (∀ (L : X.Modules) [L.IsInvertible],
      ∃ h : ((Modules.tensorPullback u).obj L).IsInvertible,
        Sheaf.H.map (upperStarGmSheafToGmSheaf u) 1
          (Etale.cohomologyMap u X.gmSheaf 1
            (Pic.toCohomologicalPicardGroup X (Pic.ofIsInvertible L))) =
        Pic.toCohomologicalPicardGroup Y
          (@Pic.ofIsInvertible Y ((Modules.tensorPullback u).obj L) h)) ∧
    (∀ a : Γ(X, ⊤)ˣ,
      Sheaf.H.equiv₀ Y.gmSheaf (MorphismProperty.Over.mkIdTerminal @Etale Y)
        (Sheaf.H.map (upperStarGmSheafToGmSheaf u) 0
          (Etale.cohomologyMap u X.gmSheaf 0
            ((Sheaf.H.equiv₀ X.gmSheaf
              (MorphismProperty.Over.mkIdTerminal @Etale X)).symm
                (ULift.up (Additive.ofMul a))))) =
        ULift.up (Additive.ofMul (Units.map u.appTop.hom.toMonoidHom a))) := by
  constructor
  · intro L hL
    obtain ⟨adj⟩ := Modules.nonempty_tensorPullbackAdjunction u
    let e := ((Modules.pullbackPushforwardAdjunction u).leftAdjointUniq adj).app L
    let : ((Modules.tensorPullback u).obj L).IsInvertible :=
      Modules.IsInvertible.of_iso e
    have := Modules.IsInvertible.sheafOfModules_isInvertible L
    have := Modules.IsInvertible.sheafOfModules_isInvertible
      ((Modules.tensorPullback u).obj L)
    obtain ⟨T', eT, heT, hT⟩ := Sheaf.Torsor.etale_torsor_h1_functoriality.1
      X Y u X.gmSheaf (Modules.etaleIsoTorsor L)
    obtain ⟨σ, hσ⟩ := Modules.etale_generators_pullback_equivariant u L T' eT heT
    refine ⟨inferInstance, ?_⟩
    change _ = Pic.toCohomologicalPicardGroup Y (Pic.mk _)
    change Sheaf.H.map _ 1
      (Etale.cohomologyMap u X.gmSheaf 1
        (Pic.toCohomologicalPicardGroup X (Pic.mk L))) = _
    rw [Pic.toCohomologicalPicardGroup_apply, Pic.etaleTorsorClass_mk,
      Pic.toCohomologicalPicardGroup_apply, Pic.etaleTorsorClass_mk]
    rw [torsor_terminal_independent X.gmSheaf
      (MorphismProperty.Over.mkIdTerminal @Etale X) Limits.terminalIsTerminal, hT]
    rw [torsor_terminal_independent Y.gmSheaf
      (MorphismProperty.Over.mkIdTerminal @Etale Y) Limits.terminalIsTerminal]
    exact classH1_map_of_hom Limits.terminalIsTerminal (upperStarGmSheafToGmSheaf u)
      T' (Modules.etaleIsoTorsor ((Modules.tensorPullback u).obj L)) σ hσ
  · intro a
    let hX := MorphismProperty.Over.mkIdTerminal @Etale X
    let hY := MorphismProperty.Over.mkIdTerminal @Etale Y
    let b := X.gmSheaf.obj.map (hX.from (⊤_ X.Etale)).op (ULift.up (Additive.ofMul a))
    let e := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
      Limits.terminalIsTerminal
    let g := e.inv.app X.gmSheaf b
    have hb : (Sheaf.H.equiv₀ X.gmSheaf Limits.terminalIsTerminal).symm b =
        (Sheaf.H.equiv₀ X.gmSheaf hX).symm (ULift.up (Additive.ofMul a)) := by
      apply (Sheaf.H.equiv₀ X.gmSheaf Limits.terminalIsTerminal).injective
      rw [AddEquiv.apply_symm_apply, ← terminal_naturality X.gmSheaf hX]
      rw [AddEquiv.apply_symm_apply]
    have h := Etale.cohomologyMap_zero_eq_globalSectionsUpperStarMap u X.gmSheaf g
    simp only [g, e, ← ConcreteCategory.comp_apply, Iso.inv_hom_id_app,
      ConcreteCategory.id_apply] at h
    rw [← hb, h, Sheaf.H.equiv₀_symm_naturality]
    rw [← terminal_naturality Y.gmSheaf Limits.terminalIsTerminal hY]
    rw [AddEquiv.apply_symm_apply]
    simp only [Etale.globalSectionsUpperStarMap, ConcreteCategory.comp_apply]
    simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app,
      ConcreteCategory.id_apply]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    let c := upperStarGmSheafToGmSheaf u
    let η := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).unit
    let U := (Etale.upperStar AddCommGrpCat.{u + 1} u).obj X.gmSheaf
    change Y.gmSheaf.obj.map (Limits.terminalIsTerminal.from (Etale.mk (𝟙 Y))).op
      (c.hom.app (op (⊤_ Y.Etale))
        (U.obj.map (Limits.PreservesTerminal.iso u.Etale).inv.op
          ((η.app X.gmSheaf).hom.app (op (⊤_ X.Etale)) b))) = _
    rw [NatTrans.naturality_apply c.hom]
    have hu := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).homEquiv
      X.gmSheaf Y.gmSheaf |>.apply_symm_apply (gmSheafToLowerStarGmSheaf u)
    change η.app X.gmSheaf ≫ (Etale.lowerStar AddCommGrpCat.{u + 1} u).map c =
      gmSheafToLowerStarGmSheaf u at hu
    have huv := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app (op (⊤_ X.Etale))) hu) b
    change c.hom.app _ ((η.app X.gmSheaf).hom.app _ b) =
      (gmSheafToLowerStarGmSheaf u).hom.app _ b at huv
    erw [huv]
    dsimp only [b]
    rw [NatTrans.naturality_apply (gmSheafToLowerStarGmSheaf u).hom]
    let p := MorphismProperty.Over.pullback @Etale ⊤ u
    let m : Etale.mk (𝟙 Y) ⟶ p.obj (Etale.mk (𝟙 X)) :=
      Limits.terminalIsTerminal.from (Etale.mk (𝟙 Y)) ≫
        (Limits.PreservesTerminal.iso u.Etale).inv ≫ p.map (hX.from (⊤_ X.Etale))
    change Y.gmSheaf.obj.map (Limits.terminalIsTerminal.from (Etale.mk (𝟙 Y))).op
      (Y.gmSheaf.obj.map (Limits.PreservesTerminal.iso u.Etale).inv.op
        (Y.gmSheaf.obj.map (p.map (hX.from (⊤_ X.Etale))).op
          ((gmSheafToLowerStarGmSheaf u).hom.app (op (Etale.mk (𝟙 X)))
            (ULift.up (Additive.ofMul a))))) = _
    erw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    change Y.gmSheaf.obj.map m.op
      ((gmSheafToLowerStarGmSheaf u).hom.app (op (Etale.mk (𝟙 X)))
        (ULift.up (Additive.ofMul a))) = _
    have hm : m.left ≫ Limits.pullback.fst (𝟙 X) u = u := by
      have hf : Limits.pullback.fst (𝟙 X) u = Limits.pullback.snd (𝟙 X) u ≫ u := by
        simpa using (Limits.pullback.condition (f := 𝟙 X) (g := u))
      rw [hf, ← Category.assoc]
      have hw : m.left ≫ Limits.pullback.snd (𝟙 X) u = 𝟙 Y := m.w
      erw [hw, Category.id_comp]
    apply ULift.ext
    apply Additive.toMul.injective
    apply Units.ext
    change m.left.appTop ((Limits.pullback.fst (𝟙 X) u).appTop (a : Γ(X, ⊤))) =
      u.appTop (a : Γ(X, ⊤))
    erw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hm]
    rfl


end AlgebraicGeometry.Scheme
