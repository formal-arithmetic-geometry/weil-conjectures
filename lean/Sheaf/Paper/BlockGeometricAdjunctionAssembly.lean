/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SystemBlockConstructions
public import Sheaf.Paper.SemilinearOrdinaryDirectSystem

/-! # Assembly of the repeated ordinary geometric adjunction

Source: Zheng Construction 4.1 and the paragraph preceding Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe c v r u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ u h
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections

private theorem blockSystemHomExt
    {D : Type c} [Category.{v} D] [EssentiallySmall.{max c v r} D]
    (K : GrothendieckTopology D) (F : ℕ → Sheaf K CommRingCat.{max c v r})
    (σ : ∀ n, F (n + 1) ⟶ F n) {M N : Systems K F σ} {f g : M ⟶ N}
    (h : ∀ n, (evaluation K F σ n).map f = (evaluation K F σ n).map g) : f = g := by
  ext X x
  exact congrArg (fun q ↦ q.val.app (op X.unop.2) x) (h X.unop.1)

private theorem blockEvaluationTranspose
    {X : Type u₁} {Y : Type u₂} {x : Type u₃} {y : Type u₄}
    [Category.{v₁} X] [Category.{v₂} Y] [Category.{v₃} x] [Category.{v₄} y]
    {E : X ⥤ x} {F : Y ⥤ y} {L : X ⥤ Y} {R : Y ⥤ X}
    {l : x ⥤ y} {q : y ⥤ x} (adj : L ⊣ R) (level : l ⊣ q)
    (eL : L ⋙ F ≅ E ⋙ l) (eR : R ⋙ E ≅ F ⋙ q)
    (hunit : ∀ M, E.map (adj.unit.app M) ≫ eR.hom.app (L.obj M) ≫
      q.map (eL.hom.app M) = level.unit.app (E.obj M))
    {M : X} {N : Y} (f : L.obj M ⟶ N) :
    E.map (adj.homEquiv _ _ f) ≫ eR.hom.app N =
      level.homEquiv _ _ (eL.inv.app M ≫ F.map f) := by
  rw [adj.homEquiv_unit, level.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hr := eR.hom.naturality f
  dsimp only [Functor.comp_map] at hr
  rw [hr]
  have hu : E.map (adj.unit.app M) ≫ eR.hom.app (L.obj M) =
      level.unit.app (E.obj M) ≫ q.map (eL.inv.app M) := by
    rw [← hunit M]
    simp only [Category.assoc, ← q.map_comp, Iso.hom_inv_id_app]
    erw [q.map_id, Category.comp_id]
  rw [← Category.assoc, hu, Category.assoc]

private theorem blockCoreAdjunction
    {D : Type c} [Category.{v} D] [EssentiallySmall.{max c v r} D]
    {D' : Type c} [Category.{v} D'] [EssentiallySmall.{max c v r} D']
    (K₀ : GrothendieckTopology D) (B : ℕ → Sheaf K₀ CommRingCat.{max c v r})
    (τ : ∀ n, B (n + 1) ⟶ B n) (K₁ : GrothendieckTopology D')
    (u : Sheaf K₀ (Type (max c v r)) ⥤ Sheaf K₁ (Type (max c v r)))
    (F : ℕ → Sheaf K₁ CommRingCat.{max c v r}) (σ : ∀ n, F (n + 1) ⟶ F n)
    (I : ∀ n, SheafOfModules.AlgebraicInverseImage u (B n) (F n))
    (P : OrdinaryInverseSystem.{c, v, r} K₀ B τ K₁ u F σ I)
    (V : ∀ n, Mod K₁ (F n) ⥤ Mod K₀ (B n)) (a : ∀ n, (I n).modules ⊣ V n)
    (K : OrdinaryDirectSystemCore.{c, v, r} K₀ B τ K₁ u F σ I P V a) :
    ∃ adj : P.pull ⊣ K.push, ∀ M N (f : P.pull.obj M ⟶ N) n,
      (evaluation K₀ B τ n).map (adj.homEquiv M N f) ≫ (K.component n).hom.app N =
        (a n).homEquiv _ _ ((P.component n).inv.app M ≫ (evaluation K₁ F σ n).map f) := by
  obtain ⟨H⟩ := ordinaryDirectSystem_homData_exists.{c, v, r} K₀ B τ K₁ u F σ I P V a K
  have hleft {M M'} (f : M ⟶ M') N (g : P.pull.obj M' ⟶ N) :
      H.homEquiv M N (P.pull.map f ≫ g) = f ≫ H.homEquiv M' N g := by
    apply blockSystemHomExt.{c, v, r} K₀ B τ
    intro n
    apply (cancel_mono ((K.component n).hom.app N)).mp
    rw [H.homEquiv_component]
    simp only [Functor.map_comp, Category.assoc]
    rw [H.homEquiv_component]
    have hn := (P.component n).inv.naturality f
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, ← hn, Category.assoc, (a n).homEquiv_naturality_left]
  have hright M {N N'} (f : P.pull.obj M ⟶ N) (g : N ⟶ N') :
      H.homEquiv M N' (f ≫ g) = H.homEquiv M N f ≫ K.push.map g := by
    apply blockSystemHomExt.{c, v, r} K₀ B τ
    intro n
    apply (cancel_mono ((K.component n).hom.app N')).mp
    rw [H.homEquiv_component]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (K.component n).hom.naturality g
    dsimp only [Functor.comp_map] at hn
    rw [hn, ← Category.assoc ((evaluation K₀ B τ n).map (H.homEquiv M N f)),
      H.homEquiv_component]
    simp only [Functor.map_comp, Category.assoc, (a n).homEquiv_naturality_right]
  let adj : P.pull ⊣ K.push := Adjunction.mkOfHomEquiv
    { homEquiv := H.homEquiv
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        apply (H.homEquiv M N).injective
        rw [Equiv.apply_symm_apply, hleft, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f g ↦ hright _ f g }
  refine ⟨adj, ?_⟩
  intro M N f n
  simpa only [adj, Adjunction.mkOfHomEquiv_homEquiv] using H.homEquiv_component M N f n

private theorem blockComponentTranspose
    {X Y Xd Yd x y : Type u} [Category.{h} X] [Category.{h} Y]
    [Category.{h} Xd] [Category.{h} Yd] [Category.{h} x] [Category.{h} y]
    {L : X ⥤ Y} {R : Y ⥤ X} {Ld : Xd ⥤ Yd} {Rd : Yd ⥤ Xd}
    {E : X ⥤ x} {F : Y ⥤ y} {Ed : Xd ⥤ x} {Fd : Yd ⥤ y}
    {l : x ⥤ y} {q : y ⥤ x} {rX : Y ⥤ Yd} {rY : X ⥤ Xd}
    (adj : L ⊣ R) (a : l ⊣ q)
    (eL : L ⋙ F ≅ E ⋙ l) (eR : R ⋙ E ≅ F ⋙ q)
    (dL : Ld ⋙ Fd ≅ Ed ⋙ l) (dR : Rd ⋙ Ed ≅ Fd ⋙ q)
    (rx : rX ⋙ Fd ≅ F) (ry : rY ⋙ Ed ≅ E)
    (δ : L ⋙ rX ≅ rY ⋙ Ld) (s : rX ⋙ Rd ≅ R ⋙ rY)
    (hunit : ∀ M, E.map (adj.unit.app M) ≫ eR.hom.app (L.obj M) ≫
      q.map (eL.hom.app M) = a.unit.app (E.obj M))
    (M : X) (N : Y) (f : L.obj M ⟶ N) (g : rY.obj M ⟶ Rd.obj (rX.obj N))
    (hp : Fd.map (δ.hom.app M) ≫ dL.hom.app (rY.obj M) ≫
      l.map (ry.hom.app M) = rx.hom.app (L.obj M) ≫ eL.hom.app M)
    (hq : Ed.map (s.hom.app N) ≫ ry.hom.app (R.obj N) ≫ eR.hom.app N =
      dR.hom.app (rX.obj N) ≫ q.map (rx.hom.app N))
    (hg : Ed.map g ≫ dR.hom.app (rX.obj N) =
      a.homEquiv _ _ (dL.inv.app (rY.obj M) ≫ Fd.map (δ.inv.app M ≫ rX.map f))) :
    Ed.map g = Ed.map (rY.map (adj.homEquiv M N f) ≫ s.inv.app N) := by
  have hi : dL.inv.app (rY.obj M) ≫ Fd.map (δ.inv.app M) ≫ rx.hom.app (L.obj M) =
      l.map (ry.hom.app M) ≫ eL.inv.app M := by
    apply (cancel_mono (eL.hom.app M)).mp
    rw [Category.assoc, Category.assoc, ← hp]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [Fd.map_id, Category.id_comp]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
  apply (cancel_mono (dR.hom.app (rX.obj N))).mp
  apply (cancel_mono (q.map (rx.hom.app N))).mp
  rw [hg]
  simp only [Functor.map_comp, Category.assoc]
  rw [← a.homEquiv_naturality_right]
  have hn := rx.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [hn]
  have hf := congrArg (fun k ↦ k ≫ F.map f) hi
  simp only [Category.assoc] at hf
  rw [hf, a.homEquiv_naturality_left,
    ← blockEvaluationTranspose adj a eL eR hunit f]
  have hr := ry.hom.naturality (adj.homEquiv M N f)
  dsimp only [Functor.comp_map] at hr
  rw [← Category.assoc, ← hr, Category.assoc]
  congr 1
  apply (cancel_epi (Ed.map (s.hom.app N))).mp
  simpa only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] using hq

private theorem blockAdjunctionSquares
    {X Y Xd Yd : Type u} [Category.{h} X] [Category.{h} Y]
    [Category.{h} Xd] [Category.{h} Yd]
    {L : X ⥤ Y} {R : Y ⥤ X} {Ld : Xd ⥤ Yd} {Rd : Yd ⥤ Xd}
    {rX : Y ⥤ Yd} {rY : X ⥤ Xd} (adj : L ⊣ R) (adjd : Ld ⊣ Rd)
    (δ : L ⋙ rX ≅ rY ⋙ Ld) (s : rX ⋙ Rd ≅ R ⋙ rY)
    (hh : ∀ M N (f : L.obj M ⟶ N),
      adjd.homEquiv _ _ (δ.inv.app M ≫ rX.map f) =
        rY.map (adj.homEquiv M N f) ≫ s.inv.app N) :
    (∀ M, rY.map (adj.unit.app M) ≫ s.inv.app (L.obj M) ≫ Rd.map (δ.hom.app M) =
      adjd.unit.app (rY.obj M)) ∧
    (∀ N, Ld.map (s.inv.app N) ≫ adjd.counit.app (rX.obj N) =
      δ.inv.app (R.obj N) ≫ rX.map (adj.counit.app N)) := by
  constructor
  · intro M
    have he := hh M (L.obj M) (𝟙 _)
    erw [rX.map_id, Category.comp_id, adj.homEquiv_id] at he
    rw [← Category.assoc, ← he]
    erw [← adjd.homEquiv_naturality_right, Iso.inv_hom_id_app, adjd.homEquiv_id]
    rfl
  · intro N
    apply (adjd.homEquiv _ _).injective
    erw [adjd.homEquiv_naturality_left, ← adjd.homEquiv_symm_id,
      Equiv.apply_symm_apply, Category.comp_id, hh,
      ← adj.homEquiv_symm_id, Equiv.apply_symm_apply, rY.map_id, Category.id_comp]

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (t : SystemBlockMap)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (B₀ : ℕ → Sheaf J CommRingCat.{max c v r}) (τ₀ : ∀ n, B₀ (n + 1) ⟶ B₀ n)
  (A : Data.{c, v, r} J B₀ τ₀)
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)
  (G : Geometry.{c, v, r} J B₀ τ₀ A J' uInv uPush adjSet)
  (RX : SystemBlockRepetition J' G.coefficients G.coefficientTransition t)
  (RY : SystemBlockRepetition J B₀ τ₀ t)
  (P : OrdinaryInverseSystem.{c, v, r}
    J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) J' uInv
    (blockCoefficients G.coefficients t)
    (blockTransitions J' G.coefficients G.coefficientTransition t)
    (fun m ↦ G.inverseImage (t.index m)))
  (K : OrdinaryDirectSystemCore.{c, v, r}
    J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) J' uInv
    (blockCoefficients G.coefficients t)
    (blockTransitions J' G.coefficients G.coefficientTransition t)
    (fun m ↦ G.inverseImage (t.index m)) P
    (fun m ↦ G.levelPush (t.index m)) (fun m ↦ G.levelAdjunction (t.index m)))
  (δ : G.pull ⋙ RX.repetition ≅ RY.repetition ⋙ P.pull)
  (s : RX.repetition ⋙ K.push ≅ G.push ⋙ RY.repetition)
  (hp : ∀ (M : Systems J B₀ τ₀) (m : ℕ),
    (evaluation J' (blockCoefficients G.coefficients t)
        (blockTransitions J' G.coefficients G.coefficientTransition t) m).map (δ.hom.app M) ≫
      (P.component m).hom.app (RY.repetition.obj M) ≫
      (G.inverseImage (t.index m)).modules.map ((RY.evaluation m).hom.app M) =
    (RX.evaluation m).hom.app (G.pull.obj M) ≫
      (G.ordinaryPullEvaluation (t.index m)).hom.app M)
  (hq : ∀ (N : Systems J' G.coefficients G.coefficientTransition) (m : ℕ),
    (evaluation J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) m).map (s.hom.app N) ≫
      (RY.evaluation m).hom.app (G.push.obj N) ≫
      (G.ordinaryPushEvaluation (t.index m)).hom.app N =
    (K.component m).hom.app (RX.repetition.obj N) ≫
      (G.levelPush (t.index m)).map ((RX.evaluation m).hom.app N))

include hp hq

attribute [local irreducible] evaluation systemRing ringPresheaf rings

/-- Assemble the system adjunction and its repetition unit and counit equations
from repeated local geometric cores with normalized evaluation squares.
Source: Zheng Construction 4.1 and the paragraph preceding Lemma 4.10.
(blueprint: lem-pur-block-geometric-adjunction-assembly)
Proof: the local transition mate gives the existing component Hom equivalence.
Evaluate to prove both naturality laws, then apply Adjunction.mkOfHomEquiv.
Transpose the two normalized square equations through each level adjunction;
the original normalized system unit identifies the original transpose.
Faithful evaluations therefore give the global Hom-equivalence compatibility.
Apply that equation to an identity and to the original counit. The first yields
the unit square, and injectivity of the new Hom equivalence yields the counit
square. All these arguments are carried out by the private helpers above. -/
theorem blockGeometricAdjunctionAssembly :
    ∃ adj : P.pull ⊣ K.push,
      (∀ M : Systems J B₀ τ₀,
        RY.repetition.map (G.ordinaryAdjunction.unit.app M) ≫
            s.inv.app (G.pull.obj M) ≫ K.push.map (δ.hom.app M) =
          adj.unit.app (RY.repetition.obj M)) ∧
      (∀ N : Systems J' G.coefficients G.coefficientTransition,
        P.pull.map (s.inv.app N) ≫ adj.counit.app (RX.repetition.obj N) =
          δ.inv.app (G.push.obj N) ≫ RX.repetition.map (G.ordinaryAdjunction.counit.app N)) := by
  obtain ⟨adj, ha⟩ := blockCoreAdjunction.{c, v, r}
    J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) J' uInv
    (blockCoefficients G.coefficients t)
    (blockTransitions J' G.coefficients G.coefficientTransition t)
    (fun m ↦ G.inverseImage (t.index m)) P
    (fun m ↦ G.levelPush (t.index m)) (fun m ↦ G.levelAdjunction (t.index m)) K
  have hh M N (f : G.pull.obj M ⟶ N) :
      adj.homEquiv _ _ (δ.inv.app M ≫ RX.repetition.map f) =
        RY.repetition.map (G.ordinaryAdjunction.homEquiv M N f) ≫ s.inv.app N := by
    apply blockSystemHomExt.{c, v, r} J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t)
    intro m
    exact blockComponentTranspose
      (L := G.pull) (R := G.push) (Ld := P.pull) (Rd := K.push)
      (E := evaluation J B₀ τ₀ (t.index m))
      (F := evaluation J' G.coefficients G.coefficientTransition (t.index m))
      (Ed := evaluation J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) m)
      (Fd := evaluation J' (blockCoefficients G.coefficients t)
        (blockTransitions J' G.coefficients G.coefficientTransition t) m)
      (l := (G.inverseImage (t.index m)).modules) (q := G.levelPush (t.index m))
      (rX := RX.repetition) (rY := RY.repetition)
      G.ordinaryAdjunction (G.levelAdjunction (t.index m))
      (G.ordinaryPullEvaluation (t.index m)) (G.ordinaryPushEvaluation (t.index m))
      (P.component m) (K.component m) (RX.evaluation m) (RY.evaluation m) δ s
      (G.ordinary_unit_evaluation (t.index m)) M N f
      (adj.homEquiv _ _ (δ.inv.app M ≫ RX.repetition.map f)) (hp M m) (hq N m)
      (ha _ _ _ m)
  exact ⟨adj, blockAdjunctionSquares G.ordinaryAdjunction adj δ s hh⟩

end WeilConjectures.SemilinearSections
