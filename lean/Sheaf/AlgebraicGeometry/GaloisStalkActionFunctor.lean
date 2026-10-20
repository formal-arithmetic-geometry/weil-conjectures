/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
import Sheaf.AlgebraicGeometry.GaloisPointAction
import Mathlib.CategoryTheory.Sites.Point.Category
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The canonical Galois action functor on geometric stalks

Source: Stacks Project, Tag 03QW.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
/-- Source: Stacks Project, Tag 03QW, section-galois-action-stalks.
(blueprint: lem-exc-galois-stalk-action-functor).

The geometric stalk lifts to discrete continuous Galois actions; no full faithfulness
or essential surjectivity is asserted here.

Proof: Every germ is represented by a section on a pointed etale neighbourhood.
For g in Gal(Ks/K), extend g to a K-automorphism of Omega and precompose the pointed
lift with its spectrum. Such an extension exists: extend g first to the algebraic
closure of K in Omega, fix a transcendence basis, and extend to its algebraic closure.
The residue field of the lifted point is finite separable over K, so its image in
Omega lies in the image of Ks. Thus the new lift is independent of the extension.
Changing a representative by an etale restriction commutes with this operation,
which therefore descends to the stalk colimit. Precomposition and contravariance of
Spec give the identity and multiplication laws for a left action. A representative
has stabilizer containing the subgroup fixing its finite separable residue-field
image; this subgroup is open. Hence all stabilizers are open, which gives continuity
for the discrete topology. Sheaf morphisms act on the section in a representative
and commute with changes of lift, so their stalk maps are equivariant. Use these
objects and maps to define T. Their underlying sets and maps are the stalk functor,
giving the natural isomorphism j. The definition on representatives is the formula
below. Only finite separable residue-field images are used, so transcendental
extensions Omega and separably closed or imperfect base fields cause no change. -/
theorem exists_galoisStalkActionFunctor
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K)
    let J := S.smallEtaleTopology
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let p := pointSmallEtale s
    let G := Gal(Ks/K)
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type (max (u + 1) v)) (G := G))
      ⋙ ObjectProperty.ι (Action.IsContinuous (V := Type (max (u + 1) v)) (G := G))
    ∃ (T : Sheaf J (Type (max (u + 1) v)) ⥤
        DiscreteContAction (Type (max (u + 1) v)) G)
      (j : T ⋙ V ⋙ Action.forget (Type (max (u + 1) v)) G ≅ p.sheafFiber),
      ∀ (F : Sheaf J (Type (max (u + 1) v))) (g : G)
          (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (j.hom.app F) ((T.obj F).obj.obj.ρ g
          ((j.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z := by
  classical
  dsimp only
  let S := Spec (.of K)
  let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let p := pointSmallEtale s
  let G := Gal(Ks/K)
  let W := Type (max (u + 1) v)
  obtain ⟨ρ, hρ, hopen⟩ := exists_galoisPointAction K Ks Ω
  let φ (g : G) : p ⟶ p := ⟨ρ g⟩
  let η (g : G) : p.sheafFiber (A := W) ⟶ p.sheafFiber := (φ g).sheafFiber
  have hη_one : η 1 = 𝟙 _ := by
    have h : φ 1 = 𝟙 p := by
      apply GrothendieckTopology.Point.hom_ext
      exact ρ.map_one
    simp only [η, h, GrothendieckTopology.Point.Hom.sheafFiber_id]
  have hη_mul (g h : G) : η (g * h) = η h ≫ η g := by
    have heq : φ (g * h) = φ g ≫ φ h := by
      apply GrothendieckTopology.Point.hom_ext
      exact ρ.map_mul g h
    simp only [η, heq, GrothendieckTopology.Point.Hom.sheafFiber_comp]
  have hη_germ (g : G) (F : Sheaf S.smallEtaleTopology W)
      (X : S.Etale) (x : p.fiber.obj X) (z : F.obj.obj (op X)) :
      (η g).app F (p.toPresheafFiber X x F.obj z) =
        p.toPresheafFiber X ((ρ g).app X x) F.obj z := by
    let hc : ∀ ⦃Y Z : S.Etale⦄ (f : Y ⟶ Z) (y : p.fiber.obj Y),
        F.obj.map f.op ≫ p.toPresheafFiber Y ((ρ g).app Y y) F.obj =
          p.toPresheafFiber Z ((ρ g).app Z (p.fiber.map f y)) F.obj := by
      intro Y Z f y
      rw [p.toPresheafFiber_w]
      congr 1
      exact ((ρ g).naturality_apply f y).symm
    change (p.toPresheafFiber X x F.obj ≫
      p.presheafFiberDesc (fun Y y ↦ p.toPresheafFiber Y ((ρ g).app Y y) F.obj) hc) z = _
    rw [p.toPresheafFiber_presheafFiberDesc
      (fun Y y ↦ p.toPresheafFiber Y ((ρ g).app Y y) F.obj) hc X x]
  let A : Sheaf S.smallEtaleTopology W ⥤ Action W G :=
    { obj := fun F ↦
        { V := p.sheafFiber.obj F
          ρ :=
            { toFun := fun g ↦ (η g).app F
              map_one' := congrArg (fun t ↦ t.app F) hη_one
              map_mul' := fun g h ↦ congrArg (fun t ↦ t.app F) (hη_mul g h) } }
      map := fun f ↦ { hom := p.sheafFiber.map f, comm := fun g ↦ ((η g).naturality f).symm } }
  have hcont (F : Sheaf S.smallEtaleTopology W) : (A.obj F).IsContinuous := by
    have : DiscreteTopology ((forget₂ (Action W G) TopCat).obj (A.obj F)) :=
      inferInstanceAs (DiscreteTopology (TopCat.discrete.obj (p.sheafFiber.obj F)))
    apply continuousSMul_iff_stabilizer_isOpen.mpr
    intro y
    obtain ⟨X, x, z, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := F.obj) y
    let : MulAction G (p.fiber.obj X) :=
      { smul := fun g x ↦ (ρ g).app X x
        one_smul := fun x ↦ by
          change (ρ 1).app X x = x
          rw [ρ.map_one]
          rfl
        mul_smul := fun g h x ↦ by
          change (ρ (g * h)).app X x = (ρ g).app X ((ρ h).app X x)
          rw [ρ.map_mul]
          rfl }
    have hb : IsOpen (MulAction.stabilizer G
        x : Set G) := hopen X x
    apply Subgroup.isOpen_mono (H₁ := MulAction.stabilizer G
      x) ?_ hb
    intro g hg
    change (η g).app F (p.toPresheafFiber X x F.obj z) = p.toPresheafFiber X x F.obj z
    rw [hη_germ]
    change (ρ g).app X x = x at hg
    rw [hg]
  let C : Sheaf S.smallEtaleTopology W ⥤ ContAction W G :=
    ObjectProperty.lift _ A hcont
  let T : Sheaf S.smallEtaleTopology W ⥤ DiscreteContAction W G :=
    ObjectProperty.lift _ C (fun F ↦
      inferInstanceAs (DiscreteTopology (TopCat.discrete.obj (p.sheafFiber.obj F))))
  refine ⟨T, Iso.refl _, ?_⟩
  intro F g τ hτ X x x' hx z
  change (η g).app F (p.toPresheafFiber X x F.obj z) = p.toPresheafFiber X x' F.obj z
  rw [hη_germ]
  have heq : (ρ g).app X x = x' := by
    apply Over.OverMorphism.ext
    exact (hρ g τ hτ X x).trans hx.symm
  rw [heq]

end AlgebraicGeometry.Scheme
