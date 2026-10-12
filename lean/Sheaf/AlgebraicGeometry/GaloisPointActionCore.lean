/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts

/-! Core action construction for geometric étale lifts. -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private noncomputable def fiberPrecomp {S : Scheme.{u}} {L M : Type u}
    [Field L] [Field M] [IsSepClosed L] [IsSepClosed M]
    (s : Spec (.of L) ⟶ S) (t : Spec (.of M) ⟶ S)
    (i : Spec (.of M) ⟶ Spec (.of L)) (h : i ≫ s = t) :
    (pointSmallEtale s).fiber ⟶ (pointSmallEtale t).fiber where
  app X := TypeCat.ofHom fun x ↦
    Over.homMk (i ≫ x.left) (by
      change (i ≫ x.left) ≫ X.hom = t
      have hx : x.left ≫ X.hom = s := Over.w x
      rw [Category.assoc, hx, h])
  naturality X Y f := by
    ext x
    apply Over.OverMorphism.ext
    change i ≫ (x.left ≫ f.left) = (i ≫ x.left) ≫ f.left
    exact (Category.assoc _ _ _).symm

private noncomputable def sepClosureAction (K Ks : Type u) [Field K] [Field Ks]
    [Algebra K Ks] [IsSepClosure K Ks] [IsSepClosed Ks] :
    Gal(Ks/K) →* End (pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))).fiber where
  toFun g := fiberPrecomp _ _ (Spec.map (CommRingCat.ofHom g.toRingHom)) (by
    rw [← Spec.map_comp]
    exact congrArg (fun c ↦ Spec.map (CommRingCat.ofHom c)) g.toAlgHom.comp_algebraMap)
  map_one' := by
    apply NatTrans.ext
    funext X
    ext x
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (AlgEquiv.refl.toRingHom)) ≫ x.left = x.left
    simp
  map_mul' g h := by
    apply NatTrans.ext
    funext X
    ext x
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (g * h).toRingHom) ≫ x.left =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        Spec.map (CommRingCat.ofHom h.toRingHom) ≫ x.left
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

/-- (blueprint: lem-exc-galois-point-action-core).

Core action-and-formula part of the geometric Galois point action theorem.

(source: Stacks Project, Tag 03QW, discussion before Theorem 59.56.3;
 blueprint: lem-exc-galois-point-action-core).

The proof extends automorphisms from a separable closure through an algebraic closure and
then a transcendence basis, and acts on geometric étale lifts by precomposition.  Factorization
through finite separable residue fields makes the result independent of the chosen extension;
functoriality of precomposition gives the monoid-homomorphism laws and the displayed formula.
-/
theorem exists_galoisPointAction_core
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K)
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let p := pointSmallEtale s
    ∃ ρ : Gal(Ks/K) →* End p.fiber,
      ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
          (_ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x : p.fiber.obj X),
        ((ρ g).app X x).left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left := by
  -- Descend lifts uniquely to Ks, act there, and transport along the fibre isomorphism.
  classical
  dsimp only
  have : IsSepClosed Ks := IsSepClosure.sep_closed K
  let sk := Spec.map (CommRingCat.ofHom (algebraMap K Ks))
  let sΩ := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let i := Spec.map (CommRingCat.ofHom (algebraMap Ks Ω))
  have hi : i ≫ sk = sΩ := by
    rw [← Spec.map_comp]
    exact congrArg (fun c ↦ Spec.map (CommRingCat.ofHom c))
      (IsScalarTower.algebraMap_eq K Ks Ω).symm
  let ε := fiberPrecomp sk sΩ i hi
  have hε (X : (Spec (.of K)).Etale) : Function.Bijective (ε.app X) := by
    constructor
    · intro x y hxy
      apply Over.OverMorphism.ext
      apply SpecMap_comp_injective (CommRingCat.ofHom (algebraMap Ks Ω))
      exact congrArg Over.Hom.left hxy
    · intro x
      obtain ⟨y, hyx, hy⟩ := X.hom.exists_SpecMap_comp_eq_of_isSepClosed
        (CommRingCat.ofHom (algebraMap Ks Ω)) sk x.left ((Over.w x).trans hi.symm)
      refine ⟨Over.homMk y hy, ?_⟩
      apply Over.OverMorphism.ext
      exact hyx
  let e : (pointSmallEtale sk).fiber ≅ (pointSmallEtale sΩ).fiber :=
    NatIso.ofComponents (fun X ↦ (Equiv.ofBijective (ε.app X) (hε X)).toIso)
      (fun f ↦ ε.naturality f)
  let a := sepClosureAction K Ks
  let ρ : Gal(Ks/K) →* End (pointSmallEtale sΩ).fiber :=
    { toFun := fun g ↦ e.inv ≫ a g ≫ e.hom
      map_one' := by
        change e.inv ≫ a 1 ≫ e.hom = 𝟙 _
        rw [map_one]
        change e.inv ≫ 𝟙 (pointSmallEtale sk).fiber ≫ e.hom = 𝟙 _
        simp
      map_mul' := by
        intro g h
        simp [map_mul, End.mul_def, Category.assoc] }
  refine ⟨ρ, ?_⟩
  intro g τ h X x
  let y := e.inv.app X x
  have hy : i ≫ y.left = x.left := by
    have he := e.inv_hom_id_app_apply X x
    exact congrArg Over.Hom.left he
  change i ≫ (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ y.left) =
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left
  rw [← hy, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun c ↦ Spec.map (CommRingCat.ofHom c) ≫ y.left) h

end AlgebraicGeometry.Scheme
