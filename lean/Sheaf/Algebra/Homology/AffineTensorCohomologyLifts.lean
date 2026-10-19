/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.Algebra.Homology.TensorActionOfAdditiveFunctor
import Sheaf.Algebra.Homology.AffineTensorCohomologyAdditiveScalar

/-! # Affine tensor cohomology: coefficient lifts

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-tensor-cohomology-lifts). -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v v'

open CategoryTheory
open scoped TensorProduct

namespace RingTensorCohomology

section
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

private noncomputable def liftMap
    (T U : ModuleCat.{u} (A ⊗[R] B))
    (f : (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj T ⟶
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj U)
    (hf : ∀ a : A, ∀ x : T,
      f ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
        (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • f x) : T ⟶ U :=
  ModuleCat.ofHom
    { toFun := f
      map_add' := f.hom.map_add
      map_smul' := by
        intro t x
        change f (t • x) = t • f x
        induction t using TensorProduct.induction_on with
        | zero => simpa using f.hom.map_zero
        | add t s ht hs => simp only [add_smul, map_add, ht, hs]
        | tmul a b =>
          have hab : (a ⊗ₜ[R] b) =
              (Algebra.TensorProduct.includeRight b : A ⊗[R] B) *
                Algebra.TensorProduct.includeLeft (S := R) a := by
            simp [Algebra.TensorProduct.includeRight, Algebra.TensorProduct.includeLeft,
              Algebra.TensorProduct.tmul_mul_tmul]
          rw [hab, mul_smul, mul_smul]
          have hB := f.hom.map_smul b
            ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x)
          change f ((Algebra.TensorProduct.includeRight b : A ⊗[R] B) •
            ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x)) =
            (Algebra.TensorProduct.includeRight b : A ⊗[R] B) •
              f ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) at hB
          rw [hB, hf] }


private theorem exists_functorLift
    {C : Type v} [Category.{v'} C] [Preadditive C] [CategoryTheory.Linear A C]
    (K : C ⥤ ModuleCat.{u} B) [K.Additive]
    (hR : ∀ M : C, ∀ r : R,
      K.map (algebraMap R A r • 𝟙 M) = algebraMap R B r • 𝟙 (K.obj M)) :
    ∃ (S : C ⥤ ModuleCat.{u} (A ⊗[R] B))
      (e : S ⋙ ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom ≅ K),
      ∀ (M : C) (a : A) (x : S.obj M),
        e.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
          K.map (a • 𝟙 M) (e.hom.app M x) := by
  classical
  choose L e he using fun M ↦ ModuleCat.tensorAction_of_additiveFunctor R A B K M (hR M)
  have hscalar (M : C) (a : A) (x : L M) :
      (e M).hom ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
        K.map (a • 𝟙 M) ((e M).hom x) :=
    congrArg (fun f ↦ f x) (he M a)
  let g {M N : C} (f : M ⟶ N) := (e M).hom ≫ K.map f ≫ (e N).inv
  have hg {M N : C} (f : M ⟶ N) (a : A) (x : L M) :
      g f ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
        (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • g f x := by
    apply (e N).toLinearEquiv.injective
    change (e N).hom (g f (_ • x)) = (e N).hom (_ • g f x)
    rw [hscalar]
    have hcomm : K.map (a • 𝟙 M) ≫ K.map f = K.map f ≫ K.map (a • 𝟙 N) := by
      rw [← K.map_comp, ← K.map_comp]
      simp
    simp only [g, ModuleCat.comp_apply,
      Iso.inv_hom_id_apply]
    rw [hscalar]
    exact congrArg (fun t ↦ t ((e M).hom x)) hcomm
  let S : C ⥤ ModuleCat.{u} (A ⊗[R] B) :=
    { obj := L
      map := fun f ↦ liftMap R A B _ _ (g f) (hg f)
      map_id := by
        intro M
        ext x
        change (e M).inv (K.map (𝟙 M) ((e M).hom x)) = x
        simp
      map_comp := by
        intro M N P f h
        ext x
        change (e P).inv (K.map (f ≫ h) ((e M).hom x)) =
          (e P).inv (K.map h ((e N).hom ((e N).inv (K.map f ((e M).hom x)))))
        simp }
  let e' : S ⋙ ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom ≅ K :=
    NatIso.ofComponents e (by
      intro M N f
      ext x
      change (e N).hom ((e N).inv (K.map f ((e M).hom x))) = K.map f ((e M).hom x)
      simp)
  exact ⟨S, e', hscalar⟩

end

/-- Tensor-algebra actions and linearity of the canonical comparison.
Source: Stacks Project, perfect.tex, Tag 0DJ8, affine proof, coefficient actions.
(blueprint: lem-pc-affine-tensor-cohomology-lifts)

Proof: Derived restriction followed by derived extension to B is additive and R-linear.
Multiplication endomorphisms of the A-complex therefore give an A-action on source
cohomology that commutes with B and agrees with its action on R. The tensor-algebra
universal property combines these actions. For the target, the ordinary identification
B tensor_R P = (A tensor_R B) tensor_A P on the functorial A-K-flat resolution gives
its tensor-algebra action. Naturality of resolution comparisons gives functoriality
of both actions. On the common K-flat span the right arrow intertwines multiplication
by A and B; the left arrow and its inverse do as well. Their composite consequently
lifts comparison to a tensor-algebra-linear natural transformation. The restriction
isomorphisms give the stated scalar and comparison equations. No localization,
boundedness or Tor independence is required; zero complexes and zero rings use the
same construction. -/
theorem exists_affineTensorCohomologyLifts
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ) :
    ∃ (S T : CochainComplex (ModuleCat.{u} A) ℤ ⥤ ModuleCat.{u} (A ⊗[R] B))
      (eS : S ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
        source R A B i)
      (eT : T ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
        target R A B i)
      (c : S ⟶ T),
      (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (x : S.obj M),
        eS.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
          (source R A B i).map (a • 𝟙 M) (eS.hom.app M x)) ∧
      (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (x : T.obj M),
        eT.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
          (target R A B i).map (a • 𝟙 M) (eT.hom.app M x)) ∧
      Functor.whiskerRight c
          (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom) ≫ eT.hom =
        eS.hom ≫ comparison R A B i := by
  classical
  obtain ⟨hsource, htarget, hRs, hRt⟩ := affineTensorCohomology_additive_scalar R A B i
  have := hsource
  have := htarget
  obtain ⟨S, eS, hS⟩ := exists_functorLift R A B (source R A B i) hRs
  obtain ⟨T, eT, hT⟩ := exists_functorLift R A B (target R A B i) hRt
  let U := ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let g (M : CochainComplex (ModuleCat.{u} A) ℤ) :=
    eS.hom.app M ≫ (comparison R A B i).app M ≫ eT.inv.app M
  have hg (M : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (x : S.obj M) :
      g M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
        @SMul.smul (A ⊗[R] B) (T.obj M) _
          (Algebra.TensorProduct.includeLeft (S := R) a) (g M x) := by
    apply (eT.app M).toLinearEquiv.injective
    change eT.hom.app M (g M (_ • x)) =
      eT.hom.app M (@SMul.smul (A ⊗[R] B) (T.obj M) _ _ (g M x))
    erw [hT]
    have hinv (z : (target R A B i).obj M) :
        eT.hom.app M (eT.inv.app M z) = z := Iso.inv_hom_id_apply (eT.app M) z
    simp only [g, ModuleCat.comp_apply, hinv]
    rw [hS]
    simpa only [ModuleCat.comp_apply] using
      congrArg (fun t ↦ t (eS.hom.app M x))
        ((comparison R A B i).naturality (a • 𝟙 M))
  let app (M : CochainComplex (ModuleCat.{u} A) ℤ) : S.obj M ⟶ T.obj M :=
    liftMap R A B _ _ (g M) (hg M)
  have happ (M : CochainComplex (ModuleCat.{u} A) ℤ) :
      U.map (app M) ≫ eT.hom.app M = eS.hom.app M ≫ (comparison R A B i).app M := by
    ext x
    change eT.hom.app M (eT.inv.app M ((comparison R A B i).app M (eS.hom.app M x))) = _
    exact Iso.inv_hom_id_apply (eT.app M) _
  let c : S ⟶ T :=
    { app := app
      naturality := by
        intro M N f
        apply U.map_injective
        apply (cancel_mono (eT.hom.app N)).1
        rw [Functor.map_comp, Functor.map_comp]
        simp only [Category.assoc]
        have hnatT : U.map (T.map f) ≫ eT.hom.app N =
            eT.hom.app M ≫ (target R A B i).map f := eT.hom.naturality f
        rw [happ, hnatT]
        rw [← Category.assoc (U.map (app M)), happ]
        rw [Category.assoc, ← (comparison R A B i).naturality f]
        have hnatS : U.map (S.map f) ≫ eS.hom.app N =
            eS.hom.app M ≫ (source R A B i).map f := eS.hom.naturality f
        rw [← Category.assoc (U.map (S.map f)), hnatS]
        simp only [Category.assoc] }
  refine ⟨S, T, eS, eT, c, hS, hT, ?_⟩
  apply NatTrans.ext
  funext M
  exact happ M


end RingTensorCohomology
