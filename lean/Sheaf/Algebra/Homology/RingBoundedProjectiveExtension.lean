/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Module.Projective
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Scalar extension of bounded projective complexes on the one-object site

Source: Stacks Project, more-algebra.tex, Tag 0A6A, proof of
lemma-base-change-RHom; Tag 064K, lemma-derived-tor-quasi-isomorphism.
(blueprint: lem-pc-ring-bounded-projective-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

/-- A bounded projective complex is K-flat, and scalar extension preserves its
projective terms. There is no finite-generation or flat-ring-map hypothesis.
Source: Stacks Project, more-algebra.tex, proof of lemma-base-change-RHom (Tag 0A6A),
and lemma-derived-tor-quasi-isomorphism (Tag 064K).
(blueprint: lem-pc-ring-bounded-projective-extension).

Proof: on the one-object bottom-topology site, evaluation identifies modules and
internal tensor with ordinary modules and tensor over the constant ring. Every
projective A-module is a retract of a free module and hence flat. The bounded-above
flat-complex theorem, applied through this identification, says that P is K-flat.
For each term choose a free-module retraction. Tensoring its two splitting maps with B
preserves their composite, so the extended term is a retract of a free B-module and
is projective. The specified object equalities identify this tensor extension with F.
These arguments work for infinite-rank projectives, the zero ring, zero terms and an empty
interval; no representative in a derived category is chosen here. -/
theorem ringBoundedProjectiveExtension {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B)
    (F : SheafOfModules.{u} ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (onePointRingSheaf A)) ⥤
      SheafOfModules.{u} ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (onePointRingSheaf B))) [F.Additive]
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings
      (⟨(Functor.const _).map (CommRingCat.ofHom φ)⟩ :
        onePointRingSheaf A ⟶ onePointRingSheaf B) M)
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (onePointRingSheaf A))) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hp : ∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩))) :
    P.IsKFlat ∧
      (∀ n : ℤ, Module.Projective B
        ((((F.mapHomologicalComplex (.up ℤ)).obj P).X n).val.obj
          (op ⟨PUnit.unit⟩))) := by
  constructor
  · apply isKFlat_of_boundedAbove_flat P
    · obtain ⟨a, b, h⟩ := hb
      exact ⟨b, fun n hn ↦ h n (Or.inr hn)⟩
    · intro n
      let R := onePointRingSheaf A
      let O := (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R
      let M := P.X n
      have hflat (V : (Discrete PUnit.{u + 1})ᵒᵖ) : Module.Flat A (M.val.obj V) := by
        have hV : V = op ⟨PUnit.unit⟩ := Subsingleton.elim _ _
        subst V
        have := hp n
        infer_instance
      have hM : PreservesFiniteLimits (MonoidalCategory.tensorRight M.val) := by
        constructor
        intro K _ _
        have (V : (Discrete PUnit.{u + 1})ᵒᵖ) :
            Module.Flat (R.obj.obj V) (M.val.obj V) := hflat V
        exact ⟨⟨fun hc ↦ ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
          (fun V ↦ isLimitOfPreserves
            (MonoidalCategory.tensorRight (show ModuleCat (R.obj.obj V) from M.val.obj V))
            (isLimitOfPreserves (PresheafOfModules.evaluation O.obj V) hc))⟩⟩⟩
      have : Presheaf.IsLocallyInjective ⊥ (𝟙 O.obj) :=
        Presheaf.isLocallyInjective_of_injective ⊥ _ (fun _ ↦ Function.injective_id)
      have : Presheaf.IsLocallySurjective ⊥ (𝟙 O.obj) :=
        Presheaf.isLocallySurjective_of_surjective ⊥ _ (fun _ ↦ Function.surjective_id)
      have hf := (PresheafOfModules.isFlat_sheafification_obj
        (R := R) (𝟙 O.obj) M.val hM).2
      let := SheafOfModules.monoidalCategory R
      let e : (PresheafOfModules.sheafification (𝟙 O.obj)).obj M.val ≅ M :=
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).counit).app M
      exact (exactFunctor _ _).prop_of_iso
        ((MonoidalCategory.curriedTensor _).flip.mapIso e) hf
  · intro n
    change Module.Projective B ((F.obj (P.X n)).val.obj (op ⟨PUnit.unit⟩))
    rw [hF (P.X n)]
    let R := onePointRingSheaf B
    let O := (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    let α : onePointRingSheaf A ⟶ R := ⟨(Functor.const _).map (CommRingCat.ofHom φ)⟩
    let N : SheafOfModules O :=
      ⟨SheafOfModules.changeOfRingsPresheaf.{u, u, u} α (P.X n), Presheaf.isSheaf_bot _⟩
    let e : SheafOfModules.changeOfRings.{u, u, u} α (P.X n) ≅ N :=
      (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).counit).app N
    have hn : Module.Projective B (N.val.obj (op ⟨PUnit.unit⟩)) := by
      let := φ.toAlgebra
      have := hp n
      change Module.Projective B
        (TensorProduct A B ((P.X n).val.obj (op ⟨PUnit.unit⟩)))
      infer_instance
    have : Module.Projective B
        ((SheafOfModules.evaluation (R := O) (op ⟨PUnit.unit⟩)).obj N) := hn
    exact Module.Projective.of_equiv'
      (((SheafOfModules.evaluation (R := O) (op ⟨PUnit.unit⟩)).mapIso e).symm.toLinearEquiv)

end CochainComplex
