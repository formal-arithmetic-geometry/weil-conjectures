/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.SixFunctors.IntegralLisseReductionData
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Finite continuous coefficients are constant sheaves

Source: Bhatt--Scholze, Lemma 6.8.2(1). The comparison sends constant sections to
constant functions; its local inverse uses open fibres of discrete-valued functions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Topology

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Finite continuous coefficient sheaves are canonically constant.

Source: Bhatt--Scholze, Lemma 6.8.2(1), pp. 58--59.
(blueprint: lem-sfb-integral-lisse-finite-constant)

Proof: the normalized profinite tower identifies each finite quotient with a discrete
space: its projection to a discrete coordinate is continuous and the quotient map
has the final topology. Map the constant presheaf into continuous functions by
constant functions. A continuous function to a discrete finite ring is constant on
its open fibres. Restricting the scheme to these open subsets gives a Zariski,
hence pro-etale, cover on which it is in the image. If two constant sections have
the same function on an object, they are equal whenever the object has a point.
When it is empty, the empty covering gives local equality. Thus this presheaf map
is locally bijective. The universal sheafification map and the local-bijection
criterion give an isomorphism from the constant ring sheaf. Its value on each
sheafified constant section is the original constant function by the defining
factorization. This also proves uniqueness and handles the empty base. -/
theorem integralLisseFiniteConstant_exists (n : ℕ) :
    ∃ e : (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of (Padic.coefficientExtensionRing l E (n + 1))) ≅
        integralLisseFiniteRing l E X n,
      ∀ (U : X.ProEtᵒᵖ) (a : Padic.coefficientExtensionRing l E (n + 1)),
      ((e.hom.hom.app U)
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (Padic.coefficientExtensionRing l E (n + 1))))).app U a)) =
        integralLisseFiniteConstant l E X n U a := by
  classical
  let := spectralNorm.normedField ℚ_[l] E
  obtain ⟨e, he, heHome⟩ :=
    (Padic.coefficientExtension_integers_profinite_tower.{u + 1, u + 1} l E).1
  have hq : @Continuous _ _
      (inferInstance : TopologicalSpace (Padic.coefficientExtensionIntegers l E)) ⊥
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := by
    let : ∀ k : ℕ, TopologicalSpace (Padic.coefficientExtensionRing l E (k + 1)) :=
      fun _ ↦ ⊥
    have hc := (continuous_apply n).comp (continuous_subtype_val.comp heHome.continuous)
    exact hc.congr (fun x ↦ he x n)
  have hd : @Continuous _ _
      (inferInstance : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1))) ⊥
      id := by
    exact (@Topology.IsQuotientMap.continuous_iff
      (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionRing l E (n + 1))
      (Padic.coefficientExtensionRing l E (n + 1))
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) id _ _ ⊥
      (QuotientRing.isOpenQuotientMap_mk
        (Padic.coefficientExtensionIdeal l E (n + 1))).isQuotientMap).mpr hq
  let P := (Functor.const X.ProEtᵒᵖ).obj
    (CommRingCat.of (Padic.coefficientExtensionRing l E (n + 1)))
  let H := integralLisseFiniteRing l E X n
  let c : P ⟶ H.obj :=
    { app := fun U ↦ CommRingCat.ofHom
        { toFun := integralLisseFiniteConstant l E X n U
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }
  have hinj : Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) c := by
    constructor
    intro W a b hab
    by_cases h : a = b
    · subst b
      exact (Scheme.ProEt.topology X).superset_covering (fun _ _ _ ↦ rfl)
        ((Scheme.ProEt.topology X).top_mem _)
    · have hempty : IsEmpty W.unop.left := ⟨fun x ↦ h (by
        exact congrArg (fun z ↦ z.down x) hab)⟩
      let j : ∀ i : PEmpty.{u + 1}, (i.elim : Scheme.{u}) ⟶ W.unop.left :=
        fun i ↦ i.elim
      let : ∀ i, IsOpenImmersion (j i) := fun i ↦ i.elim
      apply Scheme.ProEt.mem_topology_of_openImmersion _ j
      · intro x
        exact isEmptyElim x
      · intro i
        exact i.elim
  have hsurj : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) c := by
    constructor
    intro W s
    let f : C(W.left, Padic.coefficientExtensionRing l E (n + 1)) := s.down
    have hf : @Continuous _ _ _ ⊥ f := by
      apply continuous_def.mpr
      intro V hV
      exact f.continuous.isOpen_preimage _ (continuous_def.mp hd V hV)
    let V (x : W.left) : W.left.Opens :=
      ⟨f ⁻¹' {f x}, continuous_def.mp hf _ trivial⟩
    apply Scheme.ProEt.mem_topology_of_openImmersion _ (fun x ↦ (V x).ι)
    · intro x
      exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
    · intro x
      refine ⟨f x, ?_⟩
      apply ULift.ext
      apply ContinuousMap.ext
      intro y
      exact y.property.symm
  let φ : (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of (Padic.coefficientExtensionRing l E (n + 1))) ⟶ H :=
    ⟨sheafifyLift (Scheme.ProEt.topology X) c H.property⟩
  have hφ : toSheafify (Scheme.ProEt.topology X) P ≫ φ.hom = c :=
    toSheafify_sheafifyLift (Scheme.ProEt.topology X) c H.property
  have : IsIso φ := by
    apply (Sheaf.isLocallyBijective_iff_isIso φ).mp
    constructor
    · change Presheaf.IsLocallyInjective _ _
      rw [← Presheaf.comp_isLocallyInjective_iff _
        (toSheafify (Scheme.ProEt.topology X) P), hφ]
      exact hinj
    · change Presheaf.IsLocallySurjective _ _
      rw [← Presheaf.comp_isLocallySurjective_iff _
        (toSheafify (Scheme.ProEt.topology X) P), hφ]
      exact hsurj
  refine ⟨asIso φ, ?_⟩
  intro U a
  exact congrArg (fun α ↦ (α.app U) a) hφ

end AlgebraicGeometry.ProEtale
