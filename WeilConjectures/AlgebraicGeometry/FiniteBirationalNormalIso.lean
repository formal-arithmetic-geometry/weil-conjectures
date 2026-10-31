/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Finite birational morphisms onto normal integral schemes

Source: Stacks Project, Morphisms, Tag 0AB1 (lemma-finite-birational-over-normal)
(blueprint: lem-trf-finite-birational-normal-iso).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A finite birational morphism to a normal integral scheme is an isomorphism.

Source: Stacks Project, Morphisms, Tag 0AB1 (lemma-finite-birational-over-normal)
(blueprint: lem-trf-finite-birational-normal-iso).

Proof: for a nonempty affine open `V` of `Y`, finiteness makes its inverse image
`U` affine and gives a finite ring map from the sections of `V` to those of `U`.
The generic-point equality and the bijective transported stalk map identify both
rings with the same fraction field, so the ring map is injective and birational.
Every localization of the target affine ring at a maximal ideal is a normal domain
by the target local-ring hypothesis; the local-to-global normal-domain criterion
therefore makes the target affine ring integrally closed. Every element of the
finite source algebra is integral over it, hence belongs to it, so the affine ring
map is an isomorphism. These affine isomorphisms glue over `Y`; the empty open has
empty inverse image. The proof uses [def-pc-integral-scheme],
[def-weil-finite-integral-morphism], [def-sc-function-field], and
[def-weil-pbc-normal-ring], together with the affine fraction-field and
normal-domain lemmas recorded in the item proof dependencies.
-/
theorem isIso_of_finite_birational_normal
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f]
    (hgeneric : f (genericPoint X) = genericPoint Y)
    (hbirational : Function.Bijective
      ((Y.presheaf.stalkCongr (Inseparable.of_eq hgeneric)).inv ≫
        f.stalkMap (genericPoint X) : Y.functionField ⟶ X.functionField))
    (hnormal : ∀ y : Y,
      IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)) :
    IsIso f := by
  classical
  let e : Y.functionField ≃+* X.functionField := RingEquiv.ofBijective
    (((Y.presheaf.stalkCongr (Inseparable.of_eq hgeneric)).inv ≫
      f.stalkMap (genericPoint X)).hom) hbirational
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := .isomorphisms Scheme)
    (fun V : Y.affineOpens => V.1) (iSup_affineOpens_eq_top Y)
  intro V
  have hAff : IsAffineOpen V.1 := V.2
  apply (isIso_morphismRestrict_iff_isIso_app f hAff).mpr
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  by_cases hV : Nonempty V.1
  · have : Nonempty V.1 := hV
    have hη : genericPoint Y ∈ V.1 :=
      ((genericPoint_spec Y).mem_open_set_iff V.1.isOpen).mpr (by simpa using hV)
    have hξ : genericPoint X ∈ f ⁻¹ᵁ V.1 := by
      change f (genericPoint X) ∈ V.1
      rwa [hgeneric]
    have : Nonempty (f ⁻¹ᵁ V.1) := ⟨⟨_, hξ⟩⟩
    have : IsFractionRing Γ(Y, V.1) Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y V.1 hAff
    have : IsIntegrallyClosed Γ(Y, V.1) := by
      apply IsIntegrallyClosed.of_localization_maximal
      intro p _ hp
      let y : PrimeSpectrum Γ(Y, V.1) := ⟨p, inferInstance⟩
      have hy : hAff.fromSpec y ∈ V.1 :=
        (congrArg (fun s : Set Y => hAff.fromSpec y ∈ s)
          hAff.range_fromSpec).mp (Set.mem_range_self y)
      let x : V.1 := ⟨hAff.fromSpec y, hy⟩
      let := TopCat.Presheaf.algebra_section_stalk Y.presheaf x
      have : IsLocalization.AtPrime (Y.presheaf.stalk x) p :=
        hAff.isLocalization_stalk' y hy
      have : IsIntegrallyClosed (Y.presheaf.stalk x) := (hnormal x).2
      exact IsIntegrallyClosed.of_equiv
        (IsLocalization.algEquiv p.primeCompl (Y.presheaf.stalk x)
          (Localization.AtPrime p)).toRingEquiv
    have hcomm (a : Γ(Y, V.1)) :
        e (Y.germToFunctionField V.1 a) =
          X.germToFunctionField (f ⁻¹ᵁ V.1) (f.app V.1 a) := by
      have hs : Y.presheaf.germ V.1 (genericPoint Y) hη ≫
          (Y.presheaf.stalkCongr (Inseparable.of_eq hgeneric)).inv =
            Y.presheaf.germ V.1 (f (genericPoint X)) hξ := by
        simp only [TopCat.Presheaf.stalkCongr_inv, Y.presheaf.germ_stalkSpecializes]
      change (Y.presheaf.germ V.1 (genericPoint Y) hη ≫
        ((Y.presheaf.stalkCongr (Inseparable.of_eq hgeneric)).inv ≫
          f.stalkMap (genericPoint X))) a = _
      rw [← Category.assoc, hs, f.germ_stalkMap]
      rfl
    let : Algebra Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
    let g : Γ(X, f ⁻¹ᵁ V.1) →ₐ[Γ(Y, V.1)] Y.functionField :=
      { toRingHom := e.symm.toRingHom.comp (X.germToFunctionField (f ⁻¹ᵁ V.1)).hom
        commutes' := fun a => by
          change e.symm (X.germToFunctionField (f ⁻¹ᵁ V.1) (f.app V.1 a)) =
            Y.germToFunctionField V.1 a
          rw [← hcomm, e.symm_apply_apply] }
    have hg : Function.Injective g :=
      e.symm.injective.comp (X.germToFunctionField_injective (f ⁻¹ᵁ V.1))
    have : Module.Finite Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1) := f.finite_app V.1 hAff
    constructor
    · intro a b hab
      apply Y.germToFunctionField_injective V.1
      apply e.injective
      rw [hcomm, hcomm, hab]
    · intro b
      obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
        ((IsIntegral.of_finite Γ(Y, V.1) b).map g)
      refine ⟨a, hg ?_⟩
      exact (g.commutes a).trans ha
  · have he : V.1 = ⊥ := SetLike.coe_injective
      (Set.not_nonempty_iff_eq_empty.mp (by simpa using hV))
    have : Subsingleton Γ(Y, V.1) :=
      CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty he)
    have hpre : f ⁻¹ᵁ V.1 = ⊥ := congrArg (f ⁻¹ᵁ ·) he
    have : Subsingleton Γ(X, f ⁻¹ᵁ V.1) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hpre)
    exact ⟨Function.injective_of_subsingleton _, fun b => ⟨0, Subsingleton.elim _ _⟩⟩

end AlgebraicGeometry
