/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
import Sheaf.Paper.TorsionCdCriticalCoimageSurjectivity

/-! # A relation-comparison substep of the arbitrary-affine cohomological bound -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The coimage retains the strict upper bound d+2.

Source: blueprint latest, `det-sf-comp-coherence-refinement.proof.md`, paragraph (2),
first paragraph, arbitrary-affine coefficient-transfer obligation; the relation
comparison in steps 2 and 3 of `lem-sfb-torsion-cd-bounded-serre-kernel`.
Agent-formulated sub-obligation; exact full-generality reference WANTED.
(blueprint: lem-sfb-torsion-cd-bounded-serre-coimage)

Proof in words (the remaining geometric obligation):
Use the actual relation resolution of f on affine weakly contractible pro-etale
charts. Retain the continuous coefficient matrices and descend through finite
open-closed supports. For integral coefficients compare the finite quotient
relation complexes with torsion etale complexes, apply the torsion bound, and use
the countable inverse-limit comparison. For rational coefficients apply exact
scalar localization to finite integral relation stages. The resulting comparison,
combined with the two input bounds, kills the coimage cohomology in degrees
strictly above d+2. This is only the high-degree image estimate; it makes no claim
about coimage cohomology in degree d+2 or its connecting map. No completeness of
an arbitrary kernel or filtered finite-heart presentation is assumed.

For the zero map the coimage is zero. For an isomorphism the coimage is isomorphic
to the source and its quotient map is invertible. Empty schemes and zero modules
are included. The functor is the ordinary uncompleted derived sections functor.
-/
theorem torsionCd_bounded_serre_coimage
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [IsAffine X] (d : ℕ)
    (hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : M ⟶ N)
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M)
    (hN : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) N)
    (hMb : ∀ q : ℤ, (d : ℤ) + 2 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((condensedModuleSections Λ X).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))))
    (hNb : ∀ q : ℤ, (d : ℤ) + 2 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((condensedModuleSections Λ X).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj N))))
    (q : ℤ) (hq : (d : ℤ) + 2 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((condensedModuleSections Λ X).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj (Abelian.coimage f)))) := by
  -- The critical-degree theorem may be applied with a larger dimension bound.
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) + 2 = q :=
    ⟨(q - 2).toNat, by omega⟩
  have hde : d ≤ e := by omega
  have hcd' : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE e := by
    intro V v _ _ F hF r hr
    exact hcd V v F hF r (by omega)
  have hep := torsionCd_critical_coimage_surjectivity ℓ Λ hΛ X e hcd' M N f hM hN
    (fun r hr ↦ hMb r (by omega)) (fun r hr ↦ hNb r (by omega))
  let := hep
  rw [← he]
  exact IsZero.of_epi
    ((DerivedCategory.homologyFunctor _ ((e : ℤ) + 2)).map
      ((condensedModuleSections Λ X).rightDerivedFunctor.map
        ((DerivedCategory.singleFunctor _ 0).map (Abelian.coimage.π f))))
    (hMb _ (by omega))

end AlgebraicGeometry.ProEtale
