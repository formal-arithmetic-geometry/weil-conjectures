/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic

import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

/-! # Restricted injective module sheaves are direct-image acyclic -/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- An injective sheaf remains acyclic for étale direct image after restriction of
coefficients. This does not assert that restriction preserves injective objects.

Source: Stacks Project, Tag 03FD, proof, together with Tag 0D6J(3).
Proof: the canonical module/abelian derived direct-image comparison is invertible
for both coefficient rings. Its homology comparison in degree n + 1 is therefore
invertible. Positive derived direct image of I as a Λ'-module sheaf is zero by
injectivity. Forgetting coefficients and the Λ' comparison show that positive
abelian derived direct image of its underlying sheaf is zero. Restriction along
φ leaves that underlying abelian sheaf definitionally unchanged. The Λ comparison
then shows that the underlying abelian sheaf of the positive Λ-module derived
direct image is zero. The faithful coefficient-forgetting functor reflects this:
its image of the identity is zero, hence the identity itself is zero.
No flatness of φ or quasi-compactness of f is required.
(blueprint: lem-sbc-restrict-scalars-injective-direct-image-acyclic) -/
theorem restrictScalars_injective_lowerStar_rightAcyclic
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {Z W : Scheme.{u}} (f : Z ⟶ W)
    (I : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ')) [Injective I] :
    ((f)_*[ModuleCat.{u + 1} Λ]).rightAcyclic
      ((Sheaf.restrictScalars Z.smallEtaleTopology φ).obj I) := by
  intro n
  let F := (Sheaf.restrictScalars Z.smallEtaleTopology φ).obj I
  have hcomp (R : Type (u + 1)) [CommRing R] :
      IsIso (Functor.rightDerivedBaseChange (moduleAbelianLowerStarIso R f).hom
        (n + 1)) := by
    have h := isIso_moduleAbelianDerivedLowerStarComparison R f
    change IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (moduleAbelianLowerStarIso R f).hom) at h
    unfold Functor.rightDerivedBaseChange
    infer_instance
  have := hcomp Λ'
  have := hcomp Λ
  let e' := asIso (Functor.rightDerivedBaseChange
    (moduleAbelianLowerStarIso Λ' f).hom (n + 1))
  let e := asIso (Functor.rightDerivedBaseChange
    (moduleAbelianLowerStarIso Λ f).hom (n + 1))
  have hI := ((f)_*[ModuleCat.{u + 1} Λ']).isZero_rightDerived_obj_injective_succ n I
  have hAb := (Functor.map_isZero (moduleAbelianForget Λ' W) hI).of_iso
    (e'.app I).symm
  have hF : Limits.IsZero ((moduleAbelianForget Λ W).obj
      ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived (n + 1)).obj F)) :=
    hAb.of_iso (e.app F)
  rw [Limits.IsZero.iff_id_eq_zero]
  apply (moduleAbelianForget Λ W).map_injective
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  exact hF.eq_of_src _ _

end AlgebraicGeometry.Etale
