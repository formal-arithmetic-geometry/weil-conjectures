/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel

/-! # Cohomology coordinates for affine derived base change

Source: Stacks Project, Tag 0DJ8, affine proof and equation-bc.
(blueprint: lem-pc-affine-base-change-cohomology-model).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The degree-i affine module comparison and its prime localizations, without any
invertibility hypothesis. Source: Stacks Project, perfect.tex, Tag 0DJ8, affine
proof, equation-bc and the displayed localization identity.
(blueprint: lem-pc-affine-base-change-cohomology-model).

Proof: identify the cartesian affine square with the tensor square A tensor_R R'.
Use the affine quasi-coherent derived equivalence to represent K and K' by module
complexes M and N. Derived pullback is derived scalar extension; affine derived
pushforward is restriction of scalars. The canonical adjunction and composition
counits defining schemeDerivedBaseChangeMap identify it with the K-flat comparison
span E tensor_R R' -> P tensor_A A' of the affine derived comparison theorem.
In degree i the source has its A' action induced by multiplication on M, commuting
with R'; the target has the usual A' action on H^i(N). The composite with phi is
A'-linear. Take these two cohomology modules U,V and their map a. Exact tilde and
the affine derived equivalence identify the restricted modules with the cohomology
sheaves on Spec R', giving eU,eV and the displayed commuting square.
At a prime p of A', the affine comparison localization theorem identifies source
cohomology localized at p with the base-derived tensor cohomology in equation-bc.
Exact module localization identifies target cohomology with H^i(N_p). Tilde stalks
are module localizations; derived pullback agrees with the canonical tensor-stalk
isomorphism. Naturality identifies the localized a with stalkComparison, up to
these source and target isomorphisms. K-flat resolution comparisons give the same
identification in any supplied Coordinates c: apply exact stalks to the
representative isomorphisms, then use the derived tensor universal counit
equations and the represents equation for c. This gives the additive equivalences
lU,lV and their pointwise commuting square. No complex of A'-modules representing
M tensor-derived_R R' is used:
only its cohomology carries the A' action. -/
theorem exists_affineBaseChangeCohomologyModel
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    (φf : R →+* A) (φg : R →+* R') (φg' : A →+* A') (φf' : R' →+* A')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φg)))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (K' : schemeDerivedCategory (Spec (.of A')))
    (hK' : schemeDerivedQCohProperty (Spec (.of A')) K')
    (φ : (derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K ⟶ K')
    (c : SingleComplexBaseChange.Coordinates (Spec.map (CommRingCat.ofHom φg')) K K' φ)
    (i : ℤ) :
    let F := ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
    let b := schemeDerivedBaseChangeMap (Spec.map (CommRingCat.ofHom φf))
      (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom φg))
      (Spec.map (CommRingCat.ofHom φg')) sq.w K ≫
      (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf'))).map φ
    ∃ (U V : ModuleCat.{u} A') (a : U ⟶ V)
      (eU : F.obj U ≅ H.obj ((derivedPullback (Spec.map (CommRingCat.ofHom φg))).obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf))).obj K)))
      (eV : F.obj V ≅ H.obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf'))).obj K')),
      eU.hom ≫ H.map b = F.map a ≫ eV.hom ∧
      ∀ p : PrimeSpectrum A',
        let t := SingleComplexBaseChange.stalkComparison
          (Spec.map (CommRingCat.ofHom φf)) (Spec.map (CommRingCat.ofHom φf'))
          (Spec.map (CommRingCat.ofHom φg)) (Spec.map (CommRingCat.ofHom φg'))
          sq c p i
        ∃ (lU : LocalizedModule p.asIdeal.primeCompl U ≃+ (Arrow.mk t).left)
          (lV : LocalizedModule p.asIdeal.primeCompl V ≃+ (Arrow.mk t).right),
          ∀ x, lV (LocalizedModule.map p.asIdeal.primeCompl a.hom x) = t (lU x) := by
  sorry

end AlgebraicGeometry
