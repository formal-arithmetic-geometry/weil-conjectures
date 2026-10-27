/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.BoundedConstructibleTower
import Sheaf.Paper.RelativeFiniteCoefficientModel
import Sheaf.Paper.NilpotentCoefficientLissity

/-! # Nilpotent reflection of relative finite lissity -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientRingSheafify in
/-- Relative finite lissity is reflected by a nilpotent surjection of finite coefficients.

Source: Stacks Project, Cohomology on Sites, Tag 094I and Tag 094H.
(blueprint: lem-weil-pbc-relative-nilpotent-lissity)

Proof: inverse image is exact and commutes with derived scalar extension, by the
scalar-extension/pullback adjunction comparison. Identify inverse-image constant ring
sheaves with the native constant ring sheaves using the constant-section isomorphisms.
Pass to the equivalent small site and its constant coefficient module encoding. The
covering-sieve descriptions become locally constant finite-type modules. Factor the
surjection through B/ker(f), and use the quotient ring isomorphism to transport the
reduced cohomology hypothesis. Apply locallyConstantFiniteTypeModules_reduction_pow
at a positive nilpotence exponent of ker(f); its second clause gives lissity of the
unreduced complex. Exactness preserves the upper bound. Since B is finite, each finite
type constant B-module has finite underlying set. Transport these models back through
the small-site and constant-ring equivalences to relative models. This uses neither
an adic tower nor a common stratification, and includes zero rings and empty schemes. -/
theorem relative_finite_lisse_of_nilpotent_reduction {X Y : Scheme.{u}} (g : Y ⟶ X)
    {B R : Type (u + 1)} [CommRing B] [CommRing R] [Finite B] [Finite R]
    (f : B →+* R) (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (K : DerivedCategory (pbcModules X (adicLisseConstantRing X B)))
    (hbounded : ∃ b : ℤ, ∀ q : ℤ, b < q →
      IsZero ((DerivedCategory.homologyFunctor
        (pbcModules X (adicLisseConstantRing X B)) q).obj K))
    (hmod : ∀ q : ℤ, IsRelativelyFiniteLisseModule g R
      ((DerivedCategory.homologyFunctor
          (pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X R))) q).obj
        ((adicTowerPullback g (adicLisseConstantRing X R)).obj
          ((pbcDerivedExtend ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom f))).obj K)))) :
    ∀ q : ℤ, IsRelativelyFiniteLisseModule g B
      ((DerivedCategory.homologyFunctor
          (pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))) q).obj
        ((adicTowerPullback g (adicLisseConstantRing X B)).obj K)) := by
  classical
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).isEquivalence_inverse
  have : HasPullbacks (proEtaleSiteModel Y) :=
    Adjunction.hasLimitsOfShape_of_equivalence
      (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt)
  obtain ⟨L, hz, hB, hR⟩ := exists_relative_finite_coefficient_model g f K
  have hLbounded : ∃ b : ℤ, ∀ q : ℤ, b < q →
      IsZero ((coefficientModelCohomology _ q).obj L) := by
    obtain ⟨b, hb⟩ := hbounded
    exact ⟨b, fun q hq ↦ hz q (hb q hq)⟩
  have h := SheafOfModules.lisse_of_nilpotent_coefficient_surjection
    (proEtaleModelTopology Y) f hf hnil L hLbounded (fun q ↦ (hR q).mp (hmod q))
  exact fun q ↦ (hB q).mpr (h q)

end AlgebraicGeometry.Scheme
