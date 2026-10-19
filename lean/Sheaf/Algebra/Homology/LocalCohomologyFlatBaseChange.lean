import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.Algebra.Homology.IdealPowerTorsionFunctor

/-! # Flat base change for derived ideal-torsion local cohomology

Source: Stacks Project, Tag 0ALZ (lemma-torsion-change-rings), with Tag 0955
(lemma-local-cohomology-noetherian) and Tag 0956 (lemma-compute-local-cohomology-noetherian)
(blueprint: lem-per-local-cohomology-flat-base-change).

The tensor product is written in the commuted form `B ⊗[A] M`, which carries its
`B`-module structure on the first factor and is canonically the stated `M ⊗[A] B`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

open CategoryTheory
open Module

universe u

namespace ModuleCat

/-- Flat scalar extension commutes with every right-derived ideal-power torsion module,
naturally in the module.

Source: Stacks Project, Tag 0ALZ (lemma-torsion-change-rings), taking cohomology for a
flat map, together with Tag 0955 and Tag 0956 for the right-derived ideal-torsion model.
(blueprint: lem-per-local-cohomology-flat-base-change).

Proof plan. First choose finite generators of the ideal using Noetherianity and map them
to generators of the extended ideal. Apply the natural Cech comparison of
`idealPowerTorsion_rightDerived_iso_cech` over both rings. Localization tensor base
change identifies every coefficient after scalar extension, and finite products commute
with this tensor. The resulting degreewise maps are a natural isomorphism of the two
bounded alternating complexes, including the empty-generator case. Finally apply the
flat comparison `mapHomologyIso` to cohomology. The composite is `B`-linear and its
naturality follows from the fraction formulas and the cycle-class formula for flat
cohomology base change. No finite generation of the module or faithful flatness is used.
-/
theorem idealPowerTorsion_rightDerived_flat_base_change
    (A B : Type u) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : RingHom.Flat f) (I : Ideal A) :
    letI := f.toAlgebra
    ∃ e : ∀ (M : ModuleCat.{u} A) (q : ℕ),
      TensorProduct A B ((idealPowerTorsion I).rightDerived q |>.obj M)
          ≃ₗ[B]
        ((idealPowerTorsion (Ideal.map f I)).rightDerived q).obj
          (ModuleCat.of B (TensorProduct A B M)),
    ∀ (M N : ModuleCat.{u} A) (g : M ⟶ N) (q : ℕ),
      (((idealPowerTorsion (Ideal.map f I)).rightDerived q).map
          (ModuleCat.ofHom
            (TensorProduct.AlgebraTensorModule.map
              (LinearMap.id : B →ₗ[B] B) g.hom))).hom.comp (e M q).toLinearMap =
        (e N q).toLinearMap.comp
          (TensorProduct.AlgebraTensorModule.map
            (LinearMap.id : B →ₗ[B] B)
            (((idealPowerTorsion I).rightDerived q).map g).hom) := by
  sorry

end ModuleCat
