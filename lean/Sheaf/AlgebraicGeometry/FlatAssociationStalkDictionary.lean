/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
public import Sheaf.AlgebraicGeometry.RelativeAssassin
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import Sheaf.AlgebraicGeometry.FibreStalkQuotient

/-! # Stalk and fibre dictionaries for flat-pullback association

Source: Stacks Project, Divisors, Tag 05DB, proof with the structure sheaf;
Schemes, Tag 0HA1; Algebra, Tag 05BY
(blueprint: lem-trf-flat-association-stalk-dictionary).

Extension of scalars writes the tensor product as `B ⊗[A] M`, canonically
symmetric to `M ⊗[A] B`, with its `B`-module structure already bundled.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Flat local stalks, the pullback tensor-stalk dictionary, and the fibre quotient
annihilator dictionary. Source: Stacks Project, Divisors, Tag 05DB, proof with
`F = O_Y`; Schemes, Tag 0HA1; Algebra, Tag 05BY
(blueprint: lem-trf-flat-association-stalk-dictionary).

Proof:
1. By def-weil-flat-morphism the stalk map is flat. By
   def-weil-locally-ringed-space-morphism it is local, hence the inverse image
   of the target maximal ideal is the source maximal ideal.
2. Choose a Noetherian affine neighbourhood of `h y` using pqf-def-locnoeth.
   By lem-weil-pbc-affine-open-stalk-localization its germ map is localization
   at the corresponding prime. Apply lem-weil-pbc-localization-noetherian.
3. Apply lem-weil-pbc-module-stalk-pullback to identify the pullback stalk with
   extension of scalars. A linear isomorphism preserves each element annihilator.
   Thus def-trf-relative-assassin and def-weil-pbc-annihilator-associated-primes
   give both associated-point equivalences.
4. By def-pc-scheme-fibre the point `h.asFiber y` is the unique point over `y`.
   Apply lem-sbc-scheme-fibre-stalk-quotient to get the canonical quotient
   isomorphism. The extended base maximal ideal lies in the source maximal ideal
   by locality. Its quotient is the unique maximal ideal: every element outside
   it lifts to a unit of the source local ring. The isomorphism preserves it.
5. The annihilator over `B` of an element of `C` is the inverse image of its
   annihilator over `C` under the surjection `B → C`. Since the inverse image
   of `m_B / I` is `m_B`, surjectivity proves the equivalence of annihilators.
   Taking existence of an element, then transporting along the quotient
   isomorphism, gives the final associated-point equivalence. No Noetherianity
   of `B` or finite generation of `M` is used. -/
theorem flatAssociation_stalk_dictionary
    {Y Z : Scheme.{u}} (h : Y ⟶ Z) [Flat h] [IsLocallyNoetherian Z]
    (G : Z.Modules) [SheafOfModules.IsQuasicoherent.{u} G] (y : Y) :
    (h.stalkMap y).hom.Flat ∧
    IsLocalHom (h.stalkMap y).hom ∧
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap (h.stalkMap y).hom =
      IsLocalRing.maximalIdeal (Z.presheaf.stalk (h y)) ∧
    IsNoetherianRing (Z.presheaf.stalk (h y)) ∧
    Nonempty
      ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj ((tensorPullback h).obj G) ≅
        (ModuleCat.extendScalars (h.stalkMap y).hom).obj
          ((RingedSpace.moduleStalkFunctor Z.toRingedSpace (h y)).obj G)) ∧
    (y ∈ associatedPoints ((tensorPullback h).obj G) ↔
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ∈
        RingTheory.annihilatorAssociatedPrimes (Y.presheaf.stalk y)
          ((ModuleCat.extendScalars (h.stalkMap y).hom).obj
            ((RingedSpace.moduleStalkFunctor Z.toRingedSpace (h y)).obj G))) ∧
    (h y ∈ associatedPoints G ↔
      IsLocalRing.maximalIdeal (Z.presheaf.stalk (h y)) ∈
        RingTheory.annihilatorAssociatedPrimes (Z.presheaf.stalk (h y))
          ((RingedSpace.moduleStalkFunctor Z.toRingedSpace (h y)).obj G)) ∧
    (∃ e : (Y.presheaf.stalk y ⧸
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk (h y))).map (h.stalkMap y).hom) ≃+*
        (h.fiber (h y)).presheaf.stalk (h.asFiber y),
      (∀ b : Y.presheaf.stalk y,
        e (Ideal.Quotient.mk _ b) =
          ((Y.presheaf.stalkCongr (.of_eq (h.fiberι_asFiber y))).inv ≫
            (h.fiberι (h y)).stalkMap (h.asFiber y)).hom b) ∧
      ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).map (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (Z.presheaf.stalk (h y))).map
          (h.stalkMap y).hom))).map e.toRingHom =
        IsLocalRing.maximalIdeal ((h.fiber (h y)).presheaf.stalk (h.asFiber y))) ∧
    (∀ v : Y.presheaf.stalk y ⧸
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk (h y))).map (h.stalkMap y).hom,
      (⊥ : Submodule (Y.presheaf.stalk y)
        (Y.presheaf.stalk y ⧸
          (IsLocalRing.maximalIdeal (Z.presheaf.stalk (h y))).map
            (h.stalkMap y).hom)).colon {v} =
          IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ↔
      (⊥ : Submodule
        (Y.presheaf.stalk y ⧸
          (IsLocalRing.maximalIdeal (Z.presheaf.stalk (h y))).map (h.stalkMap y).hom)
        (Y.presheaf.stalk y ⧸
          (IsLocalRing.maximalIdeal (Z.presheaf.stalk (h y))).map
            (h.stalkMap y).hom)).colon {v} =
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).map (Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal (Z.presheaf.stalk (h y))).map
              (h.stalkMap y).hom))) ∧
    (h.asFiber y ∈ associatedPoints (SheafOfModules.unit (h.fiber (h y)).ringCatSheaf) ↔
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ∈
        RingTheory.annihilatorAssociatedPrimes (Y.presheaf.stalk y)
          (Y.presheaf.stalk y ⧸
            (IsLocalRing.maximalIdeal (Z.presheaf.stalk (h y))).map
              (h.stalkMap y).hom)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
