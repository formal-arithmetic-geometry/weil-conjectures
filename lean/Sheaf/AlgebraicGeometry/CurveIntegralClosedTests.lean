/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Integral closed tests and the generic witness on a proper curve

Source: Stacks Project, Varieties, Tag 0AYV, `lemma-degree-on-proper-curve`,
proof of condition (2), whole-curve case; Tag 0AYR, definition of degree.
(blueprint: lem-trf-curve-integral-closed-tests).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Integral closed subschemes of an integral proper curve are exactly the whole curve
or reduced closed points. The structure module is the generic coherent witness.

The rank is computed over the generic local ring: its maximal ideal is zero, so the
canonical residue quotient identifies this ring with the residue field. Thus the stated
finrank is precisely the dimension over the residue field, as in Tag 0AYV.
The witness is stated once, independently of the closed immersion: this is equivalent
to asserting it in every whole-curve case, since the identity is such a case.

Source: Stacks Project, Varieties, Tags 0AYV and 0AYR.
(blueprint: lem-trf-curve-integral-closed-tests).

Proof:
1. The image T of an integral closed immersion is nonempty, closed and irreducible.
Scheme sobriety (lem-weil-pbc-scheme-sober) gives its unique generic point z.
If T is proper and contains a point y different from z, then closure {y} is strictly
contained in T, which is strictly contained in C. This contradicts dimension one.
Thus a proper T is a closed singleton, distinct from the generic point of C.
Dimension one also excludes C itself being a singleton.
2. Integrality implies reducedness. Uniqueness of the reduced induced closed subscheme
(lem-weil-pbc-reduced-induced-closed-subscheme) identifies a full-image immersion with
C, and a singleton-image immersion with Spec of its residue field, over C.
The canonical residue morphism is closed by lem-trf-closed-point-residue-immersion.
The full-image and proper-singleton alternatives are mutually exclusive.
3. Properness over a field makes C Noetherian; local triviality makes its invertible
modules coherent (lem-trf-proper-field-invertible-coherent). In particular O_C is coherent.
Integral local rings are nonzero (lem-sc-integral-scheme-stalks-in-function-field), so
its module support is all of C.
4. The generic local ring is a field by the same integral-stalk theorem. Its maximal
ideal is zero, so the canonical residue quotient is an isomorphism. The structure-module
stalk is this ring as a module, hence is annihilated by that ideal. The singleton basis
consisting of 1 gives residue-field dimension one (def-weil-vector-space-dimension).
5. The balanced maps s tensor a maps to a s and s maps to s tensor 1 are inverse on
sections and commute with restriction. Sheafification (def-weil-pbc-sheafification)
therefore gives L tensor O_C isomorphic to L (def-pur-sheaf-tensor-product).
6. Cohomology preserves this isomorphism, hence the Euler characteristics agree
(def-pc-euler-characteristic). Substitute the definition
of degree (def-pc-degree-line-bundle) to obtain the final identity. -/
theorem curve_integral_closed_tests
    (k : Type u) [Field k] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsIntegral C] [IsProper (C ↘ Spec (.of k))]
    (hdim : topologicalKrullDim C = 1)
    (ξ : C) (hξ : closure ({ξ} : Set C) = Set.univ)
    (L : C.Modules) [L.IsInvertible] :
    (∀ (Z : Scheme.{u}) [IsIntegral Z] (i : Z ⟶ C) [IsClosedImmersion i],
      Xor (IsIso i)
        (∃ z : C, IsClosed ({z} : Set C) ∧ z ≠ ξ ∧
          ∃ e : Z ≅ Spec (C.residueField z), e.hom ≫ C.fromSpecResidueField z = i)) ∧
    RingedSpace.IsCoherent C.toRingedSpace (SheafOfModules.unit C.ringCatSheaf) ∧
    {x : C | ¬ Subsingleton
      ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (SheafOfModules.unit C.ringCatSheaf).val.presheaf x)} = Set.univ ∧
    IsLocalRing.maximalIdeal (C.presheaf.stalk ξ) = ⊥ ∧
    (∀ (a : C.presheaf.stalk ξ), a ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk ξ) →
      ∀ m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (SheafOfModules.unit C.ringCatSheaf).val.presheaf ξ, a • m = 0) ∧
    Nonempty ((RingedSpace.moduleStalkFunctor C.toRingedSpace ξ).obj
      (SheafOfModules.unit C.ringCatSheaf) ≅
        (ModuleCat.restrictScalars (C.residue ξ).hom).obj
          (ModuleCat.of (C.residueField ξ) (C.residueField ξ))) ∧
    Module.finrank (C.presheaf.stalk ξ)
      ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (SheafOfModules.unit C.ringCatSheaf).val.presheaf ξ) = 1 ∧
    Nonempty (L ⊗ SheafOfModules.unit C.ringCatSheaf ≅ L) ∧
    (L ⊗ SheafOfModules.unit C.ringCatSheaf).eulerChar k -
      eulerChar k (SheafOfModules.unit C.ringCatSheaf) = L.degree k := by
  sorry

end AlgebraicGeometry.Scheme.Modules
