/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import WeilConjectures.Compactification.Defs

/-!
# Compact-support image on ringed pro-etale sites

Source: proper base change, definition 1268
(blueprint: def-weil-pbc-projection-compactification).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S)

/-- Restriction along an open immersion has extension by zero as its left adjoint.
This universal property determines extension by zero up to its unique adjoint isomorphism.
Source: proper base change, definition 1268
(blueprint: def-weil-pbc-projection-compactification).
Proof: the open subtopos is the slice at the subterminal sheaf represented by j.
Extend a module on this slice by the zero module on its complement, and sheafify.
A map from this extension to M is exactly a map to the restriction of M: maps outside
j are uniquely zero, and the sheaf gluing condition gives the unique extension inside.
This bijection is natural in both modules and supplies the asserted left adjoint. -/
@[instance] theorem proEtaleOpenRestriction_isRightAdjoint :
    (proEtaleRingModulePullback j R S c).IsRightAdjoint := sorry

/-- Extension by zero, specified by its adjoint universal property to actual restriction.
Source: proper base change, definition 1268
(blueprint: def-weil-pbc-projection-compactification). -/
def proEtaleRingOpenExtension : proEtaleRingModules X S ⥤ proEtaleRingModules Z R :=
  (proEtaleRingModulePullback j R S c).leftAdjoint

/-- Extension by zero is additive and exact.
Source: proper base change, definition 1268
(blueprint: def-weil-pbc-projection-compactification).
Proof: in the open slice the construction is the identity, and off the open it is zero.
Thus it preserves zero, sums, kernels, and cokernels locally. Exactness and equality of
module maps are local on the site, so these properties descend to the original site. -/
theorem proEtaleRingOpenExtension_exact :
    (proEtaleRingOpenExtension j R S c).Additive ∧
      PreservesFiniteLimits (proEtaleRingOpenExtension j R S c) ∧
      PreservesFiniteColimits (proEtaleRingOpenExtension j R S c) := sorry

/-- Additivity of extension by zero. Source: proper base change, definition 1268
(blueprint: def-weil-pbc-projection-compactification). -/
instance proEtaleRingOpenExtension_additive :
    (proEtaleRingOpenExtension j R S c).Additive :=
  (proEtaleRingOpenExtension_exact j R S c).1

/-- Left exactness of extension by zero. Source: proper base change, definition 1268
(blueprint: def-weil-pbc-projection-compactification). -/
instance proEtaleRingOpenExtension_limits :
    PreservesFiniteLimits (proEtaleRingOpenExtension j R S c) :=
  (proEtaleRingOpenExtension_exact j R S c).2.1

/-- Right exactness of extension by zero. Source: proper base change, definition 1268
(blueprint: def-weil-pbc-projection-compactification). -/
instance proEtaleRingOpenExtension_colimits :
    PreservesFiniteColimits (proEtaleRingOpenExtension j R S c) :=
  (proEtaleRingOpenExtension_exact j R S c).2.2

/-- Exact termwise extension by zero on the full unbounded derived category.
Source: proper base change, definition 1268
(blueprint: def-weil-pbc-projection-compactification). -/
abbrev proEtaleRingDerivedOpenExtension :=
  (proEtaleRingOpenExtension j R S c).mapDerivedCategory

/-- Compact-support image for the chosen quasi-compact open / proper factorization.
For proper f, Compactification.ofIsProper f is its identity compactification.
Source: proper base change, definition 1268
(blueprint: def-weil-pbc-projection-compactification). -/
def proEtaleRingCompactSupportImage {Y : Scheme.{u}} {f : X ⟶ Y}
    (d : Compactification f) [QuasiCompact d.i]
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology d.Z) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (cp : (proEtaleSheafInverseImage d.g CommRingCat.{u + 1}).obj RY ≅ RZ)
    (cj : (proEtaleSheafInverseImage d.i CommRingCat.{u + 1}).obj RZ ≅ RX) :
    DerivedCategory (proEtaleRingModules X RX) ⥤ DerivedCategory (proEtaleRingModules Y RY) :=
  proEtaleRingDerivedOpenExtension d.i RZ RX cj ⋙ proEtaleRingDerivedDirectImage d.g RY RZ cp

end AlgebraicGeometry.Scheme
