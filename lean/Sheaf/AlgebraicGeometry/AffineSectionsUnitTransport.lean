/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Transport of the sections unit along the canonical affine isomorphism -/

@[expose] public section

set_option autoImplicit false
universe u w wA
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- Transport invertibility of the sections comparison across the canonical affine
isomorphism, for an arbitrary complex of module sheaves on its spectrum.
Source: Stacks Project, Tag 06Z0, identification of derived sections; the transport
argument below is written by the second reader.
(blueprint: new-affine-sections-unit-transport)

Proof: Put X = Spec Γ(S, top), E = restriction along S.toSpecΓ, and
G = sections on X followed by scalar restriction along (ΓSpecIso Γ(S, top)).inv.
Since S is affine, S.toSpecΓ is an isomorphism. Restriction along its inverse is
inverse to E: restrictFunctorComp, restrictFunctorCongr and restrictFunctorId
give both composites. Hence E is an exact equivalence and preserves K-injective
complexes. Evaluation of restrictAppIso at the top open, whose image is top,
gives E followed by sections on S naturally isomorphic to G. The scalar relation
is S.toSpecΓ.appTop = (ΓSpecIso Γ(S, top)).hom, so its inverse is precisely the
scalar restriction in G, not the hom in the other direction.
Choose a K-injective resolution i : C -> I. Its image E(i) is a K-injective
resolution of E(C). In these resolution models the two right-derived units are
the localized maps G(i) and Γ_S(E(i)), respectively. The preceding natural
isomorphism identifies these maps up to invertible endpoint maps. Therefore
invertibility of the first implies invertibility of the second. Uniqueness of
right-derived functors, compatible with their units, transfers this conclusion
to the independently chosen derived categories in the statement. Neither
boundedness nor quasi-coherence is needed. For the zero ring, zero complex,
and identity affine isomorphism the same equivalence and resolution argument
applies without a nonzero-object assumption. -/
theorem affineSectionsUnit_transport (S : Scheme.{u}) [IsAffine S]
    [(Scheme.Modules.restrictFunctor S.toSpecΓ).Additive]
    (C : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec Γ(S, ⊤)).toRingedSpace)) ℤ)
    (h : IsIso ((RingedSpace.globalSectionsFunctor (Spec Γ(S, ⊤)).toRingedSpace ⋙
      ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(S, ⊤)).inv.hom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj C))) :
    IsIso ((RingedSpace.globalSectionsFunctor S.toRingedSpace).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((Scheme.Modules.restrictFunctor S.toSpecΓ).mapHomologicalComplex (.up ℤ)).obj C))) :=
  by sorry

end AlgebraicGeometry
