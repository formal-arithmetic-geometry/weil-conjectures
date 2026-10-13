/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.Topology.SheafIsomorphismLocalOpenCover
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Detection of quasi-isomorphisms on an affine principal-open cover

Source: Stacks Project, Tag 08EE, final sheafification, and Tags 01HV and 01IB
(blueprint: lem-sc-affine-principal-cover-quasi-iso-detection).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- Localized quasi-isomorphisms on a principal-open cover give an invertible
map on the open derived category. No pseudo-coherence or boundedness is required.
Source: Stacks Project, Tag 08EE, final sheafification step, and Tags 01HV and 01IB
(blueprint: lem-sc-affine-principal-cover-quasi-iso-detection).

Proof: The tilde sections formula, natural in module homomorphisms, identifies
termwise associated sheaf on D(f) with termwise tilde over A_f of localization.
Transport this natural comparison along X.isoSpec and hT. Tilde preserves colimits
by its adjunction. The kernel of a map between tilde modules is quasi-coherent;
its global sections are the module kernel, since sections preserve limits.
The affine adjunction counit therefore identifies it with tilde of that kernel.
Thus tilde is exact and preserves homology. A quasi-isomorphism after localization
becomes a quasi-isomorphism of the restricted associated-sheaf complexes on D(f).
Intersect these opens with U; since they are already contained in U, they form
an open cover of U.
Exact restriction commutes with homology. Each homology map on U is invertible
on this cover, hence is invertible globally by the local criterion for sheaf
isomorphisms. Thus the complex map restricted to U is a quasi-isomorphism.
The restriction localization comparison conjugates its image under Q to the
map in the conclusion. Q inverts quasi-isomorphisms, proving the assertion.
For an empty cover the covering hypothesis forces U to be empty; the same local
criterion applies vacuously. No unit-ideal hypothesis on the family is needed.
-/
theorem affine_principal_cover_quasiIso_detection
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (T : ModuleCat.{u} (X.presheaf.obj (.op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace)) [T.PreservesZeroMorphisms]
    (hT : Nonempty (T ≅ tilde.functor (X.presheaf.obj (.op ⊤)) ⋙
      Modules.restrictFunctor X.isoSpec.hom))
    (r : ℕ) (f : Fin r → X.presheaf.obj (.op ⊤))
    (hsub : ∀ j, X.basicOpen (f j) ≤ U)
    (hcover : ∀ x : X, x ∈ U → ∃ j, x ∈ X.basicOpen (f j))
    (F M : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op ⊤))) ℤ) (α : F ⟶ M)
    (hα : ∀ j : Fin r, QuasiIso ((Functor.mapHomologicalComplex
      (ModuleCat.extendScalars
        (algebraMap (X.presheaf.obj (.op ⊤)) (Localization.Away (f j))))
      (ComplexShape.up ℤ)).map α)) :
    IsIso (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.map
      (DerivedCategory.Q.map ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map α))) :=
  by sorry

end AlgebraicGeometry.Scheme
