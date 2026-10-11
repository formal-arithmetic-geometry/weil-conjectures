/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Sheaf.Paper.PQFCohomology

/-!
# Theorem on formal functions over a complete Noetherian base ring

Source: Stacks Project, Cohomology of Schemes, Lemma 087U
(blueprint: lem-weil-pbc-formal-functions-complete-base).

The index n represents the positive level n+1. H^p and Γ are A-modules by restriction of
scalars along (ΓSpecIso A).inv ≫ f.appTop, as in lem-weil-pbc-theorem-formal-functions.
The isomorphism is specified on every limit projection, so it is the canonical map.
The degree-zero assertion uses actual global sections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry

/-- For a proper scheme over a complete Noetherian base, coherent cohomology is the
inverse limit of the cohomology of the infinitesimal quotients, as A-modules.
Source: Stacks Project, Cohomology of Schemes, Lemma 087U
(blueprint: lem-weil-pbc-formal-functions-complete-base).

Proof: By lem-pc-coherent-hi (Lemma 02O6), the cohomology module H is finite over A.
By lem-weil-pbc-finite-module-complete-over-complete-noetherian (Algebra, Lemma 00MA),
the completion map c : H → H^ is bijective. By lem-weil-pbc-theorem-formal-functions
(Theorem 02OC), the map θ identifies the
resulting completion with the inverse limit of the cohomology of the quotients;
the map in the statement is the composite of these two canonical isomorphisms:
its nth projection sends x to the image of x under the quotient-induced map,
since the formal-functions map sends x modulo I^(n+1) to that same image.
Thus the composite has the displayed projections and is an isomorphism.
-/
theorem formalFunctions_complete_base
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : CoherentModules X) (p : ℕ) :
    ∃ e : (RingedSpace.moduleCohomology X.toRingedSpace p ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F.obj ≅
      limit (formalCompletionSystem
        ((Scheme.IdealSheafData.ofIdealTop
          (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) F.obj ⋙
        (RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)),
      ∀ n : ℕ, e.hom ≫ limit.π (formalCompletionSystem
          ((Scheme.IdealSheafData.ofIdealTop
            (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) F.obj ⋙
          (RingedSpace.moduleCohomology X.toRingedSpace p ⋙
            ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)) (op n) =
        (RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
          (formalModuleQuotientπ
            ((Scheme.IdealSheafData.ofIdealTop
              (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
            (n + 1) F.obj) := by
  sorry

/-- The degree-zero case: global sections are the inverse limit of the global sections of
the infinitesimal quotients, as A-modules.
Source: Stacks Project, Cohomology of Schemes, Lemma 087U, p = 0
(blueprint: lem-weil-pbc-formal-functions-complete-base).

Proof: H^0 is global sections (the zeroth right derived functor of the left-exact
global-sections functor), naturally in the module; transport formalFunctions_complete_base
at p = 0 along this natural isomorphism, which carries the quotient-induced maps to the
quotient-induced maps on global sections.
-/
theorem globalSections_formalFunctions_complete_base
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : CoherentModules X) :
    ∃ e : (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F.obj ≅
      limit (formalCompletionSystem
        ((Scheme.IdealSheafData.ofIdealTop
          (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) F.obj ⋙
        (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)),
      ∀ n : ℕ, e.hom ≫ limit.π (formalCompletionSystem
          ((Scheme.IdealSheafData.ofIdealTop
            (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) F.obj ⋙
          (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
            ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)) (op n) =
        (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
          (formalModuleQuotientπ
            ((Scheme.IdealSheafData.ofIdealTop
              (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
            (n + 1) F.obj) := by
  sorry

end AlgebraicGeometry
