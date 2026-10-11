/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
import Sheaf.CategoryTheory.CommAlgebraSheafModule
import Sheaf.AlgebraicGeometry.CechH1MapNatural
import Sheaf.AlgebraicGeometry.ModuleCohomologyBoundary
import Sheaf.Paper.PQFCohomology

/-! # Boundary classes represented by differences of local lifts

Source: Stacks Project, Cohomology, Tags 0B8R and 0B8S, local-lift paragraph
(blueprint: lem-sc-boundary-cech-local-lifts).
-/

universe u wC wD

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Differences of local lifts give an ideal-valued cocycle representing the boundary.
The exact sequence is in modules; its middle and quotient terms are algebra sheaves.
The kernel need not be a unital algebra. The assertion is uniform in the global section
and chosen lifts, so applies simultaneously to any two such choices.
Source: Stacks Project, Cohomology, Tags 0B8R and 0B8S, local-lift paragraph
(blueprint: lem-sc-boundary-cech-local-lifts).

Proof:
1. Exactness identifies the overlap differences with sections of I. The alternating sum
on triples telescopes to zero (def-weil-pbc-site-cech-complex).
2. Apply lem-sc-boundary-cech-compatibility to the underlying module sequence. The
canonical comparison sends the class to the connecting class, with the local-lift sign
convention of Tag 0B8S.
3. The comparison is injective by lem-sc-cech-h1-injective and is the canonical map of
lem-sc-cech-h1-map-natural. Repeat for any other section and lifts. -/
theorem boundary_cech_local_lifts (X : Scheme.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C) (I : X.Modules)
    (j : I ⟶ B.toModule)
    (hzero : j ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (hshort : (ShortComplex.mk j
      ((commAlgebraSheafModuleFunctor X.sheaf).map p) hzero).ShortExact)
    (hsquare : ∀ (W : X.Opens) (a a' : I.val.obj (op W)),
      (@id (B.right.obj.obj (op W)) (j.val.app (op W) a)) *
        (@id (B.right.obj.obj (op W)) (j.val.app (op W) a')) = 0)
    {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤) :
    ∃ c : ((CategoryTheory.cechComplexFunctor U).obj I.presheafModuleCat).homology 1 ⟶
        (RingedSpace.moduleCohomology X.toRingedSpace 1).obj I,
      IsModuleCechComparison U I 1 c ∧ Function.Injective c ∧
      ∀ (f : C.right.obj.obj (op ⊤))
        (t : ∀ i : ι, B.right.obj.obj (op (U i))),
        (∀ i : ι, p.right.hom.app (op (U i)) (t i) =
          C.right.obj.map (homOfLE (le_top : U i ≤ ⊤)).op f) →
        ∃ z : ((CategoryTheory.cechComplexFunctor U).obj I.presheafModuleCat).cycles 1,
          (∀ x : Fin 2 → ι,
            j.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (x k)))
              ((Pi.π (fun y : Fin 2 → ι ↦
                I.presheafModuleCat.obj (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))) x)
                (((CategoryTheory.cechComplexFunctor U).obj I.presheafModuleCat).iCycles 1 z)) =
              B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (x k)) 0).op (t (x 0)) -
                B.right.obj.map (Pi.π (fun k : Fin 2 ↦ U (x k)) 1).op (t (x 1))) ∧
          c (((CategoryTheory.cechComplexFunctor U).obj I.presheafModuleCat).homologyπ 1 z) =
            RingedSpace.moduleCohomologyBoundary X.toRingedSpace
              (ShortComplex.mk j
                ((commAlgebraSheafModuleFunctor X.sheaf).map p) hzero) hshort 0
              ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
                C.toModule f) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
