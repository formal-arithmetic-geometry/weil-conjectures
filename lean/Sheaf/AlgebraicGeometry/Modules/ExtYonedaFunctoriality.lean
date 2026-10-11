/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology

/-!
# Functoriality of Ext and the structure-sheaf cohomology comparison

Source: Stacks Project, Derived Categories, Tag 06XP; Cohomology, Tag 01DZ
(blueprint: lem-sc-p1-ext-yoneda-functoriality).
-/

@[expose] public section

universe u₁

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Ext maps are Yoneda composition with degree-zero morphisms, and the canonical
structure-sheaf Ext-cohomology identification `locallyFreeUnitExtAddEquivH` of
lem-sc-ext-locally-free commutes with coefficient morphisms.
The final formula transports a cohomology class back to Ext, composes with the
coefficient morphism, and transports forward again; this is the meaning of phi[i] composed
with a cohomology class under the identification.
Source: Stacks Project, Derived Categories, Tags 06XP and 06XR; Cohomology, Tag 01DZ
(blueprint: lem-sc-p1-ext-yoneda-functoriality).

Proof: (1) By lem-weil-pbc-ext-via-injective-resolution, compute Ext in the derived
category. The maps of def-pc-ext are precomposition with u[0] and postcomposition with
phi[0][i]. (2) By lem-sc-ext-yoneda-composition-derived these compositions are the Yoneda
products of lem-sc-p1-ext-yoneda-associativity; their degree-zero cases give both formulas.
(3) Specialize lem-sc-ext-locally-free-second-naturality to the structure sheaf.
The comparison of lem-sc-ext-locally-free becomes Ext(O,G) = H(i,G), and its naturality
identifies the Ext map with the map of def-sc-sheaf-cohomology-functor. Apply the same
square to the inverse image of x to obtain the last formula. -/
theorem ext_yoneda_functoriality {X : Scheme.{u₁}} [HasExt.{u₁} X.Modules]
    (F F' G G' : X.Modules) (i : ℕ) (e : Ext F G i)
    (u : F' ⟶ F) (φ : G ⟶ G') :
    (((Abelian.extFunctor (C := X.Modules) i).map u.op).app G) e =
        (Abelian.Ext.mk₀ (C := X.Modules) u).comp e (zero_add i) ∧
    ((Abelian.extFunctorObj (C := X.Modules) F i).map φ) e =
        e.comp (Abelian.Ext.mk₀ (C := X.Modules) φ) (add_zero i) ∧
    (∀ a : Ext (SheafOfModules.unit X.ringCatSheaf) G i,
      locallyFreeUnitExtAddEquivH (X := X) G' i
          (((Abelian.extFunctorObj (C := X.Modules)
            (SheafOfModules.unit X.ringCatSheaf) i).map φ) a) =
        H.map φ i (locallyFreeUnitExtAddEquivH (X := X) G i a)) ∧
    (∀ x : G.H i,
      H.map φ i x =
        locallyFreeUnitExtAddEquivH (X := X) G' i
          (((locallyFreeUnitExtAddEquivH (X := X) G i).symm x).comp
            (Abelian.Ext.mk₀ (C := X.Modules) φ) (add_zero i))) := sorry

end AlgebraicGeometry.Scheme.Modules
