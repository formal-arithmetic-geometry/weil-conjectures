/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # The specified morphism underlying a module local return

Source: the semilinear return construction in the local Frobenius definition and
its cohomology comparison (blueprint: def-zl-module-return-morphism).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures.CondensedReturn

/-- Evaluate an identity comparison with its target explicitly the given object.
Source: the point trivialization in the local return (blueprint: def-zl-module-return-morphism).
This is the existing component; the annotation avoids an extra identity-object wrapper. -/
def identityComponent {C : Type v} [Category.{w} C] {F : C ⥤ C}
    (e : F ≅ 𝟭 C) (M : C) : F.obj M ≅ M := e.app M

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The module morphism before applying scalar point sections: inverse point
trivialization, inverse compositor, the semilinear equality, compositor, and the
specified iterated Weil isomorphism. All arrows have the displayed module fibres
as endpoints.

Source: the local Frobenius construction, and the opening cohomology identification
in the iterate-trace proof (blueprint: def-zl-module-return-morphism).
Construction: evaluate the inverse canonical point trivialization at the fibre;
compose with the inverse pullback compositor, transport along the given equality,
and then compose the forward compositor and the pullback of the supplied Weil map.
No representative or choice of a module is made. -/
def moduleReturnMorphism {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (a : End T) (β : End (Spec (.of k)))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (φ : (CondensedRing.upperStar Λ a).obj M ≅ M) (z : Spec (.of k) ⟶ T)
    (h : z ≫ a = β ≫ z) : End ((CondensedRing.upperStar Λ z).obj M) :=
  (identityComponent (CondensedRing.upperStarIsoIdOfIsSepClosed Λ β)
      ((CondensedRing.upperStar Λ z).obj M)).inv ≫
    (CondensedRing.upperStarComp Λ β z).inv.app M ≫
      eqToHom (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M) h.symm) ≫
        (CondensedRing.upperStarComp Λ z a).hom.app M ≫
          (CondensedRing.upperStar Λ z).map φ.hom

end WeilConjectures.CondensedReturn
