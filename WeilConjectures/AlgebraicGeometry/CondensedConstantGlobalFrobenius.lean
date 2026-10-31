/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGlobalProperFrobenius
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.GeometricHypotheses
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections

/-! # Constant condensed coefficients and global geometric Frobenius

Source: latest blueprint, def-weil-global-geometric-frobenius, ordinary composite
(blueprint: def-weil-global-geometric-frobenius).

The existing interface is retained. The general coefficient version below also admits Q_l,
needed before extension to Qbar_l. Its arrows are the published transport and coefficient unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedConstant

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual pulled-back condensed coefficient unit, placed in degree zero.
Source: latest blueprint, constant coefficients (blueprint: def-weil-global-geometric-frobenius).
-/
def unit (X : Scheme.{u}) : CondensedRing.CohomologyTransport.D Λ X :=
  (DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)

/-- The coefficient-unit Weil isomorphism, with the exact derived-pullback comparison.
Source: latest blueprint, canonical constant Weil structure
(blueprint: def-weil-global-geometric-frobenius). -/
def unitWeil {X : Scheme.{u}} (g : X ≅ X) :
    (CondensedRing.CohomologyTransport.L Λ g.hom).obj (unit Λ X) ≅ unit Λ X :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g.hom).app _ ≪≫
    ((CondensedRing.upperStar Λ g.hom).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (CondensedRing.StrictWeil.unitWeilModule Λ g).str

/-- The ordinary global composite for every underlying condensed Weil complex.
Source: latest blueprint, F = RΓ(theta) after t_g
(blueprint: def-weil-global-geometric-frobenius). -/
def globalOrdinary (k : Type u) [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (a : Y ⟶ Spec (.of k)) [QuasiCompact a]
    (g : Y ⟶ Y) [IsIso g] (b : Spec (.of k) ⟶ Spec (.of k)) [IsIso b]
    (w : g ≫ a = a ≫ b) (K : CondensedRing.CohomologyTransport.D Λ Y)
    (theta : (CondensedRing.CohomologyTransport.L Λ g).obj K ≅ K) :=
  CondensedRing.CohomologyTransport.t Λ a a b g w K ≫
    (CondensedRing.CohomologyTransport.Γ Λ (Spec (.of k))).map
      ((CondensedRing.CohomologyTransport.R Λ a).map theta.hom)

/-- Compact global Frobenius is the actual compact transport followed by RΓ_c(theta).
The normalized compactification laws fix the transport, rather than an arbitrary arrow.
Source: latest blueprint, the displayed compact composite
(blueprint: def-weil-global-geometric-frobenius). -/
def globalCompact (k : Type u) [Field k] [IsAlgClosed k]
    (P : {S : CondensedRing.CohomologyTransport.CompactData Λ (Spec (.of k)) //
      CondensedRing.CohomologyTransport.Laws Λ S})
    {Y : Scheme.{u}} (a : Y ⟶ Spec (.of k)) [QuasiCompact a]
    (c : Compactification a) (g : Y ⟶ Y) [IsIso g]
    (b : Spec (.of k) ⟶ Spec (.of k)) [IsIso b] (w : g ≫ a = a ≫ b)
    (K : (boundedConstructible (condensedRingObj Λ Y)).FullSubcategory)
    (theta : (CondensedRing.CohomologyTransport.L Λ g).obj K.obj ≅ K.obj) :=
  CondensedRing.CohomologyTransport.tc Λ P.val a a b g w c c K
      ((boundedConstructible (condensedRingObj Λ Y)).prop_of_iso theta.symm K.property) ≫
    (CondensedRing.CohomologyTransport.Γ Λ (Spec (.of k))).map
      ((CondensedRing.CohomologyTransport.C Λ c).map theta.hom)

/-- The ordinary composite specialized to the canonical coefficient-unit Weil complex.
Source: latest blueprint, F on constant coefficients
(blueprint: def-weil-global-geometric-frobenius). -/
def ordinary (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :=
  letI := Fintype.ofFinite D.k₀
  globalOrdinary Λ D.k (D.geometricFiber X₀).hom (D.geometricFrobenius X₀).hom
    (CondensedRing.StrictWeil.pointFrobenius D).hom
    (D.galoisMap_projections X₀.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).2 (unit Λ _)
    (unitWeil Λ (D.geometricFrobenius X₀))

end WeilConjectures.CondensedConstant
