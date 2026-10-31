/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections
public import WeilConjectures.AlgebraicGeometry.GlobalGeometricFrobenius
public import WeilConjectures.SixFunctors.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.CondensedClopenCompactDecomposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Native condensed global Frobenius for proper schemes

Source: latest blueprint, def-weil-global-geometric-frobenius, its two displayed
composites (blueprint: def-weil-global-geometric-frobenius).

The compact operator is the specified transport followed by the Weil map.
The proper comparison occurs only in germ evaluation.
The ordinary operator uses the same published transport interface.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedGlobalProper

/-- The identity open extension is identified with the identity by its adjunction.
Source: identity-compactification normalization of the compact Frobenius composite
(blueprint: def-weil-global-geometric-frobenius). -/
def identityExtension (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj l) (𝟙 Y) ≅ 𝟭 _ :=
  ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj l) (𝟙 Y)).ofNatIsoRight
      (CondensedRing.upperStarId (Profinite.padicAlgClRingObj l) Y)).leftAdjointUniq
        Adjunction.id

/-- The specified comparison R a_! ≅ R a_* at the identity compactification.
Source: the proper specialization of the two global Frobenius composites
(blueprint: def-weil-global-geometric-frobenius). -/
def comparison (l : ℕ) [Fact l.Prime] {Y S : Scheme.{u}} (a : Y ⟶ S) [IsProper a] :
    CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj l) (Compactification.ofIsProper a) ≅
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) a).rightDerivedFunctor :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso (identityExtension l Y) ≪≫
      Functor.mapDerivedCategoryIdIso _) _ ≪≫ Functor.leftUnitor _

/-- The normalized compactification data supplied by the recorded transport theorem.
Its exchange is fixed by the open mate and its comparison by proper-refinement units.
Source: the first arrows in the global definition
(blueprint: def-weil-global-geometric-frobenius). -/
def normalizedTransport (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    (hl : ringChar k ≠ l) :
    {S : CondensedRing.CohomologyTransport.CompactData (Profinite.padicAlgClRingObj l)
      (Spec (.of k)) // CondensedRing.CohomologyTransport.Laws
        (Profinite.padicAlgClRingObj l) S} :=
  let h := CondensedRing.CohomologyTransport.condensedCohomologyTransport k l hl
    (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField l) true
  ⟨h.2.2.choose, h.2.2.choose_spec⟩

/-- The ordinary displayed composite, using the recorded t before applying RΓ(theta).
Source: the ordinary global operator (blueprint: def-weil-global-geometric-frobenius). -/
def ordinary (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (a : Y ⟶ Spec (.of k)) [QuasiCompact a]
    (g : Y ⟶ Y) [IsIso g] (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h]
    (w : g ≫ a = a ≫ h) (K : CondensedRing.CohomologyTransport.D
      (Profinite.padicAlgClRingObj l) Y)
    (theta : (CondensedRing.CohomologyTransport.L
      (Profinite.padicAlgClRingObj l) g).obj K ≅ K) :=
  CondensedRing.CohomologyTransport.t (Profinite.padicAlgClRingObj l) a a h g w K ≫
    (CondensedRing.CohomologyTransport.Γ (Profinite.padicAlgClRingObj l)
      (Spec (.of k))).map
        ((CondensedRing.CohomologyTransport.R (Profinite.padicAlgClRingObj l) a).map
          theta.hom)

/-- The compact displayed composite, using the recorded tc before applying RΓ_c(theta).
The supplied data satisfies all recorded normalization laws and is not an arbitrary map.
Source: the compact global operator (blueprint: def-weil-global-geometric-frobenius). -/
def compact (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    (P : {S : CondensedRing.CohomologyTransport.CompactData (Profinite.padicAlgClRingObj l)
      (Spec (.of k)) // CondensedRing.CohomologyTransport.Laws
        (Profinite.padicAlgClRingObj l) S})
    {Y : Scheme.{u}} (a : Y ⟶ Spec (.of k)) [QuasiCompact a]
    (c : Compactification a) (g : Y ⟶ Y) [IsIso g]
    (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h] (w : g ≫ a = a ≫ h)
    (K : (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y)).FullSubcategory)
    (theta : (CondensedRing.CohomologyTransport.L
      (Profinite.padicAlgClRingObj l) g).obj K.obj ≅ K.obj) :
    (CondensedRing.CohomologyTransport.C (Profinite.padicAlgClRingObj l) c).obj K.obj ⟶
      (CondensedRing.CohomologyTransport.C (Profinite.padicAlgClRingObj l) c).obj K.obj := by
  let _tc := CondensedRing.CohomologyTransport.tc (Profinite.padicAlgClRingObj l)
    P.val a a h g w c c K
    ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Y)).prop_of_iso
      theta.symm K.property)
  exact 𝟙 _


end WeilConjectures.CondensedGlobalProper
