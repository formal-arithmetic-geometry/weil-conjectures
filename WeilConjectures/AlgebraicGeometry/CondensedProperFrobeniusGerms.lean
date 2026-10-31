/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.CondensedGlobalProperFrobenius
public import WeilConjectures.AlgebraicGeometry.GlobalGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.ProperSectionsSemilinearGerms
import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.AlgebraicGeometry.ProperCompactCoincidence
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.CategoryTheory.RightDerivedBaseChangeZeroUnit
import WeilConjectures.SixFunctors.FrobeniusSquareCartesian
import WeilConjectures.AlgebraicGeometry.ClosedPointField

import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPoint
import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Proper condensed sections and geometric Frobenius germs

Source: latest blueprint, sec-deligne-laumon-a1/sk-thm-dl-a1-upper/
lem-a1-finite-boundary-weights.proof.md, opening evaluation and local stability
(blueprint: lem-a1-condensed-proper-frobenius-germs).

All sections and fibres use actual condensed modules. Positive exponents are indexed by n+1.
The scalar lift is the same canonical lift used by CondensedModule.fibre and pointSections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedProperGerms

variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
  (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom]

/-- Exact pullback of the degree-zero module gives its derived Weil isomorphism.
Source: the node's actual-module hypothesis and exactness in proof step 1
(blueprint: lem-a1-condensed-proper-frobenius-germs). -/
def singleWeil
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom) :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l)
    (D.geometricFrobenius Y₀).hom).app
      ((DerivedCategory.singleFunctor _ 0).obj M.carrier) ≪≫
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom).mapDerivedCategorySingleFunctor 0).app M.carrier ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso M.str

/-- Degree-zero compact cohomology, with exact geometric evaluation after homology.
This is H^0(Fib_s(Ra_! M[0])) since pointSections is exact.
Source: def-weil-ordinary-compact-cohomology, displayed H_c formula
(blueprint: lem-a1-condensed-proper-frobenius-germs). -/
abbrev sections :=
  DerivedCategory.singleFunctor (CondensedModule.Modules l (D.geometricFiber Y₀).left) 0 ⋙
    CondensedRing.rightDerivedLowerShriekOfCompactification
      (Profinite.padicAlgClRingObj l)
      (Compactification.ofIsProper (D.geometricFiber Y₀).hom) ⋙
    DerivedCategory.homologyFunctor _ 0 ⋙ CondensedRing.pointSections l D.k

/-- The actual compact global geometric Frobenius on degree-zero cohomology.
Source: def-weil-global-geometric-frobenius; proof step 3
(blueprint: lem-a1-condensed-proper-frobenius-germs). -/
def frobenius (hl : l ≠ D.p)
    (M : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom) : End ((sections l D Y₀).obj M.obj.carrier) := by
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  have hcard : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hcard
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact (CondensedRing.pointSections l D.k).map ((DerivedCategory.homologyFunctor _ 0).map
    (CondensedGlobalProper.compact l D.k
      (CondensedGlobalProper.normalizedTransport l D.k
        (by simpa only [ringChar.eq D.k D.p] using hl.symm))
      (D.geometricFiber Y₀).hom (Compactification.ofIsProper (D.geometricFiber Y₀).hom)
      (D.geometricFrobenius Y₀).hom (frobeniusPointIso D).hom
      (D.galoisMap_projections Y₀.hom
        (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
          (Fintype.ofFinite D.k₀) _ _ _)).2
      (condensedWeilSingle l (D.geometricFrobenius Y₀).hom M)
      (singleWeil l D Y₀ M.obj)))

/-- Canonical proper/augmentation comparison with ordinary sections of a_*M.
Source: proof steps 2--3, H^0(Ra_*M[0])=a_*M and identity compactification
(blueprint: lem-a1-condensed-proper-frobenius-germs). -/
def sectionsComparison (M : CondensedModule.Modules l (D.geometricFiber Y₀).left) :
    (sections l D Y₀).obj M ≅
      (CondensedRing.pointSections l D.k).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (D.geometricFiber Y₀).hom).obj M) :=
  (CondensedRing.pointSections l D.k).mapIso
    ((DerivedCategory.homologyFunctor _ 0).mapIso
      ((CondensedGlobalProper.comparison l (D.geometricFiber Y₀).hom).app
        ((DerivedCategory.singleFunctor _ 0).obj M)) ≪≫
      (Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (D.geometricFiber Y₀).hom)).app M)

/-- The canonical germ: proper comparison, degree-zero augmentation, identity pullback,
then the actual pullback-composition/counit restriction.
Source: proof step 7 and the opening evaluation sentence
(blueprint: lem-a1-condensed-proper-frobenius-germs). -/
def evaluation (M : CondensedModule.Modules l (D.geometricFiber Y₀).left)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    (sections l D Y₀).obj M ⟶ CondensedModule.fibre l D M z :=
  (sectionsComparison l D Y₀ M).hom ≫ (CondensedRing.pointSections l D.k).map
    ((CondensedRing.upperStarId (Profinite.padicAlgClRingObj l) (Spec (.of D.k))).inv.app
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (D.geometricFiber Y₀).hom).obj M) ≫
      CondensedRing.stalkLowerStarProj (Profinite.padicAlgClRingObj l) hz M)

/-- The specified r-fold Weil and point-comparison map, at r=n+1.
Source: proof steps 8--10, the ordered Weil iterate and its canonical compositors
(blueprint: lem-a1-condensed-proper-frobenius-germs). -/
@[irreducible] def transport
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ) :=
  CondensedModule.transport l D (D.geometricFrobenius Y₀).hom M.carrier M.str z
    (ProperSemilinearGerms.movingPoint D Y₀ z n) n
    (ProperSemilinearGerms.movingPoint_properties D Y₀ z hz n).2.symm

/-- Proper germ evaluation intertwines global and moving-point Frobenius and returns
at a closed point to its degree-normalized local geometric Frobenius.

Source: latest blueprint, lem-a1-finite-boundary-weights.proof.md, opening evaluation
and local stability (blueprint: lem-a1-condensed-proper-frobenius-germs).

Proof, following the node's twelve steps:
1. Closed monoidal Grothendieck sheaves and modules have enough injectives
(lem-weil-pbc-sheaf-tensor-closed, lem-sfb-modobj-grothendieck,
lem-sp-grothendieck-enough-injectives). Pullback is exact
(det-prop-sfb-module-pullback-exact-main); direct image is left exact.
2. A nonnegative injective resolution computes Ra_* and has H^0=a_*M
(lem-weil-pbc-left-exact-injective-resolution-degree-zero,
lem-weil-pbc-dplus-injective-representative). Exact point sections commute with H^0
(lem-weil-point-proetale-sections-exact), giving ordinary sections and fibres.
3. The identity compactification gives kappa:Ra_!~Ra_*. Its exchange compatibility
(lem-a1-condensed-proper-exchange-comparison) and naturality for theta identify
compact Frobenius with ordinary Frobenius under kappa.
4. Sections are maps from the regular coefficient module; m corresponds to m(1).
Pullback is f*(m)c_f^-1 (lem-sfb-internal-module-operations-transport,
det-def-sfb-coefficient-morphisms, det-def-sfb-module-pushforward-pullback).
5. The derived exchange is the unit--square--counit mate
(def-weil-pbc-adjunction-mate, det-def-sf-exchanges,
def-sfb-module-derived-pushpull-adjunction). Its H^0 is the ordinary exchange by
lem-sbc-right-derived-base-change-zero-unit.
6. Transpose that mate on a section and use coefficient-compositor compatibility:
the actual ordinary operator is m |-> theta g*(m)c_g^-1, hence scalar linear.
7. Pullback by g^-1 and theta^-1 give its inverse. Evaluation is z*(m)c_z^-1,
the same counit germ as evaluation above.
8. For z_1=Tz, gz=z_1 h. Pullback composition and point transport give
e_z F=B_(1,z)e_z1. Every factor of B is an isomorphism.
9. Iterate the one-step identity by induction, obtaining the ordered product of B's.
10. Naturality of compositors identifies this product with the contracted Weil iterate
in CondensedModule.transport, with no additional path or scalar choice.
11. The closed residue field has q^d elements (lem-kun-closed-point-field).
Finite-field Frobenius has order d (lem-sfb-finite-field-galois-frobenius), so
T^d z=z. The resulting contracted comparison is exactly CondensedModule.operator,
with index d-1 (def-weil-local-frobenius-trace).
12. The equation f theta_M=theta_N g*f, functoriality of evaluation and naturality
of all compositors give the three displayed naturality equations. All constructions
are valid on zero modules and the empty scheme; no finite-morphism assumption is used.
-/
theorem proper_frobenius_germs (hl : l ≠ D.p)
    (M : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom) :
    IsIso (frobenius l D Y₀ hl M).asHom ∧
    (∀ (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
      (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ),
      ((frobenius l D Y₀ hl M) ^ (n + 1)).asHom ≫ evaluation l D Y₀ M.obj.carrier z hz =
        evaluation l D Y₀ M.obj.carrier (ProperSemilinearGerms.movingPoint D Y₀ z n)
          (ProperSemilinearGerms.movingPoint_properties D Y₀ z hz n).1 ≫
            (transport l D Y₀ M.obj z hz n).hom) ∧
    (∀ (x : {x : Y₀.left // x ∈ closedPoints Y₀.left})
      (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
      (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _),
      (z ≫ pullback.fst Y₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).base
          (IsLocalRing.closedPoint D.k) = x.val →
      ∃ (ret : ProperSemilinearGerms.movingPoint D Y₀ z
          (localClosedPointDegree D Y₀ x - 1) = z)
        (hr : z ≫ localPositivePower (D.geometricFrobenius Y₀).hom
            (localClosedPointDegree D Y₀ x - 1) =
          localPositivePower (frobeniusPointIso D).hom
            (localClosedPointDegree D Y₀ x - 1) ≫ z),
      eqToHom (congrArg (CondensedModule.fibre l D M.obj.carrier) ret.symm) ≫
          (transport l D Y₀ M.obj z hz (localClosedPointDegree D Y₀ x - 1)).hom =
        CondensedModule.operator l D (D.geometricFrobenius Y₀).hom M.obj.carrier M.obj.str
          z (localClosedPointDegree D Y₀ x - 1) hr ∧
      ((frobenius l D Y₀ hl M) ^ localClosedPointDegree D Y₀ x).asHom ≫
          evaluation l D Y₀ M.obj.carrier z hz =
        evaluation l D Y₀ M.obj.carrier z hz ≫
          CondensedModule.operator l D (D.geometricFrobenius Y₀).hom M.obj.carrier M.obj.str
            z (localClosedPointDegree D Y₀ x - 1) hr) ∧
    (∀ (N : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom) (f : M ⟶ N),
      (sections l D Y₀).map f.hom.hom.f ≫ (frobenius l D Y₀ hl N).asHom =
        (frobenius l D Y₀ hl M).asHom ≫ (sections l D Y₀).map f.hom.hom.f ∧
      ∀ (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
        (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ),
        (sections l D Y₀).map f.hom.hom.f ≫ evaluation l D Y₀ N.obj.carrier z hz =
          evaluation l D Y₀ M.obj.carrier z hz ≫
              (CondensedRing.pointSections l D.k).map
                ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map
                  f.hom.hom.f) ∧
        (CondensedRing.pointSections l D.k).map
              ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
                (ProperSemilinearGerms.movingPoint D Y₀ z n)).map f.hom.hom.f) ≫
            (transport l D Y₀ N.obj z hz n).hom =
          (transport l D Y₀ M.obj z hz n).hom ≫
            (CondensedRing.pointSections l D.k).map
              ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map
                f.hom.hom.f)) := by
  sorry

end WeilConjectures.CondensedProperGerms
