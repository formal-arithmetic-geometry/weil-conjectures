/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionInvariant
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # The native dualizing and section base-change mates

Source: latest blueprint, def-pur-section-invariant and def-pur-co-smoothness (3),
and lem-pur-dnc-section-geometry.proof.md, Steps 5--7.
These helpers use the recorded restricted Brown adjunction and the proper/open-normalized
compact-support exchange. Thus they name the actual pro-etale beta, before asserting its
invertibility. No exceptional inverse image or base-change arrow is supplied as a hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.SectionGeometry

variable (D : WeilConjectures.FiniteFieldDatum.{u})

local instance datumPrime : Fact D.p.Prime := ⟨D.prime⟩
local instance datumChar : CharP D.k₀ D.p := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  exact charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
local instance closureChar : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
local instance closurePrime : Fact (ringChar D.k).Prime :=
  ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
local instance closureClosed : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀

variable (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff :
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
      (Padic.coefficientExtensionRing ell E n))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))


include ell hell E n hn hcoeff

/-- The literal coefficient unit, with exactly Q50's membership certificate.
Source: def-pur-section-invariant (blueprint: lem-pur-dnc-section-geometry, Step 5). -/
def unitCtf (B : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] :
    ConstantModelConstructibleFiniteTor Λ B.left :=
  ⟨sectionInvariantUnit Λ B.left,
    sectionInvariantUnit_mem D ell hell E n hn Λ hcoeff B⟩

/-- The actual restricted Brown adjunction used by Q50's section invariant.
Source: def-pur-section-invariant (blueprint: lem-pur-dnc-section-geometry, Step 5). -/
def exceptionalAdjunction {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : X ⟶ Y) :=
  letI : Fact (ringChar D.k ≠ ell) :=
    ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  ctfExceptionalAdjunction Λ ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) g
    (sectionInvariant_admissible D ell hell E n hn Λ hcoeff)

/-- The native relative dualizing object, with its actual Dctf certificate.
Source: def-pur-section-invariant, omega_g
(blueprint: lem-pur-dnc-section-geometry, Step 5). -/
def dualizing {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : X ⟶ Y) : ConstantModelConstructibleFiniteTor Λ X.left :=
  letI : Fact (ringChar D.k ≠ ell) :=
    ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  (ctfExceptionalInverseImage Λ ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) g
    (sectionInvariant_admissible D ell hell E n hn Λ hcoeff)).obj
      (unitCtf D ell hell E n hn Λ hcoeff Y)

/-- The native beta is the transpose of inverse compact-support exchange followed by
pullback of the exceptional counit and the monoidal unit comparison. This is condition
(3)'s map, including its normalization, in native condensed module objects; at finite
coefficients the normalized encoding gives the recorded finiteCompared beta.
Source: def-pur-co-smoothness (3), and sk-lem-geometry Step 5
(blueprint: lem-pur-dnc-section-geometry). -/
def dualizingBaseChangeMap {X Y X' Y' : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (g : X ⟶ Y) (g' : X' ⟶ Y') (v : X'.left ⟶ X.left) (b : Y'.left ⟶ Y.left)
    (sq : IsPullback v g'.left g.left b) :
    (moduleObjectDerivedPullback Λ v).obj (dualizing D ell hell E n hn Λ hcoeff g).obj ⟶
      (dualizing D ell hell E n hn Λ hcoeff g').obj :=
  letI : Fact (ringChar D.k ≠ ell) :=
    ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  let Ω := dualizing D ell hell E n hn Λ hcoeff g
  let K : ConstantModelConstructibleFiniteTor Λ X'.left :=
    ⟨(moduleObjectDerivedPullback Λ v).obj Ω.obj,
      pullback_mem D ell hell E n hn Λ hcoeff X' X v Ω⟩
  let H := sixOperationsLocalizingAdjunction Λ ell D.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k) g
    (sectionInvariant_admissible D ell hell E n hn Λ hcoeff)
  let Kloc : (localizingClosureProEtale Λ X.left).FullSubcategory :=
    ⟨Ω.obj, H.source_mem Ω.obj Ω.property⟩
  let e := compactExchange D ell hell E n hn Λ hcoeff g g' v b sq
  let ε := (exceptionalAdjunction D ell hell E n hn Λ hcoeff g).counit.app
    (unitCtf D ell hell E n hn Λ hcoeff Y)
  ((exceptionalAdjunction D ell hell E n hn Λ hcoeff g').homEquiv K
    (unitCtf D ell hell E n hn Λ hcoeff Y')
    (ObjectProperty.homMk (e.inv.app Kloc ≫
      (moduleObjectDerivedPullback Λ b).map ε.hom ≫
        (leftDerivedUpperStarUnitIso Λ b).hom))).hom

/-- Pull the actual native beta to the sections and compose the canonical pullback
compositors. The equality hsection identifies the same composite scheme map.
Source: def-pur-co-smoothness (3) at the sections
(blueprint: lem-pur-dnc-section-geometry, Steps 5--7). -/
def sectionBaseChangeMap {X Y X' Y' : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (g : X ⟶ Y) (g' : X' ⟶ Y') (v : X'.left ⟶ X.left) (b : Y'.left ⟶ Y.left)
    (sq : IsPullback v g'.left g.left b)
    (s : Y.left ⟶ X.left) (s' : Y'.left ⟶ X'.left)
    (hsection : s' ≫ v = b ≫ s) :
    (moduleObjectDerivedPullback Λ b).obj
        ((moduleObjectDerivedPullback Λ s).obj
          (dualizing D ell hell E n hn Λ hcoeff g).obj) ⟶
      (moduleObjectDerivedPullback Λ s').obj
        (dualizing D ell hell E n hn Λ hcoeff g').obj :=
  ((leftDerivedUpperStarComp Λ b s).app _).inv ≫
    eqToHom (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj
      (dualizing D ell hell E n hn Λ hcoeff g).obj) hsection.symm) ≫
    ((leftDerivedUpperStarComp Λ s' v).app _).hom ≫
    (moduleObjectDerivedPullback Λ s').map
      (dualizingBaseChangeMap D ell hell E n hn Λ hcoeff g g' v b sq)

end AlgebraicGeometry.ProEtale.CondensedRing.SectionGeometry
