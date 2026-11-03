/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedDncFamily
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionInvariantAllCoefficients2
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import WeilConjectures.AlgebraicGeometry.DeformationSpace.SmoothProj

/-! # DNC invariance for all four condensed coefficients

Source: latest blueprint,
part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/thm-pur-dnc-invariance.md
and its proof (blueprint: thm-pur-dnc-invariance).
The normal and Rees pairs are the actual schemes. Their fibre maps are the native
exceptional counit mates with canonical pullback compositors. Normalization compares the
one and zero restrictions of every constant presentation of the family after arbitrary
finite-type base change; thus no auxiliary orientation or arbitrary endpoint map is chosen.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

variable (D : WeilConjectures.FiniteFieldDatum.{u})

local instance datumPrime : Fact D.p.Prime := ⟨D.prime⟩
local instance datumChar : CharP D.k₀ D.p := by
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
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
    (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ N : ℕ, ∀ a : A, (ell ^ N) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))


/-- The literal coefficient unit, with exactly Q50's membership certificate.
Source: def-pur-section-invariant (blueprint: thm-pur-dnc-invariance). -/
def unitCtf (B : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] :
    ConstantModelConstructibleFiniteTor Λ B.left :=
  ⟨sectionInvariantUnit Λ B.left,
    sectionInvariantAllUnit_mem D ell hell E n hn Λ hcoeff B⟩

/-- The actual restricted Brown adjunction used by Q50's section invariant.
Source: def-pur-section-invariant (blueprint: thm-pur-dnc-invariance). -/
def exceptionalAdjunction {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : X ⟶ Y) :=
  letI : Fact (ringChar D.k ≠ ell) :=
    ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  ctfExceptionalAdjunction Λ ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) g
    (sectionInvariantAll_admissible D ell hell E n hn Λ hcoeff)

/-- The native relative dualizing object, with its actual Dctf certificate.
Source: def-pur-section-invariant, omega_g
(blueprint: thm-pur-dnc-invariance). -/
def dualizing {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : X ⟶ Y) : ConstantModelConstructibleFiniteTor Λ X.left :=
  letI : Fact (ringChar D.k ≠ ell) :=
    ⟨(ringChar.eq D.k D.p).symm ▸ hell.symm⟩
  (ctfExceptionalInverseImage Λ ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) g
    (sectionInvariantAll_admissible D ell hell E n hn Λ hcoeff)).obj
      (unitCtf D ell hell E n hn Λ hcoeff Y)

/-- The actual pullback preserves the Dctf predicate; no alternative pullback is chosen.
Source: compact-support coherence, pullback-preservation clause
(blueprint: thm-pur-dnc-invariance). -/
abbrev pullback_mem (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
    (hcoeff :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
      Finite A ∧ (∃ N : ℕ, ∀ a : A, (ell ^ N) • a = 0) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (X Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (v : X.left ⟶ Y.left) (K : ConstantModelConstructibleFiniteTor Λ Y.left) :
    (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
      ((moduleObjectDerivedPullback Λ v).obj K.obj) :=
  let P :=
    (coherence D (Λ := Λ) ell hell E n hn hcoeff).choose_spec.choose_spec.choose_spec.choose_spec
  (P.choose (SepFinType.mk X) (SepFinType.mk Y) v).2 K.obj K.property

/-- Project the normalized exchange function once from the published coherence witness.
Its proper/open and refinement equations remain those of that same witness.
Source: sk-thm-sf-comp-composition, exchange clause
(blueprint: thm-pur-dnc-invariance). -/
@[irreducible] def normalizedExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k]
    (h : CompactSupportComposition.Coherent Λ k) :
    ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
      (_sq : IsPullback a f'.hom.left f.hom.left v)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left),
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
          (rightDerivedLowerShriekOfCompactification Λ c ⋙ moduleObjectDerivedPullback Λ v) ≅
        (localizingClosureProEtale Λ X.obj.left).ι ⋙
          (moduleObjectDerivedPullback Λ a ⋙ rightDerivedLowerShriekOfCompactification Λ d) :=
  h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

set_option maxHeartbeats 2000000 in
-- Checking the large normalized coherence witness exceeds the default kernel heartbeat budget.
/-- The proper/open-normalized compact-support exchange, with the actual chosen
compactifications at both ends. Its normalization is part of the theorem selected, not
an arbitrary isomorphism of the endpoints.
Source: sk-thm-sf-comp-composition, exchange_normalized
(blueprint: thm-pur-dnc-invariance). -/
@[irreducible] def compactExchange (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
      Finite A ∧ (∃ N : ℕ, ∀ a : A, (ell ^ N) • a = 0) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    {X Y X' Y' : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (g : X ⟶ Y) (g' : X' ⟶ Y') (v : X'.left ⟶ X.left) (b : Y'.left ⟶ Y.left)
    (sq : IsPullback v g'.left g.left b) :=
  normalizedExchange Λ D.k (coherence D (Λ := Λ) ell hell E n hn hcoeff)
    (X := SepFinType.mk X) (Y := SepFinType.mk Y)
    (X' := SepFinType.mk X') (Y' := SepFinType.mk Y')
    (f := SepFinType.homMk g) (f' := SepFinType.homMk g') (a := v) (v := b)
    sq (compactificationOverField g) (compactificationOverField g')

/-- The native beta is the transpose of inverse compact-support exchange followed by
pullback of the exceptional counit and the monoidal unit comparison. This is condition
(3)'s map, including its normalization, in native condensed module objects; at finite
coefficients the normalized encoding gives the recorded finiteCompared beta.
Source: def-pur-co-smoothness (3), and sk-lem-geometry Step 5
(blueprint: thm-pur-dnc-invariance). -/
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
      pullback_mem D (Λ := Λ) ell hell E n hn hcoeff X' X v Ω⟩
  let H := sixOperationsLocalizingAdjunction Λ ell D.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k) g
    (sectionInvariantAll_admissible D ell hell E n hn Λ hcoeff)
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
(blueprint: thm-pur-dnc-invariance). -/
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

end AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

namespace AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

/-- Packaging of exactly the smooth separated finite-type closed-section situation.
Source: def-pur-dnc-section-family (blueprint: thm-pur-dnc-invariance). -/
structure Pair (D : WeilConjectures.FiniteFieldDatum.{u}) where
  B : Over (Spec (.of D.k))
  V : Over (Spec (.of D.k))
  [base_ft : LocallyOfFiniteType B.hom]
  [base_qc : QuasiCompact B.hom]
  [base_sep : IsSeparated B.hom]
  [source_ft : LocallyOfFiniteType V.hom]
  [source_qc : QuasiCompact V.hom]
  [source_sep : IsSeparated V.hom]
  g : V ⟶ B
  [smooth : Smooth g.left]
  [separated : IsSeparated g.left]
  [finite_type : LocallyOfFiniteType g.left]
  [qc : QuasiCompact g.left]
  s : B ⟶ V
  [closed : IsClosedImmersion s.left]
  section_eq : s ≫ g = 𝟙 B
attribute [instance] Pair.base_ft Pair.base_qc Pair.base_sep Pair.source_ft Pair.source_qc
  Pair.source_sep Pair.smooth Pair.separated Pair.finite_type Pair.qc Pair.closed

variable {D : WeilConjectures.FiniteFieldDatum.{u}}

end AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

namespace AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

variable {D : WeilConjectures.FiniteFieldDatum.{u}}
  (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff :
    (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ N : ℕ, ∀ a : A, (ell ^ N) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))

/-- The canonical one-fibre map, the exceptional counit mate pulled to the section.
Source: sk-lem-geometry (1), proof Step 5 (blueprint: thm-pur-dnc-invariance). -/
def atOne (Q : Pair D) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) Q.B.left)).obj
        (Q.F ell hell E n hn Λ hcoeff) ⟶ Q.C ell hell E n hn Λ hcoeff :=
  sectionBaseChangeMap D ell hell E n hn Λ hcoeff Q.rees.g Q.g
    (Scheme.Hom.deformationSpaceOneFibre Q.g.left Q.s.left)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) Q.B.left)
    (Scheme.Hom.isPullback_deformationSpaceOneFibre Q.g.left Q.s.left)
    Q.rees.s.left Q.s.left
    (Scheme.Hom.comp_deformationSpaceOneFibre
      (congrArg (fun f ↦ f.left) Q.section_eq))

/-- The canonical zero-fibre map, using the actual associated-graded normal cone.
Source: sk-lem-geometry (1), proof Step 5 (blueprint: thm-pur-dnc-invariance). -/
def atZero (Q : Pair D) :
    (moduleObjectDerivedPullback Λ
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Q.B.left)).obj
        (Q.F ell hell E n hn Λ hcoeff) ⟶ Q.normal.C ell hell E n hn Λ hcoeff :=
  sectionBaseChangeMap D ell hell E n hn Λ hcoeff Q.rees.g Q.normal.g
    Q.s.left.ker.normalConeToDeformationSpace
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Q.B.left)
    (Scheme.Hom.isPullback_normalConeToDeformationSpace Q.g.left Q.s.left)
    Q.rees.s.left Q.normal.s.left
    (by
      change Q.s.left.normalConeZeroSection ≫ Q.s.left.ker.normalConeToDeformationSpace =
        _
      exact Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace)

end AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

namespace AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Restrict a constant presentation of a family to a section after base change.
Every arrow is a canonical derived pullback compositor, the given fibre mate, or
restriction of the same presentation e. Source: sk-thm-dnc proof, restrictions of
kappa at one and zero (blueprint: thm-pur-dnc-invariance). -/
def sectionRestrictionIso {B B' A A' : Scheme.{u}}
    (b : B' ⟶ B) (i : B ⟶ A) (i' : B' ⟶ A') (a' : A' ⟶ B') (f : A' ⟶ A)
    (hbi : b ≫ i = i' ≫ f) (hia : i' ≫ a' = 𝟙 B')
    (F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1})
      (condensedRingObj Λ A)))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
      (condensedRingObj Λ B)))
    (C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B') Ab.{u + 1})
      (condensedRingObj Λ B')))
    (θ : (moduleObjectDerivedPullback Λ i).obj F ≅ C)
    (e : (moduleObjectDerivedPullback Λ f).obj F ≅
      (moduleObjectDerivedPullback Λ a').obj C₀) :
    (moduleObjectDerivedPullback Λ b).obj C ≅ C₀ :=
  (moduleObjectDerivedPullback Λ b).mapIso θ.symm ≪≫
    ((leftDerivedUpperStarComp Λ b i).app F).symm ≪≫
    eqToIso (congrArg (fun h ↦ (moduleObjectDerivedPullback Λ h).obj F) hbi) ≪≫
    (leftDerivedUpperStarComp Λ i' f).app F ≪≫
    (moduleObjectDerivedPullback Λ i').mapIso e ≪≫
    ((leftDerivedUpperStarComp Λ i' a').app C₀).symm ≪≫
    eqToIso (congrArg (fun h ↦ (moduleObjectDerivedPullback Λ h).obj C₀) hia) ≪≫
    (leftDerivedUpperStarId Λ B').app C₀

end AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance
