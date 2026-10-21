/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech
public import Sheaf.Paper.StrictLocalKummerTameModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.RingTheory.PairHenselization
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.RingTheory.PairHenselizationNoetherianCompletion
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.RingTheory.IntegralOverHenselianPair
import WeilConjectures.RingTheory.HenselianFactorizationCriterion
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.WeaklyEtaleField
import WeilConjectures.RingTheory.RegularMapAscent
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Sheaf.RingTheory.RegularLocalLiftRegularSequenceQuotient
import WeilConjectures.RingTheory.RegularLocalLocalization
import Mathlib.GroupTheory.MonoidLocalization.Away
import Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum
import Sheaf.RingTheory.DirectedColimitFaithfullyFlatAlgebras
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.RingTheory.HenselizationUniversalProperty

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-! # Henselian SNC charts with universal residual covers

Source: Stacks 0A02, 0AGU, 0AGV, 09ZS; Bhatt--Scholze 7.4.3; ILO VIII 4.2.2(i),
IX Proposition 2.1 (blueprint: lem-sfb-snc-universal-residual-charts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The finite parameter-root quotient, including order one and the empty tuple.
Source: ILO IX Proposition 2.1 (blueprint: lem-sfb-snc-universal-residual-charts). -/
abbrev sncRootLevel {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) (n : ℕ) :=
  MvPolynomial (Fin r) R ⧸
    Ideal.span (Set.range (fun i ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i)))

/-- The root coordinate in the finite quotient.
Source: ILO IX Proposition 2.1 (blueprint: lem-sfb-snc-universal-residual-charts). -/
def sncRootCoordinate {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R)
    (n : ℕ) (i : Fin r) : sncRootLevel t n :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- The coordinate in the existing full compatible-root algebra.
Source: ILO IX Proposition 2.1 (blueprint: lem-sfb-snc-universal-residual-charts). -/
def sncFullRootCoordinate (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : TameRootOrder p) (i : Fin r) : tameRootAlgebra p t :=
  Ideal.Quotient.mk _ (MvPolynomial.X (i, n))

/-- Exactly the nonempty connected qcqs assertion for an affine ring spectrum.
Source: Stacks 0A02 and ILO IX 2.1
(blueprint: lem-sfb-snc-universal-residual-charts). -/
def SNCConnectedAffine (R : CommRingCat.{u}) : Prop :=
  ConnectedSpace (Spec R) ∧ CompactSpace (Spec R) ∧ QuasiSeparatedSpace (Spec R)

/-- The punctured finite and full root maps and their precise generator formulas.
The generator formulas determine every map uniquely. The full quotient is the existing
`tameRootAlgebra`, whose defining relations present the divisibility colimit.
Source: ILO IX Proposition 2.1 (blueprint: lem-sfb-snc-universal-residual-charts). -/
structure SNCParameterTower (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) where
  base_connected : SNCConnectedAffine (.of R)
  base_punctured_connected : SNCConnectedAffine (.of (Localization.Away (∏ i, t i)))
  level_connected : ∀ n : TameRootOrder p, SNCConnectedAffine (.of (sncRootLevel t n.val))
  full_connected : SNCConnectedAffine (.of (tameRootAlgebra p t))
  full_punctured_connected : SNCConnectedAffine (.of (Localization.Away
    (algebraMap R (tameRootAlgebra p t) (∏ i, t i))))
  transition : ∀ (n m : TameRootOrder p), n.val ∣ m.val →
    sncRootLevel t n.val →ₐ[R] sncRootLevel t m.val
  transition_root : ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val) (i : Fin r),
    transition n m h (sncRootCoordinate t n.val i) =
      sncRootCoordinate t m.val i ^ (m.val / n.val)
  transition_id : ∀ n, transition n n (dvd_refl n.val) = AlgHom.id R _
  transition_comp : ∀ (n m l : TameRootOrder p) (h : n.val ∣ m.val) (h' : m.val ∣ l.val),
    (transition m l h').comp (transition n m h) = transition n l (h.trans h')
  inclusion : ∀ n : TameRootOrder p, sncRootLevel t n.val →ₐ[R] tameRootAlgebra p t
  inclusion_root : ∀ (n : TameRootOrder p) (i : Fin r),
    inclusion n (sncRootCoordinate t n.val i) = sncFullRootCoordinate p t n i
  inclusion_compatible : ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
    (inclusion m).comp (transition n m h) = inclusion n
  full_colimit : ∀ (Q : Type u) [CommRing Q] [Algebra R Q]
      (f : ∀ n : TameRootOrder p, sncRootLevel t n.val →ₐ[R] Q),
    (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      (f m).comp (transition n m h) = f n) →
    ∃! g : tameRootAlgebra p t →ₐ[R] Q, ∀ n, g.comp (inclusion n) = f n
  puncturedLevel : ∀ n : TameRootOrder p,
    Localization.Away (∏ i, t i) →+* Localization.Away
      (algebraMap R (sncRootLevel t n.val) (∏ i, t i))
  puncturedLevel_base : ∀ (n : TameRootOrder p) (a : R),
    puncturedLevel n (algebraMap R _ a) =
      algebraMap (sncRootLevel t n.val) _ (algebraMap R _ a)
  puncturedLevel_cover : ∀ n, IsFinite (Spec.map (CommRingCat.ofHom (puncturedLevel n))) ∧
    Etale (Spec.map (CommRingCat.ofHom (puncturedLevel n))) ∧
    Surjective (Spec.map (CommRingCat.ofHom (puncturedLevel n)))
  puncturedTransition : ∀ (n m : TameRootOrder p), n.val ∣ m.val →
    Localization.Away (algebraMap R (sncRootLevel t n.val) (∏ i, t i)) →+*
      Localization.Away (algebraMap R (sncRootLevel t m.val) (∏ i, t i))
  puncturedTransition_spec : ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val)
      (a : sncRootLevel t n.val),
    puncturedTransition n m h (algebraMap (sncRootLevel t n.val) _ a) =
      algebraMap (sncRootLevel t m.val) _ (transition n m h a)
  puncturedTransition_cover : ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
    IsFinite (Spec.map (CommRingCat.ofHom (puncturedTransition n m h))) ∧
    Etale (Spec.map (CommRingCat.ofHom (puncturedTransition n m h))) ∧
    Surjective (Spec.map (CommRingCat.ofHom (puncturedTransition n m h)))
  puncturedFull : Localization.Away (∏ i, t i) →+*
    Localization.Away (algebraMap R (tameRootAlgebra p t) (∏ i, t i))
  puncturedFull_base : ∀ a : R,
    puncturedFull (algebraMap R _ a) =
      algebraMap (tameRootAlgebra p t) _ (algebraMap R _ a)
  puncturedFull_cover : Presieve.singleton (Spec.map (CommRingCat.ofHom puncturedFull)) ∈
    Scheme.proetalePrecoverage (Spec (.of (Localization.Away (∏ i, t i))))
  puncturedInclusion : ∀ n : TameRootOrder p,
    Localization.Away (algebraMap R (sncRootLevel t n.val) (∏ i, t i)) →+*
      Localization.Away (algebraMap R (tameRootAlgebra p t) (∏ i, t i))
  puncturedInclusion_spec : ∀ (n : TameRootOrder p) (a : sncRootLevel t n.val),
    puncturedInclusion n (algebraMap (sncRootLevel t n.val) _ a) =
      algebraMap (tameRootAlgebra p t) _ (inclusion n a)
  puncturedInclusion_compatible : ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
    (puncturedInclusion m).comp (puncturedTransition n m h) = puncturedInclusion n
  punctured_colimit : ∀ (Q : CommRingCat.{u})
      (f : ∀ n : TameRootOrder p,
        Localization.Away (algebraMap R (sncRootLevel t n.val) (∏ i, t i)) →+* Q),
    (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      (f m).comp (puncturedTransition n m h) = f n) →
    ∃! g : Localization.Away (algebraMap R (tameRootAlgebra p t) (∏ i, t i)) →+* Q,
      ∀ n, g.comp (puncturedInclusion n) = f n
  empty_level : r = 0 → ∀ n : TameRootOrder p,
    Function.Bijective (algebraMap R (sncRootLevel t n.val))
  empty_full : r = 0 → Function.Bijective (algebraMap R (tameRootAlgebra p t))

/-- The open obtained by deleting precisely the components not in I.
Source: ILO VIII 4.2.2(i) (blueprint: lem-sfb-snc-universal-residual-charts). -/
def sncStratumOpen {Y : Scheme.{u}} {a : ℕ} (C : Fin a → Y.IdealSheafData)
    (I : Finset (Fin a)) : Y.Opens :=
  (⨆ j : {j : Fin a // j ∉ I}, (C j.val).support).compl

/-- The reduced closed stratum inside that open, with empty intersections allowed.
Source: ILO VIII 4.2.2(i) (blueprint: lem-sfb-snc-universal-residual-charts). -/
def sncStratumIdeal {Y : Scheme.{u}} {a : ℕ} (C : Fin a → Y.IdealSheafData)
    (I : Finset (Fin a)) : (sncStratumOpen C I).toScheme.IdealSheafData :=
  ((⨆ j ∈ I, C j).comap (sncStratumOpen C I).ι).radical

/-- A chart carries its actual pair henselization and the pointed universal cover of it.
Reduction is identified over the residual base with its pointed universal cover.
Source: Stacks 0A02, 09ZS and Bhatt--Scholze 7.4.3
(blueprint: lem-sfb-snc-universal-residual-charts). -/
structure SNCResidualChart (p : ℕ) {Y : Scheme.{u}} {a : ℕ}
    (C : Fin a → Y.IdealSheafData) (I : Finset (Fin a)) where
  B : CommRingCat.{u}
  v : Spec B ⟶ (sncStratumOpen C I).toScheme
  etale : Etale v
  regular : IsRegularScheme (Spec B)
  noetherian : IsNoetherian (Spec B)
  separated : IsSeparated (terminal.from (Spec B))
  t : Fin (Fintype.card I) → B
  equations : ∀ i : Fin (Fintype.card I),
    (C ((Fintype.equivFin I).symm i).val).comap (v ≫ (sncStratumOpen C I).ι) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {(Scheme.ΓSpecIso B).inv (t i)})
  parameters : ∀ q : PrimeSpectrum B,
    ∃ (_hnoeth : IsNoetherianRing (Localization.AtPrime q.asIdeal))
      (s : List (Localization.AtPrime q.asIdeal)),
      IsLocalRing.IsRegularSystemOfParameters s ∧
      List.Nodup ((List.ofFn t).filter
        (fun z ↦ @decide (z ∈ q.asIdeal) (Classical.propDecidable _))) ∧
      List.Sublist
        (((List.ofFn t).filter (fun z ↦ @decide (z ∈ q.asIdeal) (Classical.propDecidable _))).map
          (algebraMap B (Localization.AtPrime q.asIdeal))) s
  residualIso : Spec (.of (B ⧸ Ideal.span (Set.range t))) ≅
    pullback (sncStratumIdeal C I).subschemeι v
  residualIso_base : residualIso.hom ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range t))))
  [residual_connected : ConnectedSpace (Spec (.of (B ⧸ Ideal.span (Set.range t))))]
  henselization : Cocone (ObjectProperty.ι (fun A : Under B ↦
    Etale (Spec.map A.hom) ∧ Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range t)).map A.hom.hom) A.hom.hom
        Ideal.le_comap_map)))
  henselization_isColimit : IsColimit henselization
  [henselization_connected : ConnectedSpace (Spec henselization.pt.right)]
  Ω : Type u
  [field : Field Ω]
  [closed : IsAlgClosed Ω]
  point : Spec (.of Ω) ⟶ Spec (.of (B ⧸ Ideal.span (Set.range t)))
  henselizationPoint : Spec (.of Ω) ⟶ Spec henselization.pt.right
  henselizationPoint_base : henselizationPoint ≫ Spec.map henselization.pt.hom =
    point ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range t))))
  H : CommRingCat.{u}
  b : B ⟶ H
  h : henselization.pt.right ⟶ H
  b_factor : henselization.pt.hom ≫ h = b
  universalIso : Spec H ≅ Scheme.UniversalCover.cover henselizationPoint
  universalIso_base : universalIso.hom ≫ Scheme.UniversalCover.proj henselizationPoint =
    Spec.map h
  residualCoverIso : Spec (.of (H ⧸ (Ideal.span (Set.range t)).map b.hom)) ≅
    Scheme.UniversalCover.cover point
  residualCoverIso_base : residualCoverIso.hom ≫ Scheme.UniversalCover.proj point =
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((Ideal.span (Set.range t)).map b.hom)
      b.hom Ideal.le_comap_map))
  indEtale : RingHom.IndEtaleAcrossUniverses b.hom
  henselian : HenselianRing H ((Ideal.span (Set.range t)).map b.hom)
  [lifted_residual_connected :
    ConnectedSpace (Spec (.of (H ⧸ (Ideal.span (Set.range t)).map b.hom)))]
  residual_cover : Presieve.singleton
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((Ideal.span (Set.range t)).map b.hom)
      b.hom Ideal.le_comap_map))) ∈
    Scheme.proetalePrecoverage (Spec (.of (B ⧸ Ideal.span (Set.range t))))
  zeta : TameRootOrder p → H
  zeta_primitive : ∀ n, IsPrimitiveRoot (zeta n) n.val
  zeta_compatible : ∀ (n m : TameRootOrder p), n.val ∣ m.val →
    zeta m ^ (m.val / n.val) = zeta n
  zeta_difference : ∀ (n : TameRootOrder p) (i j : Fin n.val), i ≠ j →
    IsUnit (zeta n ^ i.val - zeta n ^ j.val)
  tower : SNCParameterTower p (fun i ↦ b.hom (t i))
  residualMap : Spec (.of (H ⧸ (Ideal.span (Set.range t)).map b.hom)) ⟶
    (sncStratumIdeal C I).subscheme
  residualMap_base : residualMap ≫ (sncStratumIdeal C I).subschemeι =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((Ideal.span (Set.range t)).map b.hom))) ≫
      Spec.map b ≫ v
  empty_henselization : I = ∅ → Function.Bijective henselization.pt.hom.hom
  empty_residual : I = ∅ → Ideal.span (Set.range t) = ⊥

attribute [instance] SNCResidualChart.residual_connected SNCResidualChart.henselization_connected
  SNCResidualChart.field SNCResidualChart.closed SNCResidualChart.lifted_residual_connected

/-- Pullback on a common labelled chart, including the unit roots and the induced finite
and full root maps. Every ring map is specified on coefficients and root generators.
Source: ILO IX 2.1 and Stacks 0A02
(blueprint: lem-sfb-snc-universal-residual-charts). -/
structure SNCResidualRefinement {p : ℕ} {Y : Scheme.{u}} {a : ℕ}
    {C : Fin a → Y.IdealSheafData} {I : Finset (Fin a)}
    (Q R : SNCResidualChart p C I) where
  base : Q.B ⟶ R.B
  ambient : Spec.map base ≫ Q.v = R.v
  etale : Etale (Spec.map base)
  lift : Q.H ⟶ R.H
  lift_base : Q.b ≫ lift = base ≫ R.b
  henselizationMap : Q.henselization.pt.right ⟶ R.henselization.pt.right
  henselizationMap_base : Q.henselization.pt.hom ≫ henselizationMap =
    base ≫ R.henselization.pt.hom
  henselizationMap_lift : henselizationMap ≫ R.h = Q.h ≫ lift
  units : Fin (Fintype.card I) → R.Bˣ
  parameters : ∀ i, base.hom (Q.t i) = (units i : R.B) * R.t i
  unitRoots : Fin (Fintype.card I) → TameRootOrder p → R.Hˣ
  unitRoots_pow : ∀ i n, ((unitRoots i n : R.H) ^ n.val) = R.b.hom (units i)
  unitRoots_compatible : ∀ i (n m : TameRootOrder p), n.val ∣ m.val →
    (unitRoots i m : R.H) ^ (m.val / n.val) = unitRoots i n
  finiteMap : ∀ n : TameRootOrder p,
    sncRootLevel (fun i ↦ Q.b.hom (Q.t i)) n.val →+*
      sncRootLevel (fun i ↦ R.b.hom (R.t i)) n.val
  finiteMap_base : ∀ (n : TameRootOrder p) (h : Q.H),
    finiteMap n (algebraMap Q.H _ h) = algebraMap R.H _ (lift.hom h)
  finiteMap_root : ∀ (n : TameRootOrder p) i,
    finiteMap n (sncRootCoordinate (fun i ↦ Q.b.hom (Q.t i)) n.val i) =
      algebraMap R.H _ (unitRoots i n : R.H) *
        sncRootCoordinate (fun i ↦ R.b.hom (R.t i)) n.val i
  finiteMap_transition : ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
    (finiteMap m).comp (Q.tower.transition n m h).toRingHom =
      (R.tower.transition n m h).toRingHom.comp (finiteMap n)
  fullMap : tameRootAlgebra p (fun i ↦ Q.b.hom (Q.t i)) →+*
    tameRootAlgebra p (fun i ↦ R.b.hom (R.t i))
  fullMap_base : ∀ h : Q.H,
    fullMap (algebraMap Q.H _ h) = algebraMap R.H _ (lift.hom h)
  fullMap_root : ∀ (n : TameRootOrder p) i,
    fullMap (sncFullRootCoordinate p (fun i ↦ Q.b.hom (Q.t i)) n i) =
      algebraMap R.H _ (unitRoots i n : R.H) *
        sncFullRootCoordinate p (fun i ↦ R.b.hom (R.t i)) n i
  fullMap_inclusion : ∀ n : TameRootOrder p,
    fullMap.comp (Q.tower.inclusion n).toRingHom =
      (R.tower.inclusion n).toRingHom.comp (finiteMap n)
  residueMap : (Q.H ⧸ (Ideal.span (Set.range Q.t)).map Q.b.hom) →+*
    (R.H ⧸ (Ideal.span (Set.range R.t)).map R.b.hom)
  residueMap_spec : ∀ h : Q.H,
    residueMap (Ideal.Quotient.mk _ h) = Ideal.Quotient.mk _ (lift.hom h)
  puncturedBaseMap : Localization.Away (∏ i, Q.b.hom (Q.t i)) →+*
    Localization.Away (∏ i, R.b.hom (R.t i))
  puncturedBaseMap_spec : ∀ h : Q.H,
    puncturedBaseMap (algebraMap Q.H _ h) = algebraMap R.H _ (lift.hom h)
  puncturedFiniteMap : ∀ n : TameRootOrder p,
    Localization.Away (algebraMap Q.H
      (sncRootLevel (fun i ↦ Q.b.hom (Q.t i)) n.val) (∏ i, Q.b.hom (Q.t i))) →+*
    Localization.Away (algebraMap R.H
      (sncRootLevel (fun i ↦ R.b.hom (R.t i)) n.val) (∏ i, R.b.hom (R.t i)))
  puncturedFiniteMap_spec : ∀ (n : TameRootOrder p)
      (z : sncRootLevel (fun i ↦ Q.b.hom (Q.t i)) n.val),
    puncturedFiniteMap n (algebraMap _ _ z) = algebraMap _ _ (finiteMap n z)
  puncturedFullMap : Localization.Away
      (algebraMap Q.H (tameRootAlgebra p (fun i ↦ Q.b.hom (Q.t i)))
        (∏ i, Q.b.hom (Q.t i))) →+*
    Localization.Away
      (algebraMap R.H (tameRootAlgebra p (fun i ↦ R.b.hom (R.t i)))
        (∏ i, R.b.hom (R.t i)))
  puncturedFullMap_spec : ∀ z : tameRootAlgebra p (fun i ↦ Q.b.hom (Q.t i)),
    puncturedFullMap (algebraMap _ _ z) = algebraMap _ _ (fullMap z)

/-- The two actual covering families and their common pointed refinements. The empty
stratum has an empty index type. Refinements need not belong to the selected atlas.
Source: ILO VIII 4.2.2(i), IX 2.1 and Stacks 09ZS
(blueprint: lem-sfb-snc-universal-residual-charts). -/
structure SNCResidualAtlas (p : ℕ) {Y : Scheme.{u}} {a : ℕ}
    (C : Fin a → Y.IdealSheafData) (I : Finset (Fin a)) where
  indices : Type u
  chart : indices → SNCResidualChart p C I
  etale_cover : Presieve.ofArrows
    (fun j ↦ Spec (.of ((chart j).B ⧸ Ideal.span (Set.range (chart j).t))))
    (fun j ↦ (chart j).residualIso.hom ≫ pullback.fst _ _) ∈
    Scheme.etalePrecoverage (sncStratumIdeal C I).subscheme
  proetale_cover : Presieve.ofArrows
    (fun j ↦ Spec (.of ((chart j).H ⧸
      (Ideal.span (Set.range (chart j).t)).map (chart j).b.hom)))
    (fun j ↦ (chart j).residualMap) ∈
    Scheme.proetalePrecoverage (sncStratumIdeal C I).subscheme
  empty : IsEmpty (sncStratumIdeal C I).subscheme → IsEmpty indices
  refinements : ∀ (q : ℕ) (j : Fin q → indices)
      (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
      (s : Spec (.of Ω') ⟶ (sncStratumIdeal C I).subscheme)
      (sv : ∀ d : Fin q,
        Spec (.of Ω') ⟶ Spec (.of ((chart (j d)).B ⧸ Ideal.span (Set.range (chart (j d)).t)))),
    (∀ d, sv d ≫ (chart (j d)).residualIso.hom ≫ pullback.fst _ _ = s) →
    ∃ (R : SNCResidualChart p C I)
      (sr : Spec (.of Ω') ⟶ Spec (.of (R.B ⧸ Ideal.span (Set.range R.t))))
      (f : ∀ d : Fin q, SNCResidualRefinement (chart (j d)) R)
      (ur : Spec (.of Ω') ⟶ Spec R.H)
      (uv : ∀ d : Fin q, Spec (.of Ω') ⟶ Spec (chart (j d)).H),
      sr ≫ R.residualIso.hom ≫ pullback.fst _ _ = s ∧
      ur ≫ Spec.map R.b = sr ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span (Set.range R.t)))) ∧
      (∀ d, ur ≫ Spec.map (f d).lift = uv d) ∧
      (∀ d, uv d ≫ Spec.map (chart (j d)).b =
        sv d ≫ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span (Set.range (chart (j d)).t))))) ∧
      ∀ d, sr ≫ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span (Set.range R.t)))) ≫ Spec.map (f d).base =
        sv d ≫ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span (Set.range (chart (j d)).t))))

/-- Henselian SNC charts, their universal residual covers and prime-to-p root towers.
Source: Stacks 0A02, 0AGU, 0AGV, 09ZS; Bhatt--Scholze 7.4.3; ILO VIII 4.2.2(i),
IX Proposition 2.1 (blueprint: lem-sfb-snc-universal-residual-charts).

Proof plan (the DAG proof, including the strict-local clause stated separately below):
1. The field k is Noetherian, so Y and its open Y_I are Noetherian. Let P_a be the ideal of the
component D_a, an integral regular closed subscheme of the boundary definition. Fix y\in Y_I, put
J_y=\{i\in I:y\in D_i\} and \mathcal O=\mathcal O_{Y,y}, regular local of dimension d with maximal
ideal \mathfrak m. For i\in J_y, \mathcal O/P_{i,y}=\mathcal O_{D_i,y} is regular local of
dimension d-1 by the boundary dimension formula. The quotient-kernel theorem gives
P_{i,y}=(x_1,\ldots,x_c) for part of a regular system, and the regular-sequence theorem gives
dimension d-c, so c=1: any generator s_i of P_{i,y} is a nonzerodivisor of the domain \mathcal O.
The intersection ideal I'=\sum_{i\in J_y}(s_i) has \mathcal O/I'=\mathcal O_{C_{J_y},y} regular
local of dimension d-|J_y|, so likewise I'=(x_1,\ldots,x_{|J_y|}) for part of a regular system.
Each generating set expresses the other modulo \mathfrak mI'\subseteq\mathfrak m^2. So the classes
of the s_i span the same |J_y|-dimensional subspace of \mathfrak m/\mathfrak m^2 as the x_j; they
are distinct and independent, and by Nakayama they extend to a regular system of parameters. As
P_i has finite type, a generator of P_{i,y} generates P_i on an affine open W\ni y of Y_I missing
the D_i with i\notin J_y. For y\in S, J_y=I, so every D_i has a global equation t_i on W. At each
y'\in W the t_i vanishing at y' generate the P_{i,y'}, so the same argument shows they are part of
a regular system there. The ideal of S\cap W is J=(t_i), and C_I is regular, hence reduced, so
this is the reduced stratum. Open immersions are etale.
2. The regular Noetherian schemes Y_I and S have disjoint open-and-closed integral components.
Around each point s\in S, restrict to the ambient component through s and remove from an affine
chart all other components of its intersection with S. Take an affine open neighbourhood of s
inside that open. Its intersection S_V with S is a nonempty open of one integral component, hence
is integral and connected: any two nonempty basic opens in a domain meet. Retain the functions t_i
by restriction. Then V=\operatorname{Spec}B is regular, Noetherian, affine and separated, and
S_V=\operatorname{Spec}(B/J), J=(t_i), is nonempty connected regular. Since S is quasi-compact,
finitely many such charts suffice. Fix a geometric point s of each S_V.
3. Form the pair henselization A=B^h. Its construction is a small filtered colimit of etale
B-algebras, A/JA=B/J, and (A,JA) is henselian. As B is Noetherian, A is Noetherian. Reduction
identifies idempotents of A with those of A/JA: apply the henselian definition to the finite
algebra A itself. The latter ring is nonzero and has only idempotents 0,1, because S_V is nonempty
connected. Hence \operatorname{Spec}A is nonempty connected. Its affineness gives qcqs. The point
s maps to \operatorname{Spec}A by A\to A/JA\to\Omega.
4. Apply the pointed finite-etale limit-cover theorem to the nonempty connected qcqs scheme
X=\operatorname{Spec}A and s. Write its small cofinal pointed connected finite etale Galois system
as \operatorname{Spec}C_\lambda\to X and put H=\varinjlim_\lambda C_\lambda. For the henselian
pair (A,JA) apply finite-etale lifting with the proper morphism X\to\operatorname{Spec}A equal to
the identity. This identifies its finite-etale category, including morphisms and group actions,
with that of S_V. Idempotent lifting shows that connected objects correspond to connected objects.
Fibres at the same point s agree. Thus this equivalence identifies the entire pointed connected
Galois system with the one over S_V, not merely its objects. Quotienting the colimit by the
finitely generated ideal J gives H/JH=\varinjlim_\lambda C_\lambda/JC_\lambda: maps out of either
ring are exactly compatible maps killing the t_i. Therefore S_U=\operatorname{Spec}(H/JH) is
precisely the pointed universal finite-etale limit of S_V. It is nonempty connected and is a
pro-etale covering of S_V.
5. Each C_\lambda is finite etale over the Noetherian ring A, hence Noetherian. Each is integral
over A, and so is H: an element of H comes from a finite stage and satisfies there a monic
polynomial over A. Consequently (C_\lambda,JC_\lambda) and (H,JH) are henselian. Their marked
ideals are contained in their Jacobson radicals. The map B\to A is ind-etale by the henselization
construction, and A\to H is ind-etale by its finite-etale presentation. Stability under
composition makes B\to H ind-etale. Thus U\to V is affine ind-etale, and all the specified
henselian assertions hold.
6. The ring B is regular Noetherian and B\to A\to C_\lambda is ind-etale, by step 5 and since
every etale map is ind-etale; ind-etale maps are weakly etale, hence flat. Let \mathfrak p\subset
B be prime and F=\kappa(\mathfrak p)\otimes_BC_\lambda. By base change F is ind-etale, hence
weakly etale, over \kappa(\mathfrak p). The weak-etale field theorem makes F reduced and puts
every element of F in a finite etale, hence finite, \kappa(\mathfrak p)-subalgebra. If \mathfrak
Q\subset F is prime, a nonzero element of the domain F/\mathfrak Q satisfies a monic equation over
\kappa(\mathfrak p) with nonzero constant term, so it is invertible. Thus every prime is maximal,
each F_\mathfrak Q is a reduced zero-dimensional local ring, and its maximal ideal, the
nilradical, is zero. So F_\mathfrak Q is a field, and F (Noetherian, a localization of
C_\lambda/\mathfrak pC_\lambda) is regular. Flat ascent gives regularity of the Noetherian ring
C_\lambda. Now let \mathfrak m\subset C_\lambda be maximal. It contains JC_\lambda by the Jacobson
conclusion of step 5, so \mathfrak p=\mathfrak m\cap B is a point of S_V. By step 1 the t_i are
part of a regular system of parameters of B_\mathfrak p. Then they form a B_\mathfrak p-regular
sequence and B_\mathfrak p/(t_i) is regular local. The local map B_\mathfrak p\to
R:=(C_\lambda)_\mathfrak m is flat. Tensoring the injective multiplications by t_{j+1} on
B_\mathfrak p/(t_1,\ldots,t_j) with R keeps them injective, and R/(t_i)\neq0 since all
t_i\in\mathfrak m. So the t_i form an R-regular sequence. The closed fibre R/\mathfrak pR is a
localization of F at a prime, hence a field. The flat local map B_\mathfrak p/(t_i)\to R/(t_i) has
the same closed fibre, so the regular-fibre theorem makes R/(t_i) regular local. Each C_\lambda is
nonempty connected by construction, so regularity and the Noetherian normal decomposition show
that it is a domain.
7. Fix an algebraically closed geometric fibre field \Omega for the point s. For each prime q\ne
p, choose recursively primitive q^a-th roots in \Omega whose q-th powers are the roots already
chosen. Such a lift exists and is primitive: any q-th root of a primitive q^a-th root has order
q^{a+1}. For different primes take products and, by the Chinese remainder theorem for the
exponents, obtain primitive roots \bar\zeta_n for all (n,p)=1, with \bar\zeta_m^{m/n}=\bar\zeta_n
whenever n\mid m. Equivalently these choices specify a generator at every level of the prime-to-p
Tate module.
8. For (n,p)=1, the algebra A[z]/(z^n-1) is finite free by monic division and etale: its
derivative nz^{n-1} is a unit, so its monic presentation is the standard-etale presentation. The
universal-cover splitting over \operatorname{Spec}H, applied to this finite etale X-scheme, gives
a section for each fibre root. Choose the section indexed by \bar\zeta_n, and denote its value by
\zeta_n\in H. Naturality of that splitting for the power maps on root-of-unity schemes proves
\zeta_m^{m/n}=\zeta_n. The same splitting identifies the finite etale group scheme \mu_n over H
with the constant group on its geometric fibre. Distinct powers therefore remain distinct at every
prime of H, so \zeta_n^a-\zeta_n^b is in no maximal ideal and is a unit. In particular these are
primitive roots in the stated strong sense.
9. Write r=|I| and f=\prod_i t_i. For each finite stage C=C_\lambda and (n,p)=1 put
K_{\lambda,n}=C[x_1,\ldots,x_r]/(x_i^n-t_i). Repeated monic division gives the basis x^a with 0\le
a_i<n, so this is finite free of positive rank n^r over C and is Noetherian. Its reduction modulo
J is (C/JC)[x_i]/(x_i^n). The ideal generated by its x_i is nilpotent (its power r(n-1)+1 is
zero), and its further quotient is C/JC. Idempotents are unchanged by this nilpotent quotient.
Since (C,JC) is henselian, idempotents of the finite algebra K_{\lambda,n} are precisely those of
K_{\lambda,n}/JK_{\lambda,n}, hence those of C/JC. The residual finite cover is connected, so
K_{\lambda,n} has only 0,1 as idempotents. It is nonzero by its positive-rank basis, and therefore
its spectrum is nonempty connected.
10. Fix a maximal ideal \mathfrak q of K_{\lambda,n} and let \mathfrak m be its contraction to C.
Finiteness makes this contraction maximal. Since JC is in the Jacobson radical, JK_{\lambda,n}
lies in every maximal ideal as well. Each x_i^n=t_i then forces x_i\in\mathfrak q. Set
R=C_\mathfrak m and L=R[x_i]/(x_i^n-t_i). By step 6, t_1,\ldots,t_r form an R-regular sequence and
R/(t_i) is regular local. For 0\le j<r, substitution gives L/(x_1,\ldots,x_j)\cong
(R/(t_1,\ldots,t_j))[x_{j+1},\ldots,x_r]/(x_i^n-t_i)_{i>j}. The remaining monomials are a free
basis over R/(t_1,\ldots,t_j). Multiplication by t_{j+1} is injective on every coefficient, hence
on this free module. As x_{j+1}^n=t_{j+1}, multiplication by x_{j+1} is injective too. The final
quotient is R/(t_i)\ne0. This proves directly that the x_i form a regular sequence in L.
11. Localize the preceding regular sequence at the prime corresponding to \mathfrak q. Its entries
are in that prime, so it remains a regular sequence in K_{\lambda,n,\mathfrak q}. Quotienting by
the root coordinates gives the localization of R/(t_i) at its maximal ideal; this is R/(t_i)
itself. The identification follows from evaluation x_i\mapsto0 and quotient-localization
commutation. It is regular local. The regular-sequence lifting theorem therefore makes
K_{\lambda,n,\mathfrak q} regular local. Every other prime is contained in a maximal ideal, and
localizations of regular local rings are regular. Hence K_{\lambda,n} is regular. Its already
proved connectedness and nonemptiness, together with the regular Noetherian normal decomposition,
now make K_{\lambda,n} a domain. This argument uses no Noetherianity of H.
12. Polynomial presentations commute with the filtered colimit here: assigning the finitely many
roots satisfying x_i^n=t_i and a compatible map on all C_\lambda is exactly a map from either H_n
or \varinjlim_\lambda K_{\lambda,n}. Thus H_n=\varinjlim_\lambda K_{\lambda,n}. A filtered colimit
of nonzero domains along unital maps is a nonzero domain: if a product is zero, represent its two
factors at a common stage and the zero equality at a later stage; one factor is zero there and
therefore in the colimit. Also 1=0 in the colimit would hold at a stage, which is impossible. This
proves that H, every H_n, and H_\infty are nonzero domains. For each i, the image of t_i is
nonzero at every C_\lambda and K_{\lambda,n}: at a maximal ideal it is a nonzerodivisor of the
nonzero local ring of C_\lambda (step 6), and the monic basis embeds C_\lambda into K_{\lambda,n}.
The elementwise colimit criterion therefore keeps every t_i, and f, nonzero in these colimits.
13. In a nonzero domain the zero ideal is prime and belongs to every nonempty basic open. Thus its
spectrum is nonempty irreducible, hence connected. Localizing at a nonzero element is again a
nonzero domain: a/f^b=0 means f^ca=0, hence a=0. Apply this to H,H_n,H_\infty and f to get the
asserted nonempty connected total and punctured schemes. All are affine (the punctures are
principal localizations), so all are qcqs. This also supplies nonemptiness of U^\circ, which does
not follow merely from nonemptiness of the residual stratum.
14. After inverting f, each t_i and each root x_i is a unit. The monic polynomial X^n-t_i has unit
derivative nX^{n-1} in its root quotient. The monic standard-etale criterion, iterated over i,
shows that H_n[1/f] is etale over H[1/f]; composition of etale maps is etale. Its monomial basis
has positive rank n^r, so every maximal-ideal fibre is a nonzero vector space and the ring map is
flat. The flat proper-maximal-ideal criterion makes the map faithfully flat, hence surjective on
spectra. It is finite by the same finite basis. Thus every indicated finite punctured level is
finite etale and surjective.
15. For n\mid m, write d=m/n. The transition sends x_{i,n} to x_{i,m}^d. Elimination of the old
root variables gives H_m\cong H_n[y_i]/(y_i^d-x_{i,n})_{i\in I},\qquad y_i\longmapsto x_{i,m}. The
inverse sends x_{i,m} to y_i; its defining relation is y_i^m=(y_i^d)^n=t_i. Repeated monic
division gives a positive-rank d^r basis over H_n. On the puncture y_i and d are units, so the
same derivative calculation proves etaleness of the transition. The same finite-free argument
proves surjectivity. These explicit formulas also verify the identity and composite transition
laws, since (x^{m/n})^{n/a}=x^{m/a}.
16. The affine inverse-limit theorem identifies the inverse limit of the punctured finite levels
with \operatorname{Spec}H_\infty[1/f]: localization commutes with this colimit because compatible
maps on either ring are exactly compatible stage maps in which f is a unit. The limit ring is
ind-etale over H[1/f], hence weakly etale. The punctured levels are faithfully flat over H[1/f],
so their directed colimit is faithfully flat and surjective on spectra. The map is affine, and
therefore its single affine source covers the affine target in the fpqc covering condition of the
pro-etale site. This proves that T^\circ\to U^\circ is a pro-etale covering, not just a weakly
etale map.
17. For the separate strict-local assertion let R be a strictly henselian regular Noetherian local
ring of characteristic p, with maximal ideal \mathfrak m and residue field \kappa. Let
t_1,\ldots,t_r be part of a regular system of parameters, f=\prod_it_i, and (n,p)=1. Put
K=R[x_i]/(x_i^n-t_i). Repeated monic division makes K finite free over R on the monomials x^a,
0\le a_i<n, so K is nonzero, Noetherian, integral over R, and R\to K is injective. Since R is
henselian, idempotents of the finite algebra K are those of K/\mathfrak mK=\kappa[x_i]/(x_i^n).
Its ideal (x_i) is nilpotent with quotient the field \kappa, so K has only 0,1 as idempotents and
\operatorname{Spec}K is nonempty connected. Every maximal ideal \mathfrak q of K contracts to
\mathfrak m by integrality and contains every x_i, since x_i^n=t_i\in\mathfrak m. The
regular-sequence theorem makes the t_i an R-regular sequence with R/(t_i) regular local. Steps 10
and 11 apply verbatim with C_\mathfrak m replaced by R and L=K. The x_i form a regular sequence in
K_\mathfrak q, and K_\mathfrak q/(x_i)=R/(t_i) is regular local. The lifting theorem makes
K_\mathfrak q regular local, so K is regular and, being connected, a domain. Each t_i is a
nonzerodivisor of the nonzero ring R, so f\neq0 in R\subseteq K. The finite punctured ring K[1/f]
is therefore a nonzero domain. The full root ring \varinjlim_nK_n is a nonzero domain by the
filtered-colimit argument of step 12, and f stays nonzero at every stage by freeness. Its puncture
is consequently a nonzero domain too. Spectra of all these domains are nonempty connected. For
r=0, K=R is a regular local ring, hence a domain.
18. For the finite chart family chosen in step 2, each S_U\to S_V is the pro-etale covering of
step 4. The finite open family S_V\to S covers S and each affine S_U surjects onto S_V. The
composites are weakly etale by stability under composition. They satisfy the covering condition:
over an affine open in S, its inverse images in the finitely many S_V are quasi-compact opens of
Noetherian affine schemes, so are finite unions of principal opens; pull these back to the
corresponding S_U to obtain finitely many affine opens covering that affine target. Thus the
composites form a pro-etale covering of S. For an empty stratum take the empty family; every
requested assertion indexed by a chart is then vacuous.
19. To compare two charts above the same geometric stratum point, take their fibre product over
Y_I with the induced point, then an affine neighbourhood of that point. It is etale over either
chart by base change, and its reduced stratum is regular. As in step 2, shrink to a nonempty open
of its component through the point. It is a chart of the same type. A ring map of these charts
preserves the stratum ideals and therefore induces a map on pair henselizations by their universal
property. Apply the naturality for pointed scheme morphisms of the universal finite-etale cover to
obtain compatible maps on H and on H/JH. At finite levels the maps are the maps of pointed finite
covers supplied by the equivalence of finite-etale categories. Uniqueness there makes all the
diagrams commute before taking colimits. Repeating the fibre-product construction gives common
refinements for any finite collection of pointed charts.
20. On such an affine overlap, two equations of the same labelled Cartier ideal differ by a unit:
after shrinking, write t'_i=a_i t_i with a_i a unit. For each (n,p)=1 the algebra A[z]/(z^n-a_i)
is finite etale by monic division and the unit derivative criterion. Choose compatible roots of
the fibre value of a_i in \Omega (recursively for prime powers and then for divisibility). The
pointed universal-cover splitting gives compatible roots b_{i,n} in H with b_{i,n}^n=a_i and
b_{i,m}^{m/n}=b_{i,n}. The map between root presentations sends x'_{i,n}\mapsto b_{i,n}x_{i,n};
its n-th power is a_it_i=t'_i. Its compatibility with transitions is the equality
(b_{i,m}x_{i,m})^{m/n}=b_{i,n}x_{i,n}. On a common refinement of several charts, choose roots for
the ratio of each equation to one reference equation, and define the roots of a pairwise ratio by
dividing those choices. Their products then give exactly the roots for composed ratios. Naturality
of the normalized splitting preserves these prescribed fibre values, so the comparison maps
satisfy the cocycle identities. Thus the displayed rings, punctures, and chosen root systems admit
the asserted compatible pullbacks on common pointed refinements.
21. When I=\varnothing, J=0 and f=1. The pair (B,0) is henselian directly from its idempotent
definition, so the pair-henselization universal property identifies A=B. There are no root
variables or relations, and every H_n and the colimit H_\infty is H. Here S_V=V and U\to V is
exactly the pointed universal finite-etale limit cover constructed in step 4. All transition and
comparison maps reduce to those of that cover. The case n=1 for arbitrary I similarly gives H_1=H
by substituting x_i=t_i.
-/
theorem nonempty_sncResidualAtlas
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType y] [QuasiCompact y] [IsSeparated y]
    (hY : IsRegularScheme Y) (D : Y.IdealSheafData)
    (hD : IsStrictNormalCrossingsBoundary D)
    (a : ℕ) (C : Fin a → Y.IdealSheafData)
    (hC : Function.Injective (fun i ↦ (C i).support) ∧
      (∀ i, IsIntegral (C i).subscheme ∧ IsRegularScheme (C i).subscheme) ∧
      D.support = ⨆ i, (C i).support ∧
      ∀ s : Finset (Fin a), ∀ z : (⨆ i ∈ s, C i).subscheme,
        IsRegularScheme (⨆ i ∈ s, C i).subscheme ∧
        ringKrullDim (Y.presheaf.stalk ((⨆ i ∈ s, C i).subschemeι z)) =
          ringKrullDim ((⨆ i ∈ s, C i).subscheme.presheaf.stalk z) + (s.card : ℕ))
    (I : Finset (Fin a)) : Nonempty (SNCResidualAtlas p C I) := by
  sorry

/-- The strict-local assertion, also for the empty parameter tuple.
Source: ILO IX Proposition 2.1
(blueprint: lem-sfb-snc-universal-residual-charts).

Proof: use step 17 of the main proof. Monic division gives a positive-rank free basis.
Henselianness and the nilpotent residual root ideal give connectedness. At maximal
ideals the root coordinates form a regular sequence with regular quotient R/(t).
The regular-sequence lifting theorem gives regularity; connected regular Noetherian
rings are domains. The parameter product is nonzero by regularity and freeness.
The elementwise filtered-colimit criterion preserves nonzero domains and that product.
Their localizations are nonzero domains, so every displayed spectrum is nonempty
connected. When the tuple is empty the product is 1 and all root rings identify with R. -/
theorem snc_strictLocal_roots_connected
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p]
    [IsStrictlyHenselianLocalRing R] [IsRegularLocalRing R]
    (r : ℕ) (t : Fin r → R)
    (ht : ∃ rest : List R, IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ rest)) :
    (∀ n : TameRootOrder p,
      ConnectedSpace (Spec (.of (sncRootLevel t n.val))) ∧
      ConnectedSpace (Spec (.of (Localization.Away
        (algebraMap R (sncRootLevel t n.val) (∏ i, t i)))))) ∧
    ConnectedSpace (Spec (.of (tameRootAlgebra p t))) ∧
    ConnectedSpace (Spec (.of (Localization.Away
      (algebraMap R (tameRootAlgebra p t) (∏ i, t i))))) := by
  sorry

end AlgebraicGeometry.ProEtale
