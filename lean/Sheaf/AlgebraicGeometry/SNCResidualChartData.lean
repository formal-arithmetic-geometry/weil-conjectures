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


end AlgebraicGeometry.ProEtale
