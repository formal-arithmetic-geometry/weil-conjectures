/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.AlgebraicGeometry.VeryTameFSLogAction
public import Sheaf.AlgebraicGeometry.LogMorphismOperations
public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.NormalCrossingsBranchCount
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Compactification.StrictTransform
public import Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure

/-! # Data for the four stages of the absolute Gabber modification

Source: ILO, Travaux de Gabber, VIII 4.1.1--4.1.9, 5.3.8--5.5.5 and 5.6.1
(blueprint: def-per-gabber-modification-data).

These are predicates and diagrams, not choices of modifications from existence statements.
The finite towers remember their centers. Empty towers and disconnected local charts are allowed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
namespace GabberModification

/-- The free geometric-point condition on an invariant open. Source: ILO VIII 1.1
(blueprint: def-per-gabber-modification-data). -/
def FreeOpen {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    (a : FSLogGroupAction G X) (U : X.scheme.Opens) : Prop :=
  (∀ (g : G) (x : X.scheme), (a.baseAction g).hom x ∈ U ↔ x ∈ U) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
      (g : G), t default ∈ U → t ≫ (a.baseAction g).hom = t → g = 1

/-- The largest invariant free open, formed as the union of all invariant free opens.
Source: ILO VIII 1.1 (blueprint: def-per-gabber-modification-data). -/
def freeLocus {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    (a : FSLogGroupAction G X) : X.scheme.Opens :=
  ⨆ U : {U : X.scheme.Opens // FreeOpen a U}, U.1

/-- Quasi-excellence is tested on every affine open. Source: ILO VIII 1.1
(blueprint: def-per-gabber-modification-data). -/
def QuasiExcellent (X : Scheme.{u}) : Prop :=
  ∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U.1)

/-- The hypotheses on the original triple. Source: ILO VIII 1.1
(blueprint: def-per-gabber-modification-data). -/
def Input {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    (a : FSLogGroupAction G X) : Prop :=
  IsIntegral X.scheme ∧ IsNoetherian X.scheme ∧ QuasiExcellent X.scheme ∧
    X.scheme.IsSeparated ∧ X.IsLogRegular ∧ a.IsTame ∧ a.IsGenericallyFree

/-- Distinct translates of each irreducible boundary component are disjoint.
Source: ILO VIII 4.1.5 (blueprint: def-per-gabber-modification-data). -/
def GStrict {G : Type v} [Group G] {X : Scheme.{u}} (a : G →* Aut X)
    (B : X.IdealSheafData) : Prop :=
  ∀ C ∈ irreducibleComponents B.subscheme, ∀ g : G,
    (a g).hom '' (B.subschemeι '' C) = B.subschemeι '' C ∨
      Disjoint ((a g).hom '' (B.subschemeι '' C)) (B.subschemeι '' C)

/-- All geometric inertia groups are abelian. Source: ILO VIII 4.1.9
(blueprint: def-per-gabber-modification-data). -/
def AbelianInertia {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    (a : FSLogGroupAction G X) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme),
    ∀ g h : G, t ≫ (a.baseAction g).hom = t → t ≫ (a.baseAction h).hom = t →
      g * h = h * g

/-- The unrestricted permissible-center condition: the center need not lie in the old
boundary. Both ideals use one full regular parameter system. Source: ILO VIII 4.1.2;
X 1.4 (blueprint: def-per-gabber-modification-data). -/
def Permissible {X : Scheme.{u}} (B I : X.IdealSheafData) : Prop :=
  IsRegularScheme I.subscheme ∧ ∀ x : X, x ∈ I.support →
    ∃ (W : Scheme.{u}) (e : W ⟶ X), Etale e ∧ ∃ w : W, e w = x ∧
      ∃ (U : W.affineOpens) (hw : w ∈ U.1) (d r m : ℕ)
        (hn : IsNoetherianRing (W.presheaf.stalk w))
        (t : Fin d → W.presheaf.stalk w) (f : Fin r → Γ(W, U.1))
        (g : Fin m → Γ(W, U.1)) (s : Fin r → Fin d) (q : Fin m → Fin d),
        Function.Injective s ∧ Function.Injective q ∧ 0 < m ∧
          @IsLocalRing.IsRegularSystemOfParameters (W.presheaf.stalk w)
            inferInstance inferInstance hn (List.ofFn t) ∧
          (B.comap e).ideal U = Ideal.span {∏ i, f i} ∧
          (I.comap e).ideal U = Ideal.span (Set.range g) ∧
          (∀ i, (W.presheaf.germ U.1 w hw).hom (f i) = t (s i)) ∧
          ∀ j, (W.presheaf.germ U.1 w hw).hom (g j) = t (q j)

/-- A fixed closed subscheme, characterized by its functor of points, including
nonreduced tests. Source: ILO VIII 4.1.9 (blueprint: def-per-gabber-modification-data). -/
def FixedIdeal {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    (a : FSLogGroupAction G X) (H : Subgroup G) (I : X.scheme.IdealSheafData) : Prop :=
  ∀ (T : Scheme.{u}) (f : T ⟶ X.scheme),
    I.comap f = ⊥ ↔ ∀ h : H, f ≫ (a.baseAction h).hom = f

/-- A finite equivariant normalized blowup tower over its specified log base.
The projections obey the log composition equations. Source: ILO VIII 5.6.1(i)
(blueprint: def-per-gabber-modification-data). -/
structure Tower (G : Type v) [Group G] (X : FineSaturatedLogScheme.{u})
    (a : FSLogGroupAction G X) where
  length : ℕ
  level : Fin (length + 1) → FineSaturatedLogScheme.{u}
  initial : level 0 = X
  action : ∀ i, FSLogGroupAction G (level i)
  initialAction : HEq (action 0) a
  center : ∀ i : Fin length, (level i.castSucc).scheme.IdealSheafData
  arrow : ∀ i : Fin length, EtaleLogHom (level i.succ) (level i.castSucc)
  normalized : ∀ i, Monoscheme.IsNormalizedBlowup (arrow i).base (center i)
  denseCenterComplement : ∀ i, Dense ((center i).support.compl : Set (level i.castSucc).scheme)
  invariantCenter : ∀ (i : Fin length) (g : G),
    (center i).comap ((action i.castSucc).baseAction g).hom = center i
  equivariant : ∀ i, (action i.succ).IsEquivariant (action i.castSucc) (arrow i)
  projection : ∀ i, EtaleLogHom (level i) X
  initialProjection : HEq (projection 0) (EtaleLogHom.id X)
  composition : ∀ i, (arrow i).CompEq (projection i.castSucc) (projection i.succ)

/-- The final source of a tower. Source: ILO VIII 5.6.1
(blueprint: def-per-gabber-modification-data). -/
def Tower.source {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    {a : FSLogGroupAction G X} (T : Tower G X a) : FineSaturatedLogScheme.{u} :=
  T.level (Fin.last T.length)

/-- The total log morphism of a tower. Source: ILO VIII 5.6.1
(blueprint: def-per-gabber-modification-data). -/
def Tower.map {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    {a : FSLogGroupAction G X} (T : Tower G X a) : EtaleLogHom T.source X :=
  T.projection (Fin.last T.length)

/-- Boundary ideals at every level, with precisely the log triviality complement.
Source: ILO VIII 4.1.1--4.1.9 (blueprint: def-per-gabber-modification-data). -/
def Tower.Boundaries {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    {a : FSLogGroupAction G X} (T : Tower G X a)
    (B : ∀ i, (T.level i).scheme.IdealSheafData) : Prop :=
  ∀ i, (B i).radical = B i ∧
    ((B i).support : Set (T.level i).scheme) = (T.level i).logStructure.trivialityLocusᶜ

/-- The scheme-theoretic strict transform along a specified modification, with its
preserved open given by the actual center. Source: ILO VIII 4.1.3
(blueprint: def-per-gabber-modification-data). -/
def transform {Y X : Scheme.{u}} (f : Y ⟶ X) (I D : X.IdealSheafData) :
    Y.IdealSheafData :=
  (strictTransformMap D.subschemeι f I.support.compl).ker

/-- An ordinary blowup step with its given center and given map.
Source: ILO VIII 4.1.2 (blueprint: def-per-gabber-modification-data). -/
def OrdinaryStep {Y X : Scheme.{u}} (f : Y ⟶ X) (I : X.IdealSheafData) : Prop :=
  ∃ e : Y ≅ I.blowup, e.hom ≫ I.blowupMap = f

/-- One full minimal-fixed-family round. All nontrivial subgroup fixed schemes are
initialized at the start, then strictly transformed. Each center is the union of ALL
nonempty minimal members; the final family is empty. Source: ILO VIII 4.1.9, 4.2.11
(blueprint: def-per-gabber-modification-data). -/
structure FixedRound {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    {a : FSLogGroupAction G X} (T : Tower G X a)
    (first last : Fin (T.length + 1)) where
  order : first ≤ last
  family : ∀ i, Subgroup G → (T.level i).scheme.IdealSheafData
  initial : ∀ H : Subgroup G, H ≠ ⊥ → FixedIdeal (T.action first) H (family first H)
  centers : ∀ i : Fin T.length, first.val ≤ i.val → i.val < last.val →
    T.center i = ⨅ H : {H : Subgroup G // H ≠ ⊥ ∧
      (family i.castSucc H).support ≠ ⊥ ∧
      ∀ K : Subgroup G, K ≠ ⊥ → (family i.castSucc K).support ≠ ⊥ →
        (family i.castSucc K).support ≤ (family i.castSucc H).support →
        (family i.castSucc K).support = (family i.castSucc H).support},
      family i.castSucc H.1
  transforms : ∀ (i : Fin T.length) (H : Subgroup G),
    first.val ≤ i.val → i.val < last.val →
      family i.succ H = transform (T.arrow i).base (T.center i) (family i.castSucc H)
  finished : ∀ H : Subgroup G, H ≠ ⊥ → (family last H).support = ⊥

/-- Strict inertia preservation for a possibly changing group. Surjectivity and
injectivity are stated on the actual geometric stabilizers. Source: ILO VIII 5.3.6
(blueprint: def-per-gabber-modification-data). -/
def Inert {H G : Type v} [Group H] [Group G] {Y X : FineSaturatedLogScheme.{u}}
    (b : FSLogGroupAction H Y) (a : FSLogGroupAction G X) (rho : H →* G)
    (f : EtaleLogHom Y X) : Prop :=
  (∀ h : H, ∃ c : EtaleLogHom Y X,
    (b.logMap h).CompEq f c ∧ f.CompEq (a.logMap (rho h)) c) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y.scheme),
      (∀ g : G, (t ≫ f.base) ≫ (a.baseAction g).hom = t ≫ f.base →
        ∃ h : H, t ≫ (b.baseAction h).hom = t ∧ rho h = g) ∧
      ∀ h k : H, t ≫ (b.baseAction h).hom = t → t ≫ (b.baseAction k).hom = t →
        rho h = rho k → h = k

/-- Relative finite-projective-space quasi-projectivity over an arbitrary base.
Source: the finite-projective-space refinement of ILO VIII 5.6.1
(blueprint: def-per-gabber-modification-data). -/
def QuasiProjective {Y B : Scheme.{u}} (p : Y ⟶ B) : Prop :=
  ∃ (n : ℕ) (i : Y ⟶ ℙ(ULift.{u} (Fin (n + 1)); B)),
    IsImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (n + 1)); B) ↘ B = p

/-- The domain of the fourth stage, also allowing disconnected strict inert charts.
Source: ILO VIII 5.1, 5.3.7 (blueprint: def-per-gabber-modification-data). -/
def AbelianInput {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    (a : FSLogGroupAction G X) (B : X.scheme.IdealSheafData) : Prop :=
  IsNoetherian X.scheme ∧ QuasiExcellent X.scheme ∧ X.scheme.IsSeparated ∧
    IsRegularScheme X.scheme ∧ X.IsLogRegular ∧ a.IsTame ∧ AbelianInertia a ∧
    IsStrictNormalCrossingsBoundary B ∧ GStrict a.baseAction B ∧
    (B.support : Set X.scheme) = X.logStructure.trivialityLocusᶜ ∧
    FreeOpen a B.support.compl

/-- An auxiliary very tame enlarged strict normal crossings boundary on the same scheme,
identified by an actual isomorphism on underlying schemes. The original log structure is
retained by `forget`. Source: ILO VIII 5.3.5--5.3.8
(blueprint: def-per-gabber-modification-data). -/
structure Rigidification {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    (a : FSLogGroupAction G X) where
  enlarged : FineSaturatedLogScheme.{u}
  action : FSLogGroupAction G enlarged
  forget : EtaleLogHom enlarged X
  sameScheme : IsIso forget.base
  equivariant : action.IsEquivariant a forget
  boundary : enlarged.scheme.IdealSheafData
  snc : IsStrictNormalCrossingsBoundary boundary
  support : (boundary.support : Set enlarged.scheme) = enlarged.logStructure.trivialityLocusᶜ
  contains : enlarged.logStructure.trivialityLocus ⊆
    forget.base ⁻¹' X.logStructure.trivialityLocus
  veryTame : action.IsVeryTame
  logRegular : enlarged.IsLogRegular

/-- The log regular inputs of the chosen saturated resolution rule. Source: ILO VIII 3.3.15
(blueprint: def-per-gabber-modification-data). -/
def ResolutionInput (X : FineSaturatedLogScheme.{u}) : Prop :=
  IsLogBlowupInput X ∧ X.IsLogRegular

/-- A quotient presentation for an auxiliary rigidification, retaining the actual invariant
log quotient and its input to the common resolution rule. Source: ILO VIII 5.3.8
(blueprint: def-per-gabber-modification-data). -/
structure RigidifiedQuotient {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    {a : FSLogGroupAction G X} (R : Rigidification a) where
  quotient : FineSaturatedLogScheme.{u}
  map : EtaleLogHom R.enlarged quotient
  invariantQuotient : R.action.IsQuotient map
  finite : IsFinite map.base
  surjective : Surjective map.base
  input : ResolutionInput quotient

/-- Ordered contraction of a scheme pullback, with all centers and canonical projections.
Exactly unit centers are deleted, including consecutive ones; proper principal centers stay.
Source: ILO VIII 5.4.4--5.5.5 (blueprint: def-per-gabber-modification-data). -/
structure Comparison {G H : Type v} [Group G] [Group H]
    {X Y : FineSaturatedLogScheme.{u}} {a : FSLogGroupAction G X}
    {b : FSLogGroupAction H Y} (f : EtaleLogHom Y X)
    (T : Tower G X a) (S : Tower H Y b) where
  count : Fin (T.length + 1) →o Fin (S.length + 1)
  first : count 0 = 0
  last : count (Fin.last T.length) = Fin.last S.length
  retained : Fin S.length ↪o Fin T.length
  before : ∀ k, count (retained k).castSucc = k.castSucc
  after : ∀ k, count (retained k).succ = k.succ
  deleted : ∀ i, i ∉ Set.range retained → count i.succ = count i.castSucc
  lift : ∀ i, EtaleLogHom (S.level (count i)) (T.level i)
  initial : HEq (lift 0) f
  step : ∀ i : Fin T.length,
    EtaleLogHom (S.level (count i.succ)) (S.level (count i.castSucc))
  cartesian : ∀ i, IsPullback (step i).base (lift i.succ).base
    (lift i.castSucc).base (T.arrow i).base
  logSquare : ∀ i, (step i).Square (lift i.castSucc) (lift i.succ) (T.arrow i)
  keptStep : ∀ k, HEq (step (retained k)) (S.arrow k)
  keptCenter : ∀ k, HEq ((T.center (retained k)).comap (lift (retained k).castSucc).base)
    (S.center k)
  unitCenter : ∀ i, i ∉ Set.range retained ↔
    (T.center i).comap (lift i.castSucc).base = ⊤

/-- The actual fs pullback of a resolved enlarged quotient, identified with the original
boundary's normalized tower at every scheme level. Centers are the ring ideals generated
by the pulled-back log ideals, tested in geometric strict local rings. Discarding the
auxiliary boundary changes the log structures, not these schemes, arrows or centers.
Source: ILO VIII 5.3.8--5.3.11 (blueprint: def-per-gabber-modification-data). -/
structure RigidifiedConstruction
    (P : StrictEtaleLogBlowupProcedure ResolutionInput.{u})
    {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    {a : FSLogGroupAction G X} (T : Tower G X a) (R : Rigidification a)
    (Q : RigidifiedQuotient R) where
  index : Fin (T.length + 1) ≃o Fin ((P.tower Q.quotient Q.input).tower.length + 1)
  stage : Fin T.length ≃o Fin (P.tower Q.quotient Q.input).tower.length
  first : index 0 = 0
  before : ∀ i, index i.castSucc = (stage i).castSucc
  after : ∀ i, index i.succ = (stage i).succ
  enlargedLevel : Fin (T.length + 1) → FineSaturatedLogScheme.{u}
  initial : enlargedLevel 0 = R.enlarged
  schemeIso : ∀ i, (enlargedLevel i).scheme ≅ (T.level i).scheme
  initialIso : HEq ((schemeIso 0).hom ≫ (T.projection 0).base) R.forget.base
  arrow : ∀ i : Fin T.length, EtaleLogHom (enlargedLevel i.succ) (enlargedLevel i.castSucc)
  schemeArrow : ∀ i, (arrow i).base ≫ (schemeIso i.castSucc).hom =
    (schemeIso i.succ).hom ≫ (T.arrow i).base
  quotientMap : ∀ i, EtaleLogHom (enlargedLevel i)
    ((P.tower Q.quotient Q.input).tower.level (index i))
  initialMap : HEq (quotientMap 0) Q.map
  quotientArrow : ∀ i : Fin T.length,
    EtaleLogHom ((P.tower Q.quotient Q.input).tower.level (index i.succ))
      ((P.tower Q.quotient Q.input).tower.level (index i.castSucc))
  quotientStep : ∀ i, HEq (quotientArrow i) ((P.tower Q.quotient Q.input).tower.arrow (stage i))
  cartesian : ∀ i, (arrow i).IsFSPullback (quotientMap i.castSucc)
    (quotientMap i.succ) (quotientArrow i)
  logCenter : ∀ i : Fin T.length, (enlargedLevel i.castSucc).logStructure.IdealFamily
  pulledCenter : ∀ i, ∃ J :
      ((P.tower Q.quotient Q.input).tower.level (index i.castSucc)).logStructure.IdealFamily,
    HEq J ((P.tower Q.quotient Q.input).tower.center (stage i)) ∧
      logCenter i = (quotientMap i.castSucc).pullbackIdeal J
  ringCenter : ∀ (i : Fin T.length) (V : (enlargedLevel i.castSucc).scheme.affineOpens)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ (enlargedLevel i.castSucc).scheme)
    (w : (Scheme.pointSmallEtale t).fiber.obj (Scheme.Etale.mk V.1.ι)),
    (((T.center i).comap (schemeIso i.castSucc).hom).ideal V).map
      ((strictLocalGerm _ t (Scheme.Etale.mk V.1.ι) w).hom.comp V.1.topIso.inv.hom) =
        Ideal.span ((enlargedLevel i.castSucc).logStructure.toEtalePrelogStructure.stalkAlpha t ''
          (enlargedLevel i.castSucc).logStructure.idealStalk (logCenter i) t)

-- The two independent site/group universes enter this structure through their maximum.
set_option linter.checkUnivs false in
/-- A common fourth-stage rule, with its choice-free local construction and comparisons.
The rule applies to all regular abelian-inertia pairs, including disconnected chart covers.
Source: ILO VIII 5.3.8--5.5.5 (blueprint: def-per-gabber-modification-data). -/
structure FourthProcedure where
  resolution : StrictEtaleLogBlowupProcedure ResolutionInput.{u}
  resolves : ∀ (X : FineSaturatedLogScheme.{u}) (h : ResolutionInput X),
    IsRegularScheme ((resolution.tower X h).tower.level
      (Fin.last (resolution.tower X h).tower.length)).scheme
  tower : ∀ (G : Type v) [Group G] [Finite G] (X : FineSaturatedLogScheme.{u})
    (a : FSLogGroupAction G X) (B : X.scheme.IdealSheafData),
    AbelianInput a B → Tower G X a
  result : ∀ (G : Type v) [Group G] [Finite G] (X : FineSaturatedLogScheme.{u})
    (a : FSLogGroupAction G X) (B : X.scheme.IdealSheafData) (h : AbelianInput a B),
    (tower G X a B h).source.IsLogRegular ∧
      ((tower G X a B h).action (Fin.last (tower G X a B h).length)).IsVeryTame ∧
      ((tower G X a B h).source.logStructure.trivialityLocus) =
        (tower G X a B h).map.base ⁻¹' X.logStructure.trivialityLocus
  localConstruction : ∀ (G : Type v) [Group G] [Finite G]
    (X : FineSaturatedLogScheme.{u}) (a : FSLogGroupAction G X)
    (B : X.scheme.IdealSheafData) (h : AbelianInput a B),
    (∀ x : X.scheme, ∃ U : X.scheme.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∀ (g : G) (z : X.scheme), (a.baseAction g).hom z ∈ U ↔ z ∈ U) →
    ∀ (R : Rigidification a) (Q : RigidifiedQuotient R),
      Nonempty (RigidifiedConstruction resolution (tower G X a B h) R Q)
  localCover : ∀ (G : Type v) [Group G] [Finite G]
    (X : FineSaturatedLogScheme.{u}) (a : FSLogGroupAction G X)
    (B : X.scheme.IdealSheafData) (_h : AbelianInput a B),
    ∃ (U : FineSaturatedLogScheme.{u}) (b : FSLogGroupAction G U)
      (BU : U.scheme.IdealSheafData) (_hu : AbelianInput b BU) (f : EtaleLogHom U X),
      IsAffine U.scheme ∧ Etale f.base ∧ Surjective f.base ∧ QuasiCompact f.base ∧
      f.IsStrict ∧ Inert b a (MonoidHom.id G) f ∧ BU = (B.comap f.base).radical ∧
      ∃ R : Rigidification b, Nonempty (RigidifiedQuotient R)
  comparison : ∀ (G H : Type v) [Group G] [Finite G] [Group H] [Finite H]
    (X Y : FineSaturatedLogScheme.{u}) (a : FSLogGroupAction G X)
    (b : FSLogGroupAction H Y) (BX : X.scheme.IdealSheafData)
    (BY : Y.scheme.IdealSheafData) (hx : AbelianInput a BX) (hy : AbelianInput b BY)
    (rho : H →* G) (f : EtaleLogHom Y X), f.IsStrict → Inert b a rho f →
    Comparison f (tower G X a BX hx) (tower H Y b BY hy)
  identity : ∀ (G : Type v) [Group G] [Finite G] (X : FineSaturatedLogScheme.{u})
    (a : FSLogGroupAction G X) (B : X.scheme.IdealSheafData) (h : AbelianInput a B)
    (f : EtaleLogHom X X) (hs : f.IsStrict) (hi : Inert a a (MonoidHom.id G) f),
    f.IsIdentity → ∀ i,
      (comparison G G X X a a B B h h (MonoidHom.id G) f hs hi).count i = i ∧
      ∃ e : EtaleLogHom ((tower G X a B h).level i) ((tower G X a B h).level i),
        e.IsIdentity ∧ HEq
          ((comparison G G X X a a B B h h (MonoidHom.id G) f hs hi).lift i) e
  composition : ∀ (G H K : Type v)
    [Group G] [Finite G] [Group H] [Finite H] [Group K] [Finite K]
    (X Y Z : FineSaturatedLogScheme.{u})
    (a : FSLogGroupAction G X) (b : FSLogGroupAction H Y) (c : FSLogGroupAction K Z)
    (BX : X.scheme.IdealSheafData) (BY : Y.scheme.IdealSheafData)
    (BZ : Z.scheme.IdealSheafData)
    (hx : AbelianInput a BX) (hy : AbelianInput b BY) (hz : AbelianInput c BZ)
    (rho : H →* G) (sigma : K →* H) (f : EtaleLogHom Y X) (g : EtaleLogHom Z Y)
    (hsf : f.IsStrict) (hsg : g.IsStrict) (hsc : (g.comp f).IsStrict)
    (hif : Inert b a rho f) (hig : Inert c b sigma g)
    (hic : Inert c a (rho.comp sigma) (g.comp f)), ∀ i,
      (comparison G K X Z a c BX BZ hx hz (rho.comp sigma) (g.comp f) hsc hic).count i =
        (comparison H K Y Z b c BY BZ hy hz sigma g hsg hig).count
          ((comparison G H X Y a b BX BY hx hy rho f hsf hif).count i) ∧
      HEq ((comparison G K X Z a c BX BZ hx hz
        (rho.comp sigma) (g.comp f) hsc hic).lift i)
        (((comparison H K Y Z b c BY BZ hy hz sigma g hsg hig).lift
          ((comparison G H X Y a b BX BY hx hy rho f hsf hif).count i)).comp
            ((comparison G H X Y a b BX BY hx hy rho f hsf hif).lift i))

/-- A first-stage saturated log blowup regularization. Source: ILO VIII 4.1.1
(blueprint: def-per-gabber-modification-data). -/
def FirstStage {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    {a : FSLogGroupAction G X} (T : Tower G X a) : Prop :=
  IsRegularScheme T.source.scheme ∧ T.source.IsLogRegular ∧
    ∀ i : Fin T.length, ∃ I, IsSaturatedLogBlowup (T.arrow i) I

/-- The second-stage deepest-boundary-stratum algorithm, tracking the OLD strict
transform until it is empty. Source: ILO VIII 4.1.6--4.1.8
(blueprint: def-per-gabber-modification-data). -/
structure SecondStage {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    {a : FSLogGroupAction G X} (T : Tower G X a) where
  boundary : ∀ i, (T.level i).scheme.IdealSheafData
  boundaries : T.Boundaries boundary
  oldBoundary : ∀ i, (T.level i).scheme.IdealSheafData
  initial : oldBoundary 0 = boundary 0
  transforms : ∀ i, oldBoundary i.succ =
    transform (T.arrow i).base (T.center i) (oldBoundary i.castSucc)
  stratum : ∀ i : Fin T.length, ∃ d : ℕ, 0 < d ∧
    (∀ x : (T.level i.castSucc).scheme, (oldBoundary i.castSucc).ncBranchCount x ≤ d) ∧
    (T.center i).radical = T.center i ∧
    ((T.center i).support : Set (T.level i.castSucc).scheme) =
      {x | (oldBoundary i.castSucc).ncBranchCount x = d} ∧
    (T.center i).support ≠ ⊥
  ordinary : ∀ i, OrdinaryStep (T.arrow i).base (T.center i)
  saturated : ∀ i, ∃ I, IsSaturatedLogBlowup (T.arrow i) I
  regular : ∀ i, IsRegularScheme (T.level i).scheme
  finished : (oldBoundary (Fin.last T.length)).support = ⊥
  snc : IsStrictNormalCrossingsBoundary (boundary (Fin.last T.length))
  gStrict : GStrict (T.action (Fin.last T.length)).baseAction (boundary (Fin.last T.length))

/-- The third-stage finite sequence of complete minimal-fixed-family rounds, with the
permissible local operations and transformed-plus-exceptional boundary at each step.
Source: ILO VIII 4.1.9, 4.2.11--4.2.13; X 1.4--1.7
(blueprint: def-per-gabber-modification-data). -/
structure ThirdStage {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    {a : FSLogGroupAction G X} (T : Tower G X a) where
  boundary : ∀ i, (T.level i).scheme.IdealSheafData
  boundaries : T.Boundaries boundary
  ordinary : ∀ i, OrdinaryStep (T.arrow i).base (T.center i)
  permissible : ∀ i, Permissible (boundary i.castSucc) (T.center i)
  nonemptyCenters : ∀ i, (T.center i).support ≠ ⊥
  boundaryTransform : ∀ i, boundary i.succ =
    (transform (T.arrow i).base (T.center i) (boundary i.castSucc) ⊓
      (T.center i).comap (T.arrow i).base).radical
  regular : ∀ i, IsRegularScheme (T.level i).scheme
  snc : ∀ i, IsStrictNormalCrossingsBoundary (boundary i)
  gStrict : ∀ i, GStrict (T.action i).baseAction (boundary i)
  rounds : ℕ
  cut : Fin (rounds + 1) →o Fin (T.length + 1)
  first : cut 0 = 0
  last : cut (Fin.last rounds) = Fin.last T.length
  fixedRounds : ∀ i : Fin rounds, Nonempty (FixedRound T (cut i.castSucc) (cut i.succ))
  abelian : AbelianInertia (T.action (Fin.last T.length))
  free : FreeOpen (T.action (Fin.last T.length)) (boundary (Fin.last T.length)).support.compl

/-- The four successive towers, each on the actual source of the preceding one.
Source: ILO VIII 5.6.1 (blueprint: def-per-gabber-modification-data). -/
structure FourStage (P : FourthProcedure.{u, v})
    (G : Type v) [Group G] [Finite G] (X : FineSaturatedLogScheme.{u})
    (a : FSLogGroupAction G X) where
  first : Tower G X a
  firstStage : FirstStage first
  second : Tower G first.source (first.action (Fin.last first.length))
  secondStage : SecondStage second
  third : Tower G second.source (second.action (Fin.last second.length))
  thirdStage : ThirdStage third
  fourthInput : AbelianInput (third.action (Fin.last third.length))
    (thirdStage.boundary (Fin.last third.length))

/-- The fourth tower, using the COMMON choice-free construction.
Source: ILO VIII 5.5.5 (blueprint: def-per-gabber-modification-data). -/
def FourStage.fourth {P : FourthProcedure.{u, v}} {G : Type v} [Group G] [Finite G]
    {X : FineSaturatedLogScheme.{u}} {a : FSLogGroupAction G X} (F : FourStage P G X a) :=
  P.tower G F.third.source (F.third.action (Fin.last F.third.length))
    (F.thirdStage.boundary (Fin.last F.third.length)) F.fourthInput

/-- The final fs log scheme. Source: ILO VIII 5.6.1
(blueprint: def-per-gabber-modification-data). -/
def FourStage.source {P : FourthProcedure.{u, v}} {G : Type v} [Group G] [Finite G]
    {X : FineSaturatedLogScheme.{u}} {a : FSLogGroupAction G X} (F : FourStage P G X a) :=
  F.fourth.source

/-- The composite of all four log modifications. Source: ILO VIII 5.6.1
(blueprint: def-per-gabber-modification-data). -/
def FourStage.map {P : FourthProcedure.{u, v}} {G : Type v} [Group G] [Finite G]
    {X : FineSaturatedLogScheme.{u}} {a : FSLogGroupAction G X}
    (F : FourStage P G X a) : EtaleLogHom F.source X :=
  F.fourth.map.comp (F.third.map.comp (F.second.map.comp F.first.map))

/-- All output assertions, including the dense unchanged open and the finite-projective-space
refinement for EVERY affine Noetherian base. Source: ILO VIII 1.1, 5.6.1 and the ample-base
refinement (blueprint: def-per-gabber-modification-data). -/
def FourStage.Output {P : FourthProcedure.{u, v}} {G : Type v} [Group G] [Finite G]
    {X : FineSaturatedLogScheme.{u}} {a : FSLogGroupAction G X} (F : FourStage P G X a) : Prop :=
  IsIntegral F.source.scheme ∧ F.source.IsLogRegular ∧
    (F.fourth.action (Fin.last F.fourth.length)).IsVeryTame ∧
    (F.fourth.action (Fin.last F.fourth.length)).IsEquivariant a F.map ∧
    IsProjectiveBundle F.map.base ∧
    (∃ (T : Tower G X a) (e : F.source.scheme ≅ T.source.scheme),
      e.hom ≫ T.map.base = F.map.base) ∧
    (∃ U : X.scheme.Opens,
      (U : Set X.scheme) = X.logStructure.trivialityLocus ∩ (freeLocus a : Set X.scheme) ∧
      Dense (U : Set X.scheme) ∧ IsIso (F.map.base ∣_ U)) ∧
    F.source.logStructure.trivialityLocus =
      F.map.base ⁻¹' (X.logStructure.trivialityLocus ∩ (freeLocus a : Set X.scheme)) ∧
    ∀ (B : Scheme.{u}) [IsAffine B] [IsNoetherian B] (p : X.scheme ⟶ B),
      LocallyOfFiniteType p → QuasiCompact p → QuasiProjective p →
      IsHProjective F.map.base ∧ QuasiProjective (F.map.base ≫ p) ∧
        LocallyOfFiniteType (F.map.base ≫ p) ∧ QuasiCompact (F.map.base ≫ p)

end GabberModification
end AlgebraicGeometry
