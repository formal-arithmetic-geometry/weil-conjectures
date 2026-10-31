/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HilbertSamuelInvariant
public import WeilConjectures.AlgebraicGeometry.MarkedIdealOrder
public import WeilConjectures.AlgebraicGeometry.AdaptedNormalCrossingsCenter
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Hilbert--Samuel presentations and their finite tests

Source: BMT, arXiv:0905.3580, sections 5.1--5.2 and 6.1--6.3; BM 1997, Definition 6.2
(blueprint: def-trf-hilbert-samuel-presentation).
Normal crossings uses the existing `HasAdaptedNormalCrossingsCenter`; for smooth rational
ambients its regular parameters extend to an étale coordinate chart.
The depth-indexed predicates quantify over every finite test sequence. Transforms are specified
by cartesian or scheme-theoretic strict-transform squares and equality of ideal sheaves.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.HilbertSamuel

variable (k : Type u) [Field k]

/-- A smooth ambient, a closed embedded scheme, a retained level and the ordered test boundary.
Earlier exceptional history is deliberately not part of this boundary. Source: BMT 6.2
(blueprint: def-trf-hilbert-samuel-presentation). -/
structure Embedded where
  Z : Scheme.{u}
  p : Z ⟶ Spec (.of k)
  smooth : Smooth p
  X : Scheme.{u}
  i : X ⟶ Z
  closed : IsClosedImmersion i
  level : ℕ → ℕ
  boundary : List Z.IdealSheafData

variable {k}

/-- The equality locus, considered inside the ambient. Source: BMT 6.2 after shrinking
away from larger levels (blueprint: def-trf-hilbert-samuel-presentation). -/
noncomputable def Embedded.locus (S : Embedded k) : Set S.Z :=
  S.i '' {x | function (S.i ≫ S.p) x = S.level}

/-- Marked coefficient data on a smooth closed subspace of the ambient. The ideal is genuinely
coherent and the marking is positive. The field `coherent` uses the recorded
`Scheme.Modules.IsQuasiCoherentFiniteType`: since `N` is smooth over a field, it is locally
Noetherian, so this is equivalent to coherence (Stacks Project, Tag 01XZ).
Source: BMT 5.1 and 6.2
(blueprint: def-trf-hilbert-samuel-presentation). -/
structure Marked (S : Embedded k) where
  N : Scheme.{u}
  j : N ⟶ S.Z
  closed : IsClosedImmersion j
  smooth : Smooth (j ≫ S.p)
  ideal : N.IdealSheafData
  coherent : Scheme.Modules.IsQuasiCoherentFiniteType ideal.toModules
  marking : ℕ
  positive : 0 < marking

/-- Cosupport in the ambient. Source: BMT 5.1
(blueprint: def-trf-hilbert-samuel-presentation). -/
noncomputable def Marked.cosupport {S : Embedded k} (M : Marked S) : Set S.Z :=
  M.j '' {x | (M.marking : ℕ∞) ≤ order M.ideal x}

/-- Three permitted operation types. Source: BMT 5.2
(blueprint: def-trf-hilbert-samuel-presentation). -/
inductive TestKind where
  | admissibleBlowup
  | line
  | exceptionalIntersection
  deriving DecidableEq

/-- Strict transforms of the ordered old boundary, followed by the new exceptional ideal.
Source: BMT 5.2 (blueprint: def-trf-hilbert-samuel-presentation). -/
noncomputable def blowupBoundary {S : Embedded k} {Z' : Scheme.{u}} (π : Z' ⟶ S.Z)
    (C : S.Z.IdealSheafData) : List Z'.IdealSheafData :=
  S.boundary.map (fun D ↦ (strictTransformMap D.subschemeι π C.support.compl).ker) ++
    [C.comap π]

/-- The zero section of the relative affine line. Source: BMT 5.2
(blueprint: def-trf-hilbert-samuel-presentation). -/
noncomputable def lineZero (Z : Scheme.{u}) :
    Z ⟶ AffineSpace (ULift.{u} (Fin 1)) Z :=
  AffineSpace.homOfVector (𝟙 Z) (fun _ ↦ 0)

/-- Geometric test operation, before choosing whether the center is admissible for the
Hilbert--Samuel stratum or for a marked ideal. Blowups use the existing global blowup.
Source: BMT 5.2 and 6.2 (blueprint: def-trf-hilbert-samuel-presentation). -/
structure Step (S T : Embedded k) where
  kind : TestKind
  π : T.Z ⟶ S.Z
  center : S.Z.IdealSheafData
  over_base : π ≫ S.p = T.p
  geometry : match kind with
    | .line =>
      center = ⊤ ∧ ∃ e : T.Z ≅ AffineSpace (ULift.{u} (Fin 1)) S.Z,
        π = e.hom ≫ (AffineSpace (ULift.{u} (Fin 1)) S.Z ↘ S.Z) ∧
        T.boundary = S.boundary.map (fun D ↦ D.comap π) ++ [(lineZero S.Z).ker.comap e.hom]
    | .admissibleBlowup =>
      ∃ e : T.Z ≅ center.blowup,
        π = e.hom ≫ center.blowupMap ∧ Smooth (center.subschemeι ≫ S.p) ∧
        HasAdaptedNormalCrossingsCenter center (fun i ↦ S.boundary.get i) ∧
        T.boundary = blowupBoundary π center
    | .exceptionalIntersection =>
      ∃ (a b : Fin S.boundary.length), a ≠ b ∧
        center = S.boundary.get a ⊔ S.boundary.get b ∧
        ∃ e : T.Z ≅ (S.boundary.get a ⊔ S.boundary.get b).blowup,
          π = e.hom ≫ (S.boundary.get a ⊔ S.boundary.get b).blowupMap ∧
          T.boundary = blowupBoundary π (S.boundary.get a ⊔ S.boundary.get b)
  schemeTransform : match kind with
    | .admissibleBlowup =>
      ∃ q : T.X ≅ strictTransform S.i π center.support.compl,
        T.i = q.hom ≫ strictTransformMap S.i π center.support.compl
    | _ => ∃ q : T.X ⟶ S.X, IsPullback q T.i S.i π
  levelTransform : T.level = if kind = .line then summation S.level else S.level

/-- The center, specified intrinsically by the blowup isomorphism in an admissible step.
All choices satisfying this characterization are quantified over, never arbitrarily selected.
Source: BMT 5.2 (blueprint: def-trf-hilbert-samuel-presentation). -/
def Step.HasCenter {S T : Embedded k} (s : Step S T) (C : S.Z.IdealSheafData) : Prop :=
  s.kind = .admissibleBlowup ∧ C = s.center

/-- Admissibility against a given ambient subset. The other two test operations are unrestricted.
Source: BMT 5.2 and 6.2 (blueprint: def-trf-hilbert-samuel-presentation). -/
def Step.Admissible {S T : Embedded k} (s : Step S T) (L : Set S.Z) : Prop :=
  s.kind ≠ .admissibleBlowup ∨
    ∃ C : S.Z.IdealSheafData, s.HasCenter C ∧ Set.range C.subschemeι ⊆ L

/-- Transformation of marked data: strict transform and controlled ideal for an admissible
blowup; cartesian pullback and ordinary ideal pullback in the other cases. The controlled ideal
is characterized by multiplication by the marking-th exceptional power, so no arbitrary
quotient map is supplied. Source: BMT 5.1--5.2; BM 1997, formula (6.1)
(blueprint: def-trf-hilbert-samuel-presentation). -/
def Step.Transforms {S T : Embedded k} (s : Step S T) (M : Marked S) (M' : Marked T) : Prop :=
  M'.marking = M.marking ∧
  match s.kind with
  | .admissibleBlowup =>
    ∃ (C : S.Z.IdealSheafData) (_ : s.HasCenter C)
      (q : M'.N ≅ strictTransform M.j s.π C.support.compl),
      M'.j = q.hom ≫ strictTransformMap M.j s.π C.support.compl ∧
      M'.ideal * ((C.comap s.π).comap M'.j) ^ M.marking =
        M.ideal.comap (q.hom ≫ strictTransformToSource M.j s.π C.support.compl)
  | _ => ∃ q : M'.N ⟶ M.N,
      IsPullback q M'.j M.j s.π ∧ M'.ideal = M.ideal.comap q

/-- Presentation tested through a prescribed finite depth. The universal quantifier on every
successor, the existence of its transform, and the quantifier on every such transform exclude
vacuous tests and arbitrary choices of controlled transforms. Source: BMT 6.2
(blueprint: def-trf-hilbert-samuel-presentation). -/
noncomputable def PresentsThrough : ℕ → (S : Embedded k) → Marked S → Prop
  | 0, S, M => M.cosupport = S.locus
  | n + 1, S, M => M.cosupport = S.locus ∧
      ∀ (T : Embedded k) (s : Step S T),
        (s.Admissible S.locus →
          (∃ M' : Marked T, s.Transforms M M') ∧
          ∀ M' : Marked T, s.Transforms M M' → PresentsThrough n T M')

/-- A presentation agrees with the retaining-level locus after every finite admissible test
sequence. At its starting stage the test boundary is empty. Source: BMT 6.2
(blueprint: def-trf-hilbert-samuel-presentation). -/
noncomputable def Presents {S : Embedded k} (M : Marked S) : Prop :=
  S.boundary = [] ∧ ∀ n : ℕ, PresentsThrough n S M

/-- Equivalence through finite depth means that the cosupports and allowed next centers agree,
and that equivalence persists for every pair of transforms. Source: BMT 5.2
(blueprint: def-trf-hilbert-samuel-presentation). -/
noncomputable def EquivalentThrough : ℕ → (S : Embedded k) → Marked S → Marked S → Prop
  | 0, _, M, P => M.cosupport = P.cosupport
  | n + 1, S, M, P => M.cosupport = P.cosupport ∧
      ∀ (T : Embedded k) (s : Step S T),
        (s.Admissible M.cosupport →
          (∃ M' : Marked T, s.Transforms M M') ∧
          (∃ P' : Marked T, s.Transforms P P') ∧
          ∀ (M' P' : Marked T), s.Transforms M M' → s.Transforms P P' →
            EquivalentThrough n T M' P')

/-- Equality of all finite marked-ideal tests. Source: BMT 5.2
(blueprint: def-trf-hilbert-samuel-presentation). -/
noncomputable def Equivalent {S : Embedded k} (M P : Marked S) : Prop :=
  ∀ n : ℕ, EquivalentThrough n S M P

/-- Smooth pullback of an embedded situation, on a fixed relative-dimension piece; earlier
centers, when present, are supplied separately and do not become test boundary components.
Source: BMT 6.3 (blueprint: def-trf-hilbert-samuel-presentation). -/
def Pullback {S T : Embedded k} (f : T.Z ⟶ S.Z) (r : ℕ) : Prop :=
  SmoothOfRelativeDimension r f ∧ f ≫ S.p = T.p ∧
    (∃ g : T.X ⟶ S.X, IsPullback g T.i S.i f) ∧
    T.level = (summation^[r]) S.level ∧
    T.boundary = S.boundary.map (fun D ↦ D.comap f)

/-- Pullback of marked data, specified by its actual cartesian square and ideal equality.
Source: BMT 6.3 (blueprint: def-trf-hilbert-samuel-presentation). -/
def MarkedPullback {S T : Embedded k} (f : T.Z ⟶ S.Z) (M : Marked S) (P : Marked T) : Prop :=
  P.marking = M.marking ∧ ∃ g : P.N ⟶ M.N,
    IsPullback g P.j M.j f ∧ P.ideal = M.ideal.comap g

/-- Minimality of a smooth local envelope: its defining stalk ideal lies in the square of
its maximal ideal, equivalently the cotangent map is an isomorphism. Source: BMT 6.2
(blueprint: def-trf-hilbert-samuel-presentation). -/
noncomputable def MinimalAt (S : Embedded k) (x : S.X) : Prop :=
  stalkIdeal S.i.ker (S.i x) ≤ IsLocalRing.maximalIdeal (S.Z.presheaf.stalk (S.i x)) ^ 2

/-- Full-envelope maximal order; the isomorphism prevents replacing the whole envelope by a
proper closed subscheme. Source: BMT 6.2, with the node's singular-point qualification
(blueprint: def-trf-hilbert-samuel-presentation). -/
noncomputable def FullMaximalOrder {S : Embedded k} (M : Marked S) : Prop :=
  IsIso M.j ∧ ∀ x : M.N, M.j x ∈ M.cosupport → order M.ideal x = (M.marking : ℕ∞)

/-- Common étale comparison of two embedded germs at the same specified level. The cartesian
squares identify their copies of the same intrinsic scheme. The two maps pull back each ordered
earlier-center ideal identically. Source: BM 1997, Remarks 6.3 and Definition 6.4; BMT 6.2
(blueprint: def-trf-hilbert-samuel-presentation). -/
structure CommonComparison (S T : Embedded k) (x : S.X) (y : T.X)
    (intrinsic : S.X ≅ T.X) (earlierS : List S.Z.IdealSheafData)
    (earlierT : List T.Z.IdealSheafData) where
  W : Embedded k
  f : W.Z ⟶ S.Z
  g : W.Z ⟶ T.Z
  f_etale : Etale f
  g_etale : Etale g
  f_pullback : Pullback f 0
  g_pullback : Pullback g 0
  q : W.X ⟶ S.X
  squareS : IsPullback q W.i S.i f
  squareT : IsPullback (q ≫ intrinsic.hom) W.i T.i g
  w : W.X
  pointS : q w = x
  pointT : intrinsic.hom x = y
  earlier : earlierS.map (fun I ↦ I.comap f) = earlierT.map (fun I ↦ I.comap g)

/-- A smooth center inside the embedded scheme on which the intrinsic level is locally
constant; no normal-crossing boundary is needed for numerical nonincrease. Source: BMT 6.1
(blueprint: def-trf-hilbert-samuel-presentation). -/
noncomputable def LocallyConstantCenter (S : Embedded k) (C : S.Z.IdealSheafData) : Prop :=
  Smooth (C.subschemeι ≫ S.p) ∧ ∃ c : C.subscheme ⟶ S.X,
    c ≫ S.i = C.subschemeι ∧ ∀ a : C.subscheme,
      ∃ U : C.subscheme.Opens, a ∈ U ∧ ∀ b : C.subscheme, b ∈ U →
        function (S.i ≫ S.p) (c b) = function (S.i ≫ S.p) (c a)

/-- A blowup and its scheme-theoretic strict transform, with a locally constant smooth center.
The level can be reset after a drop; this relation records the intrinsic history independently
of a particular retained level. Source: BMT 6.1
(blueprint: def-trf-hilbert-samuel-presentation). -/
noncomputable def BlowupTransition (S T : Embedded k) : Prop :=
  ∃ (C : S.Z.IdealSheafData) (_ : LocallyConstantCenter S C)
    (e : T.Z ≅ C.blowup) (q : T.X ≅ C.strictTransform S.i),
    e.hom ≫ C.blowupMap ≫ S.p = T.p ∧
    T.i ≫ e.hom = q.hom ≫ strictTransformMap S.i C.blowupMap C.support.compl

/-- A pointed étale localization of the given locally closed embedding, together with its
presentation. Source: BMT 6.2 (blueprint: def-trf-hilbert-samuel-presentation). -/
noncomputable def LocalPresentationAt {X Z : Scheme.{u}} (p : Z ⟶ Spec (.of k))
    (i : X ⟶ Z) (x : X) : Prop :=
  ∃ (S : Embedded k) (f : S.Z ⟶ Z) (g : S.X ⟶ X) (a : S.X) (M : Marked S),
    Etale f ∧ f ≫ p = S.p ∧ IsPullback g S.i i f ∧ g a = x ∧
    S.level = function (i ≫ p) x ∧ Presents M

end AlgebraicGeometry.HilbertSamuel
