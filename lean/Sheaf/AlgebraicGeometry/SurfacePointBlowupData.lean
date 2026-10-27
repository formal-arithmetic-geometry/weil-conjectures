module

public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Sheaf.AlgebraicGeometry.ProjectiveNodalTower
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Point blowups, fibre coefficients and iterated strict transforms

Source: Stacks Project, resolve.tex, Tags 0AGQ and 0AGR; divisors.tex, Tag 080E;
models.tex, Tags 0CDC and 0CDD; the fibre-divisor calculation in
lem-sfb-point-blowup-fibre-defects (blueprint: def-sfb-surface-point-blowup-data).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SurfacePointBlowup

/-- The ideal of the reduced closed point, not a chosen thickening.
Source: resolve.tex, Tag 0AGQ (blueprint: def-sfb-surface-point-blowup-data). -/
def pointIdeal {X : Scheme.{u}} (p : X) (hp : IsClosed ({p} : Set X)) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩

/-- The image of a trait element in the actual local ring of its total space.
Source: the divisor calculation following resolve.tex, Tag 0AGQ
(blueprint: def-sfb-surface-point-blowup-data). -/
def germ {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (x : X) (a : R) : X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial) a

/-- Exact maximal-ideal order, expressed without making a choice of a maximum.
Source: the initial-form calculation in lem-sfb-point-blowup-fibre-defects, Step 3
(blueprint: def-sfb-surface-point-blowup-data). -/
def HasOrder {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (x : X) (a : R) (d : ℕ) : Prop :=
  germ f x a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ d ∧
    germ f x a ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (d + 1)

/-- The divisor coefficient at a component generic point is the length of the quotient
of the ambient local ring by the trait element. In a DVR this is its normalized valuation.
Source: Stacks Project, Algebra, Tag 02MD; resolve.tex, Tag 0AGQ
(blueprint: def-sfb-surface-point-blowup-data). -/
def coefficient {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (x : X) (a : R) : ℕ∞ :=
  Ring.ord (X.presheaf.stalk x) (germ f x a)

/-- The canonical map on residue fields over a closed point of the trait.
Source: Stacks Project, Schemes, residue fields
(blueprint: def-sfb-surface-point-blowup-data). -/
def residueMap {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (x : X) (hx : f x = IsLocalRing.closedPoint R) :
    (Spec (.of R)).residueField (IsLocalRing.closedPoint R) ⟶ X.residueField x :=
  ((Spec (.of R)).residueFieldCongr hx).inv ≫ f.residueFieldMap x

/-- The canonical map from a field to the residue field at a point of a scheme over it.
Source: Stacks Project, Schemes, residue fields
(blueprint: def-sfb-surface-point-blowup-data). -/
def fieldMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) : k →+* X.residueField x :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom

/-- An integral reduced component of the scheme-theoretic special fibre, embedded in
its total space. The component is taken in the fibre, not in the total surface.
Source: lem-sfb-point-blowup-fibre-defects, Step 4
(blueprint: def-sfb-surface-point-blowup-data). -/
def IsSpecialComponent {R : Type u} [CommRing R] [IsLocalRing R]
    {X C : Scheme.{u}} (f : X ⟶ Spec (.of R)) (i : C ⟶ X) : Prop :=
  IsIntegral C ∧ IsClosedImmersion i ∧
    ∃ Z : Set (f.fiber (IsLocalRing.closedPoint R)),
      Z ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)) ∧
        Set.range i = (f.fiberι (IsLocalRing.closedPoint R)) '' Z

/-- A finite sequence of point blowups, together with the actual iterated strict
transform of a given morphism and its canonical projection to the original source.
The zero-step case is included. Each successor uses the canonical blowup of the
reduced closed special-fibre point and the existing scheme-theoretic strict transform.
Source: resolve.tex, Tags 0AGQ and 0AGR; divisors.tex, Tag 080E; the induction in
lem-sfb-point-blowup-fibre-defects, Steps 2, 4, 5 and 7
(blueprint: def-sfb-surface-point-blowup-data). -/
inductive TransformChain (R : Type u) [CommRing R] [IsLocalRing R] :
    {X Y C D : Scheme.{u}} → (X ⟶ Spec (.of R)) → (Y ⟶ Spec (.of R)) →
      (C ⟶ X) → (D ⟶ Y) → (D ⟶ C) → Prop where
  /-- A sequence of length zero, with the identity projection.
  Source: induction on the number of blowups
  (blueprint: def-sfb-surface-point-blowup-data). -/
  | refl {X C : Scheme.{u}} (f : X ⟶ Spec (.of R)) (i : C ⟶ X) :
      TransformChain R f f i i (𝟙 C)
  /-- Append the blowup at a reduced closed special-fibre point and take strict transform.
  Source: divisors.tex, Tag 080E
  (blueprint: def-sfb-surface-point-blowup-data). -/
  | step {X Y C D : Scheme.{u}} {f : X ⟶ Spec (.of R)}
      {g : Y ⟶ Spec (.of R)} {i : C ⟶ X} {j : D ⟶ Y} {r : D ⟶ C}
      (previous : TransformChain R f g i j r) (p : Y)
      (hp : IsClosed ({p} : Set Y)) (hs : g p = IsLocalRing.closedPoint R) :
      TransformChain R f ((pointIdeal p hp).blowupMap ≫ g) i
        (strictTransformMap j (pointIdeal p hp).blowupMap (pointIdeal p hp).support.compl)
        (strictTransformToSource j (pointIdeal p hp).blowupMap
          (pointIdeal p hp).support.compl ≫ r)

/-- The canonical point-blowup family over the trait.
Source: resolve.tex, Tag 0AGQ (blueprint: def-sfb-surface-point-blowup-data). -/
def family {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (p : X) (hp : IsClosed ({p} : Set X)) :
    (pointIdeal p hp).blowup ⟶ Spec (.of R) :=
  (pointIdeal p hp).blowupMap ≫ f

/-- The scheme-theoretic exceptional fibre, with its existing residue-field projection.
Source: resolve.tex, Tag 0AGQ (blueprint: def-sfb-surface-point-blowup-data). -/
abbrev exceptional {X : Scheme.{u}} (p : X) (hp : IsClosed ({p} : Set X)) : Scheme.{u} :=
  (pointIdeal p hp).blowupMap.fiber p

/-- Its canonical closed immersion into the blown-up surface.
Source: resolve.tex, Tag 0AGQ (blueprint: def-sfb-surface-point-blowup-data). -/
def exceptionalι {X : Scheme.{u}} (p : X) (hp : IsClosed ({p} : Set X)) :
    exceptional p hp ⟶ (pointIdeal p hp).blowup :=
  (pointIdeal p hp).blowupMap.fiberι p

/-- The exceptional curve as a scheme over the centre residue field.
Source: resolve.tex, Tag 0AGQ (blueprint: def-sfb-surface-point-blowup-data). -/
def exceptionalToField {X : Scheme.{u}} (p : X) (hp : IsClosed ({p} : Set X)) :
    exceptional p hp ⟶ Spec (X.residueField p) :=
  (pointIdeal p hp).blowupMap.fiberToSpecResidueField p

/-- The exceptional curve over the original trait residue field, using the canonical
residue-field map, so inseparability refers to the specified extension.
Source: the inseparability calculation in lem-sfb-point-blowup-fibre-defects, Step 6
(blueprint: def-sfb-surface-point-blowup-data). -/
def exceptionalToResidue {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (p : X) (hp : IsClosed ({p} : Set X))
    (hs : f p = IsLocalRing.closedPoint R) :
    exceptional p hp ⟶ Spec ((Spec (.of R)).residueField (IsLocalRing.closedPoint R)) :=
  exceptionalToField p hp ≫ Spec.map (residueMap f p hs)

/-- Nodal geometric fibres on a neighbourhood of a specified subset, allowing empty
and disconnected fibres. Reducedness is explicit, as in the fibre-defects statement.
Source: models.tex, Tags 0CDC and 0CDD; curves.tex, Tag 0C5D
(blueprint: def-sfb-surface-point-blowup-data). -/
def IsNodalNear {X S : Scheme.{u}} (f : X ⟶ S) (Z : Set X) : Prop :=
  ∃ U : X.Opens, Z ⊆ U ∧ Flat (U.ι ≫ f) ∧ LocallyOfFinitePresentation (U.ι ≫ f) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ S),
      IsReduced (pullback (C := Scheme.{u}) (U.ι ≫ f) g) ∧
      Scheme.IsPureDimension (pullback (C := Scheme.{u}) (U.ι ≫ f) g) 1 ∧
      ∀ x : pullback (C := Scheme.{u}) (U.ι ≫ f) g,
        IsClosed ({x} : Set (pullback (C := Scheme.{u}) (U.ι ≫ f) g)) →
        (¬ ∃ V : (pullback (C := Scheme.{u}) (U.ι ≫ f) g).Opens,
          x ∈ V ∧ Smooth (V.ι ≫ pullback.snd (U.ι ≫ f) g)) →
        IsGeometricOrdinaryDoublePoint Ω (pullback (C := Scheme.{u}) (U.ι ≫ f) g) x

end AlgebraicGeometry.SurfacePointBlowup
