module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Sheaf.AlgebraicGeometry.OrderedNodalBranchOverlap
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # The nodal chart and its specified torus action

Source: Alper--Halpern-Leistner--Heinloth, Cartan--Iwahori--Matsumoto
Decompositions, Section 2, printed p.2 (blueprint: def-sfb-nodal-torus-chart).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.NodalTorusChart

variable (A : Type u) [CommRing A] (π : A)

/-- The chart as an actual scheme over Spec A. Source: AHLH, Section 2, p.2
(blueprint: def-sfb-nodal-torus-chart). -/
def chart : Over (Spec (.of A)) :=
  Over.mk (StrictSemistableModel.nodal (A := .of A) π).baseMap

/-- The multiplicative group over A, with its Laurent Hopf algebra group law: the
recorded `RingGroupSchemes.multiplicative` (def-sfb-split-torus-over-ring), not a copy.
Source: AHLH, Section 2, p.2 (blueprint: def-sfb-nodal-torus-chart). -/
abbrev torus : Grp (Over (Spec (.of A))) :=
  RingGroupSchemes.multiplicative A

/-- Pullback of a coordinate function to any test scheme.
Source: AHLH, Section 2, p.2 (blueprint: def-sfb-nodal-torus-chart). -/
def value {T : Over (Spec (.of A))} (x : T ⟶ chart A π) (i : Fin 2) : Γ(T.left, ⊤) :=
  x.left.appTop (strictNodalCoordinate (.of A) π i)

/-- The Laurent coordinate of a torus point, for either exponent 1 or -1.
Source: AHLH, Section 2, p.2 (blueprint: def-sfb-nodal-torus-chart). -/
def torusValue {T : Over (Spec (.of A))} (z : T ⟶ (torus A).X) (n : ℤ) : Γ(T.left, ⊤) :=
  z.left.appTop ((Scheme.ΓSpecIso (.of (LaurentPolynomial A))).inv (LaurentPolynomial.T n))

/-- A specified action is the standard action precisely when its coordinates have
weights 1 and -1 on all test schemes. These equations determine the action uniquely;
they do not permit an arbitrary action. Source: AHLH, Section 2, p.2
(blueprint: def-sfb-nodal-torus-chart). -/
def IsStandardAction (a : ModObj (torus A).X (chart A π)) : Prop :=
  ∀ (T : Over (Spec (.of A))) (z : T ⟶ (torus A).X) (x : T ⟶ chart A π),
    value A π (lift z x ≫ a.smul) 0 = torusValue A z 1 * value A π x 0 ∧
    value A π (lift z x ≫ a.smul) 1 = torusValue A z (-1) * value A π x 1

/-- The puncture D(s) ∪ D(t), the complement of V(s,t).
Source: AHLH, Section 2, p.2 (blueprint: def-sfb-nodal-torus-chart). -/
def puncture : (chart A π).left.Opens :=
  (chart A π).left.basicOpen (strictNodalCoordinate (.of A) π 0) ⊔
    (chart A π).left.basicOpen (strictNodalCoordinate (.of A) π 1)

/-- The punctured chart as a scheme over Spec A.
Source: AHLH, Section 2, p.2 (blueprint: def-sfb-nodal-torus-chart). -/
def openChart : Over (Spec (.of A)) :=
  Over.mk ((puncture A π).ι ≫ (chart A π).hom)

/-- The actual open inclusion. Source: AHLH, Section 2, p.2
(blueprint: def-sfb-nodal-torus-chart). -/
def inclusion : openChart A π ⟶ chart A π :=
  Over.homMk (puncture A π).ι rfl

/-- The coordinate formulas determine a unique action on the actual nodal chart.
Source: AHLH, Section 2, p.2 (blueprint: def-sfb-nodal-torus-chart).
Proof: on A[s,t] substitute s ↦ z s and t ↦ z⁻¹ t. The relation st-π is
preserved, so this descends to the quotient. Substitution at z=1 is the identity,
and two successive substitutions multiply the Laurent parameters. Thus these
maps define an action. Maps into an affine scheme are determined by their
coordinate functions, proving uniqueness by Yoneda and extensionality of ModObj. -/
theorem standardAction_existsUnique :
    ∃! a : ModObj (torus A).X (chart A π), IsStandardAction A π a := by
  sorry

/-- The uniquely determined action with weights 1 and -1. Its data is fixed by
all coordinate formulas, rather than chosen from mere existence.
Source: AHLH, Section 2, p.2 (blueprint: def-sfb-nodal-torus-chart). -/
noncomputable instance standardAction : ModObj (torus A).X (chart A π) :=
  (standardAction_existsUnique A π).exists.choose

/-- The standard action restricts uniquely to D(s) ∪ D(t).
Source: AHLH, Section 2, p.2 (blueprint: def-sfb-nodal-torus-chart).
Proof: multiplication by the invertible z or z⁻¹ preserves each principal
open. Therefore the action factors uniquely through the open immersion on
G_m × U. The action laws follow after composing with this monomorphism.
Uniqueness follows from the same monomorphism and extensionality of ModObj. -/
theorem openAction_existsUnique :
    ∃! a : ModObj (torus A).X (openChart A π),
      ∀ (T : Over (Spec (.of A))) (z : T ⟶ (torus A).X) (x : T ⟶ openChart A π),
        (lift z x ≫ a.smul) ≫ inclusion A π = z • (x ≫ inclusion A π) := by
  sorry

/-- Restriction of the specified action, uniquely determined through the open immersion.
Source: AHLH, Section 2, p.2 (blueprint: def-sfb-nodal-torus-chart). -/
noncomputable instance openAction : ModObj (torus A).X (openChart A π) :=
  (openAction_existsUnique A π).exists.choose

end AlgebraicGeometry.NodalTorusChart
