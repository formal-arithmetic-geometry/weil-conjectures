module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.GroupScheme.RelativeReductive
public import Sheaf.AlgebraicGeometry.GroupScheme.RelativeReductiveConditions
public import Sheaf.AlgebraicGeometry.RelativeSplitTorus
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Relative reductive groups and central coverings

Source: Conrad, Reductive group schemes, Definitions 3.1.1 and 3.2.1,
Example 5.1.7, and Exercise 6.5.2(i).
(blueprint: def-sfb-relative-reductive-cover-terminology).

The relative predicates use the recorded geometric-field predicates and actual
pullbacks of group objects. Centrality is tested on every scheme over the base.
Relative reductivity is the recorded `GroupScheme.IsReductive`
(def-sfb-relative-reductive-group), and simply connected semisimple geometric fibres are
the recorded `RelativeReductive.HasSimplyConnectedSemisimpleFibres`
(def-sfb-relative-reductive-conditions); both are reused here, not redefined.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.RelativeReductiveCover

/-- A central homomorphism has central image on all test schemes, including nonreduced ones.
Source: Conrad, Definition 3.3.9 and Example 5.1.7
(blueprint: def-sfb-relative-reductive-cover-terminology). -/
def IsCentral {B : Scheme.{u}} {N G : Over B} [GrpObj N] [GrpObj G]
    (i : N ⟶ G) : Prop :=
  ∀ (V : Over B) (n : V ⟶ N) (g : V ⟶ G),
    (n ≫ i) * g = g * (n ≫ i)

/-- Smooth affine finitely presented with reductive connected geometric fibres: the recorded
relative reductivity predicate of def-sfb-relative-reductive-group (its quasi-compactness and
quasi-separatedness clauses follow from affineness). Source: Conrad, Definition 3.1.1
(blueprint: def-sfb-relative-reductive-cover-terminology). -/
abbrev IsReductive {B : Scheme.{u}} (G : Grp (Over B)) : Prop :=
  AlgebraicGeometry.GroupScheme.IsReductive G

/-- Smooth affine finitely presented with semisimple connected geometric fibres.
Source: Conrad, Definition 3.1.1
(blueprint: def-sfb-relative-reductive-cover-terminology). -/
def IsSemisimple {B : Scheme.{u}} (G : Grp (Over B)) : Prop :=
  Smooth G.X.hom ∧ IsAffineHom G.X.hom ∧ LocallyOfFinitePresentation G.X.hom ∧
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ B),
      IsSemisimpleGroupScheme ((Over.pullback s).mapGrp.obj G).X

/-- Every geometric fibre is semisimple and simply connected: every surjective homomorphism
onto it from a semisimple group with finite central scheme-theoretic kernel is an isomorphism.
This is the recorded predicate of def-sfb-relative-reductive-conditions.
Source: Conrad, Exercise 6.5.2(i)
(blueprint: def-sfb-relative-reductive-cover-terminology). -/
abbrev HasSimplyConnectedFibres {B : Scheme.{u}} (G : Grp (Over B)) : Prop :=
  AlgebraicGeometry.RelativeReductive.HasSimplyConnectedSemisimpleFibres G

/-- A closed split torus whose geometric fibres are maximal tori, with rank zero allowed.
Source: Conrad, Definition 3.2.1 and Section 5.1
(blueprint: def-sfb-relative-reductive-cover-terminology). -/
def IsSplitMaximalTorus {B : Scheme.{u}} {T G : Grp (Over B)} (i : T ⟶ G) : Prop :=
  IsClosedImmersion i.hom.hom.left ∧
    (∃ r : ℕ, Nonempty (T ≅ relativeSplitTorus B r)) ∧
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ B),
      ReductiveTorusCentralizer.IsMaximalTorus ((Over.pullback s).mapGrp.map i)

/-- A closed subgroup whose geometric fibres are Borel subgroups, using the recorded
scheme-theoretic derived-series predicate. Source: Conrad, Section 5.2
(blueprint: def-sfb-relative-reductive-cover-terminology). -/
def IsBorel {B : Scheme.{u}} {P G : Grp (Over B)} (i : P ⟶ G) : Prop :=
  IsClosedImmersion i.hom.hom.left ∧
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ B),
      IsBorelGroupScheme ((Over.pullback s).mapGrp.map i).hom.hom

/-- Existence of a split maximal torus. Over Spec Z this is the splitness criterion;
its arbitrary scalar extensions remain split. Source: Conrad, Example 5.1.4
(blueprint: def-sfb-relative-reductive-cover-terminology). -/
def HasSplitMaximalTorus {B : Scheme.{u}} (G : Grp (Over B)) : Prop :=
  ∃ (T : Grp (Over B)) (i : T ⟶ G), IsSplitMaximalTorus i

end AlgebraicGeometry.RelativeReductiveCover
