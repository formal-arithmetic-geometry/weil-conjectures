module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Sheaf.AlgebraicGeometry.RelativeTorus
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.GroupTheory.Finiteness

/-! # Relative reductive groups and central quotient terminology

Source: Conrad, Reductive group schemes, Definitions 3.1.1 and 3.2.1, Section 3.3,
Corollary 3.3.5, and Appendix B.1
(blueprint: def-sfb-relative-reductive-quotient-terminology).

The field predicates, relative torus predicate and represented fppf quotient presentation
are reused. Relative geometric conditions are tested at all algebraically closed fields.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonObj

namespace AlgebraicGeometry.RelativeReductive

/-- Multiplicative type over a scheme means fppf locally diagonalizable with finitely
generated character group. Affine splitting charts suffice by refinement.
Source: Conrad, Appendix B.1, pp.280--281
(blueprint: def-sfb-relative-reductive-quotient-terminology). -/
def IsMultiplicativeType {S : Scheme.{u}} (C : Grp (Over S)) : Prop :=
  ∃ (I : Type u) (R : I → CommRingCat.{u}) (N : I → AddCommGrpCat.{u})
    (f : ∀ i : I, Spec (R i) ⟶ S),
    (∀ i : I, AddGroup.FG (N i)) ∧
    Presieve.ofArrows (fun i : I ↦ Spec (R i)) f ∈ Scheme.fppfPrecoverage S ∧
    ∀ i : I, Nonempty (((Over.pullback (f i)).mapGrp.obj C) ≅
      ringDiagonalizableGroup (R i) (N i))

/-- Relative reductivity: smooth affine finite type, with reductive geometric fibres.
The field reductivity predicate includes geometric connectedness and excludes every
nontrivial smooth connected normal unipotent subgroup.
Source: Conrad, Definition 3.1.1, p.81
(blueprint: def-sfb-relative-reductive-quotient-terminology). -/
def IsReductive {S : Scheme.{u}} (G : Grp (Over S)) : Prop :=
  Smooth G.X.hom ∧ IsAffineHom G.X.hom ∧ LocallyOfFiniteType G.X.hom ∧
    QuasiCompact G.X.hom ∧
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      ReductiveTorusCentralizer.IsReductive ((Over.pullback s).mapGrp.obj G)

/-- A geometrically maximal relative torus, with its closed inclusion.
Source: Conrad, Definition 3.2.1, p.91
(blueprint: def-sfb-relative-reductive-quotient-terminology). -/
def IsMaximalTorus {S : Scheme.{u}} {T G : Grp (Over S)} (i : T ⟶ G) : Prop :=
  IsClosedImmersion i.hom.hom.left ∧ IsRelativeTorus T.X ∧
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      ReductiveTorusCentralizer.IsMaximalTorus ((Over.pullback s).mapGrp.map i)

/-- Centrality is commutation on all test schemes, hence includes every further
extension of a test algebra, including nonreduced ones.
Source: Conrad, Section 3.3, pp.96--100
(blueprint: def-sfb-relative-reductive-quotient-terminology). -/
def IsCentral {S : Scheme.{u}} {C G : Grp (Over S)} (i : C ⟶ G) : Prop :=
  ∀ (U : Over S) (c : U ⟶ C.X) (g : U ⟶ G.X), Commute (c ≫ i.hom.hom) g

/-- The represented scheme-theoretic centre. A point must commute with all group points
on every further test scheme; testing only commutation over its original ring is insufficient.
Source: Conrad, Theorem 3.3.4 and Corollary 3.3.5, pp.98--101
(blueprint: def-sfb-relative-reductive-quotient-terminology). -/
def IsCentre {S : Scheme.{u}} {Z G : Grp (Over S)} (z : Z ⟶ G) : Prop :=
  IsClosedImmersion z.hom.hom.left ∧
    ∀ U : Over S,
      Set.range (fun a : U ⟶ Z.X ↦ a ≫ z.hom.hom) =
        {g | ∀ (V : Over S) (f : V ⟶ U) (x : V ⟶ G.X), Commute (f ≫ g) x}

/-- A maximal-torus quotient presentation: C lies in T, T/C is a maximal torus of Q,
and T is exactly its scheme-theoretic inverse image under p. The quotient presentation
retains the kernel and the actual quotient map.
Source: Conrad, Corollary 3.3.5 and proof, pp.100--101
(blueprint: def-sfb-relative-reductive-quotient-terminology). -/
def IsMaximalTorusQuotientSquare {S : Scheme.{u}} {C G Q T U : Grp (Over S)}
    (c : C ⟶ G) (p : G ⟶ Q) (i : T ⟶ G) (j : U ⟶ Q) (q : T ⟶ U) : Prop :=
  IsMaximalTorus i ∧ IsMaximalTorus j ∧ IsPullback i.hom.hom q.hom.hom p.hom.hom j.hom.hom ∧
    ∃ k : C ⟶ T, k ≫ i = c ∧ IsFppfGroupQuotient k q

/-- The quotient and inverse-image maps give a correspondence on maximal torus subgroups.
Both projections of the relation are onto; its cartesian squares identify the inverse
image uniquely as a subgroup, so this is a bijection of subgroups, independent of presentations.
The last clause says that each specified quotient square pulls back to the same correspondence.
Source: Conrad, Corollary 3.3.5 and proof, pp.100--101
(blueprint: def-sfb-relative-reductive-quotient-terminology). -/
def HasMaximalTorusCorrespondence {S : Scheme.{u}} {C G Q : Grp (Over S)}
    (c : C ⟶ G) (p : G ⟶ Q) : Prop :=
  (∀ (T : Grp (Over S)) (i : T ⟶ G), IsMaximalTorus i →
    ∃ (U : Grp (Over S)) (j : U ⟶ Q) (q : T ⟶ U),
      IsMaximalTorusQuotientSquare c p i j q) ∧
  (∀ (U : Grp (Over S)) (j : U ⟶ Q), IsMaximalTorus j →
    ∃ (T : Grp (Over S)) (i : T ⟶ G) (q : T ⟶ U),
      IsMaximalTorusQuotientSquare c p i j q) ∧
  ∀ (T U : Grp (Over S)) (i : T ⟶ G) (j : U ⟶ Q) (q : T ⟶ U),
    IsMaximalTorusQuotientSquare c p i j q →
    ∀ (S' : Scheme.{u}) (f : S' ⟶ S),
      IsMaximalTorusQuotientSquare ((Over.pullback f).mapGrp.map c)
        ((Over.pullback f).mapGrp.map p) ((Over.pullback f).mapGrp.map i)
        ((Over.pullback f).mapGrp.map j) ((Over.pullback f).mapGrp.map q)

end AlgebraicGeometry.RelativeReductive
