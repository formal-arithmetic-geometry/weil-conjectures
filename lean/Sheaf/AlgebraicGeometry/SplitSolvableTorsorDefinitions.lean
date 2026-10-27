module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Split solvable groups and represented right torsors

Source: Milne, Algebraic Groups (2017), Definition 6.33 and Sections 2.66--2.72.
(blueprint: def-sfb-split-solvable-right-torsors)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A split series of the specified length. At each step the next smooth connected
closed normal subgroup has represented fppf quotient G_a or G_m; length zero is the
trivial group. The quotient interface identifies the actual scheme-theoretic kernel.
Source: Milne, Definition 6.33 (blueprint: def-sfb-split-solvable-right-torsors). -/
def SplitSolvableLength {k : Type u} [Field k]
    (H : Grp (Over (Spec (.of k)))) : ℕ → Prop
  | 0 => Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧ Nonempty (H ≅ Grp.trivial _)
  | n + 1 => Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧
      ∃ (N Q : Grp (Over (Spec (.of k)))) (i : N ⟶ H) (q : H ⟶ Q),
        IsClosedSubgroupScheme i.hom.hom ∧ IsNormalSubgroupScheme i.hom.hom ∧
        SolvableGroupStructure.IsFppfQuotient i.hom.hom q ∧
        (Nonempty (Q ≅ Grp.mk (StandardGroupSchemes.additive k)) ∨
          Nonempty (Q ≅ Grp.mk (StandardGroupSchemes.multiplicative k))) ∧
        SplitSolvableLength N n

/-- Existence of a finite split series, including the zero-length series.
Source: Milne, Definition 6.33 (blueprint: def-sfb-split-solvable-right-torsors). -/
def IsSplitSolvable {k : Type u} [Field k] (H : Grp (Over (Spec (.of k)))) : Prop :=
  ∃ n : ℕ, SplitSolvableLength H n

/-- A represented right H-torsor over S. The action is a scheme morphism, the laws
are tested on every scheme, and the cartesian square says precisely that
(p,h) ↦ (p,ph) identifies P × H with P ×_S P. Finite presentation is locally finite
presentation plus quasi-compactness and quasi-separatedness; faithful flatness is
flatness and surjectivity. No choice of a local section is part of the data.
Source: Milne, 2.66--2.72 (blueprint: def-sfb-split-solvable-right-torsors). -/
structure RepresentedRightTorsor {B : Scheme.{u}} (H : Grp (Over B)) (S : Over B) where
  space : Over B
  projection : space ⟶ S
  action : space ⊗ H.X ⟶ space
  flat : Flat projection.left
  surjective : Surjective projection.left
  lfp : LocallyOfFinitePresentation projection.left
  qc : QuasiCompact projection.left
  qs : QuasiSeparated projection.left
  one_action : ∀ (T : Over B) (p : T ⟶ space), lift p 1 ≫ action = p
  mul_action : ∀ (T : Over B) (p : T ⟶ space) (g h : T ⟶ H.X),
    lift (lift p g ≫ action) h ≫ action = lift p (g * h) ≫ action
  torsor : IsPullback (fst space H.X) action projection projection

/-- Equivariant triviality on a Zariski neighbourhood of each point. The cartesian
square expresses an isomorphism U × H ≅ P ×_S U over U, with its specified action.
Source: Milne, Proposition 16.55(c)
(blueprint: def-sfb-split-solvable-right-torsors). -/
def RepresentedRightTorsor.IsZariskiLocallyTrivial {B : Scheme.{u}}
    {H : Grp (Over B)} {S : Over B} (P : RepresentedRightTorsor H S) : Prop :=
  ∀ x : S.left, ∃ (U : Over B) (j : U ⟶ S),
    IsOpenImmersion j.left ∧ x ∈ Set.range j.left.base ∧
    ∃ t : U ⊗ H.X ⟶ P.space,
      IsPullback t (fst U H.X) P.projection j ∧
      ∀ (T : Over B) (a : T ⟶ U) (g h : T ⟶ H.X),
        lift a (g * h) ≫ t = lift (lift a g ≫ t) h ≫ P.action

end AlgebraicGeometry
