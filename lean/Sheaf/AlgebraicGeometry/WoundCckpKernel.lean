module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology

/-! # Wound groups and the cckp-kernel condition

Source: Conrad, The structure of solvable groups over general fields (2014),
Definitions 2.1 and 3.1, printed pp.10 and 15 (blueprint: def-sfb-wound-cckp-kernel).

These predicates specify actual morphisms and their universal properties; they choose no data.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A wound group is smooth, connected, affine of finite type and unipotent, and every
scheme morphism from the affine line factors through a rational point. The morphisms
are in the category of schemes over k, with no homomorphism condition.
Source: Conrad, Definition 2.1, printed p.10 (blueprint: def-sfb-wound-cckp-kernel). -/
def IsWound {k : Type u} [Field k] (G : Grp (Over (Spec (.of k)))) : Prop :=
  SolvableGroupStructure.IsAlgebraic G ∧ Smooth G.X.hom ∧ ConnectedSpace G.X.left ∧
    SolvableGroupStructure.IsUnipotent G ∧
    ∀ f : StandardGroupSchemes.additive k ⟶ G.X,
      ∃ x : StandardGroupSchemes.affine k k ⟶ G.X,
        f = StandardGroupSchemes.map k (Algebra.ofId k (Polynomial k)) ≫ x

/-- A smooth connected central closed subgroup killed by p. Centrality is the existing
universal centralizer condition, and p-torsion is tested on every commutative algebra,
including nonreduced algebras.
Source: Conrad, Definition 3.1, printed p.15 (blueprint: def-sfb-wound-cckp-kernel). -/
def IsCentralPTorsionSubgroup {k : Type u} [Field k] (p : ℕ)
    {F U : Grp (Over (Spec (.of k)))} (i : F ⟶ U) : Prop :=
  SolvableGroupStructure.IsAlgebraic F ∧ IsClosedSubgroupScheme i.hom.hom ∧
    Smooth F.X.hom ∧ ConnectedSpace F.X.left ∧
    (∀ (A : Type u) [CommRing A] [Algebra k A]
      (x : StandardGroupSchemes.affine k A ⟶ F.X),
      x ≫ i.hom.hom ∈ ReductiveTorusCentralizer.centralizerPoints (𝟙 U) A) ∧
    ∀ (A : Type u) [CommRing A] [Algebra k A]
      (x : StandardGroupSchemes.affine k A ⟶ F.X), x ^ p = 1

/-- The cckp-kernel condition is largestness among smooth connected central closed
subgroups killed by p, expressed by factorization of their group-scheme inclusions.
Source: Conrad, Definition 3.1, printed p.15 (blueprint: def-sfb-wound-cckp-kernel). -/
def IsCckpKernel {k : Type u} [Field k] (p : ℕ)
    {F U : Grp (Over (Spec (.of k)))} (i : F ⟶ U) : Prop :=
  IsCentralPTorsionSubgroup p i ∧
    ∀ (B : Grp (Over (Spec (.of k)))) (j : B ⟶ U),
      IsCentralPTorsionSubgroup p j → ∃ f : B ⟶ F, f ≫ i = j

end AlgebraicGeometry
