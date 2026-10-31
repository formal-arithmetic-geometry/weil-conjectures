/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SolvableGroupStructure
public import Mathlib.Topology.Connected.Basic

/-! # Reductive groups, maximal tori, and centralizer points

Source: Milne, Algebraic Groups (2017), Chapter 17 and Proposition 1.92, pp.33--34
(blueprint: def-sfb-reductive-torus-centralizer-terminology).

The algebraic-group and unipotence predicates and the scalar-extension and torus
constructions are the previously recorded ones. Centralizing is tested after every
algebra extension, without a reducedness assumption.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.ReductiveTorusCentralizer

/-- A maximal torus is a closed torus inclusion with no strictly larger torus subgroup.
Source: Milne, Chapter 17, Proposition 17.61(a), p.372
(blueprint: def-sfb-reductive-torus-centralizer-terminology). -/
def IsMaximalTorus {k : Type u} [Field k] {T G : Grp (Over (Spec (.of k)))}
    (i : T ⟶ G) : Prop :=
  IsClosedSubgroupScheme i.hom.hom ∧ MultiplicativeType.IsTorus T ∧
    ∀ (S : Grp (Over (Spec (.of k)))) (j : S ⟶ G),
      IsClosedSubgroupScheme j.hom.hom → MultiplicativeType.IsTorus S →
        ∀ f : T ⟶ S, f ≫ j = i → IsIso f

/-- Reductivity means smooth affine finite type, geometric connectedness, and no
nontrivial smooth connected normal unipotent subgroup after algebraic closure.
Source: Milne, Chapter 17, reductive-group convention and Proposition 17.61, p.372
(blueprint: def-sfb-reductive-torus-centralizer-terminology). -/
def IsReductive {k : Type u} [Field k] (G : Grp (Over (Spec (.of k)))) : Prop :=
  SolvableGroupStructure.IsAlgebraic G ∧ Smooth G.X.hom ∧
    ConnectedSpace ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G).X.left ∧
    ∀ (U : Grp (Over (Spec (.of (AlgebraicClosure k)))))
      (j : U ⟶ (MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G),
      SolvableGroupStructure.IsAlgebraic U → IsClosedSubgroupScheme j.hom.hom →
        IsNormalSubgroupScheme j.hom.hom → ConnectedSpace U.X.left →
          SolvableGroupStructure.IsUnipotent U → Nonempty (U ≅ Grp.trivial _)

/-- The scheme-theoretic centralizer condition on A-points: after every A-algebra
extension, the extended point commutes with every point of the subgroup.
Source: Milne, Proposition 1.92, pp.33--34
(blueprint: def-sfb-reductive-torus-centralizer-terminology). -/
def centralizerPoints {k : Type u} [Field k] {T G : Grp (Over (Spec (.of k)))}
    (i : T ⟶ G) (A : Type u) [CommRing A] [Algebra k A] :
    Set (StandardGroupSchemes.affine k A ⟶ G.X) :=
  {g | ∀ (B : Type u) [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (t : StandardGroupSchemes.affine k B ⟶ T.X),
      Commute (StandardGroupSchemes.map k f ≫ g) (t ≫ i.hom.hom)}

end AlgebraicGeometry.ReductiveTorusCentralizer
