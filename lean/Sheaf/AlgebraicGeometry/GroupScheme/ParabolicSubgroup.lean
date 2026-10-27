module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.Topology.Connected.Basic

/-! # Rational parabolic subgroups and their fppf coset sheaves

Source: Milne, Algebraic Groups (2017), Chapter 25(a), pp.544--546, and
Definition 5.20, pp.104--105 (blueprint: def-sfb-parabolic-subgroup).

The coequalizer identifies g and gp on every test scheme. Its fppf sheafification
restricts on affine tests to the sheafification of A ↦ G(A)/P(A). Affine schemes
form a basis of the big fppf site. Lifted Yoneda values allow sheafification in
the size universe of the site without changing its points or equivalence relation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The fppf right-coset sheaf of a group-scheme homomorphism i : P → G.
It is constructed by sheafifying the pointwise coequalizer of (g,p) ↦ g and
(g,p) ↦ g i(p), without choosing a representing scheme.
Source: Milne, Definition 5.20 and Proposition 5.25, pp.104--105
(blueprint: def-sfb-parabolic-subgroup). -/
noncomputable def fppfRightCosetSheaf {k : Type u} [Field k]
    {P G : Grp (Over (Spec (.of k)))} (i : P ⟶ G) :
    Sheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).obj
    (coequalizer (uliftYoneda.{u + 1}.map (fst G.X P.X))
      (uliftYoneda.{u + 1}.map (fst G.X P.X * (snd G.X P.X ≫ i.hom.hom))))

/-- A rational parabolic is a smooth geometrically connected closed subgroup whose
fppf right-coset sheaf is represented by a proper finite-type scheme over k.
Geometric connectedness is tested over an algebraic closure. Representability
is an isomorphism of the sheaf's underlying presheaf with lifted Yoneda.
Source: Milne, Chapter 25(a), pp.544--546, and Definition 17.15, p.356
(blueprint: def-sfb-parabolic-subgroup). -/
def IsParabolicSubgroup {k : Type u} [Field k]
    {P G : Grp (Over (Spec (.of k)))} (i : P ⟶ G) : Prop :=
  IsClosedImmersion i.hom.hom.left ∧ Smooth P.X.hom ∧
    ConnectedSpace ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj P).X.left ∧
    ∃ X : Over (Spec (.of k)),
      IsProper X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
        Nonempty ((fppfRightCosetSheaf i).obj ≅ uliftYoneda.{u + 1}.obj X)

/-- A minimal rational parabolic contains no strictly smaller rational parabolic.
The factorization condition compares subgroups of the same ambient group;
minimality alone does not assert that the subgroup is proper.
Source: Milne, Chapter 25(a), Theorem 25.8, p.546
(blueprint: def-sfb-parabolic-subgroup). -/
def IsMinimalParabolicSubgroup {k : Type u} [Field k]
    {P G : Grp (Over (Spec (.of k)))} (i : P ⟶ G) : Prop :=
  IsParabolicSubgroup i ∧
    ∀ (Q : Grp (Over (Spec (.of k)))) (j : Q ⟶ G), IsParabolicSubgroup j →
      ∀ f : Q ⟶ P, f ≫ i = j → IsIso f

end AlgebraicGeometry
