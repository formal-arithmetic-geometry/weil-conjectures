module

public import Sheaf.CategoryTheory.DgAlgebraHomotopyStructure
public import Sheaf.CategoryTheory.DgGoodCharacterEmbedding
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

import Sheaf.CategoryTheory.DgCompositeConeContraction
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Triangulation and admissible triangles in the DG derived category

Source: Stacks Project, dga.tex, Tags 09KJ, 09K8, 09K6, 09KW, 09KX and 09KF
(blueprint: lem-sfb-dg-derived-admissible-triangles).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.DgAlgebra

/-- The asserted standard triangulation on the actual DG localization, together
with its exact homotopy localization and admissible triangles. The two imported
structure types fix shifts by their underlying signed complexes and fix distinguished
triangles by their iff with the signed DG cones. The comparison identifies the
localization of the homotopy quotient with the specified Gabriel--Zisman localization.
The first two arrows in `admissible` are literally the images of the given maps.
The localization shift comparison is pinned by `shiftComparison`, using the given
shift comparisons and `factorIso`. The coproducts bundled in `DerivedStructure`
are those of Stacks Tag 09QI, lemma-derived-products.
Source: Stacks, dga.tex, Tags 09KJ, 09K8, 09KW and 09KX
(blueprint: lem-sfb-dg-derived-admissible-triangles). -/
structure DerivedAdmissibleTriangles (A : Algebra.{u}) where
  [homotopy : HomotopyStructure A]
  [derived : DerivedStructure A]
  localization : HomotopyCategory A ⥤ Derived A
  factorIso : homotopyQuotient A ⋙ localization ≅ Q A
  [isLocalization : localization.IsLocalization
    (fun _ _ f ↦ ∀ n : ℤ, IsIso ((HomotopyStructure.cohomology n).map f))]
  [commShift : localization.CommShift ℤ]
  shiftComparison (n : ℤ) (M S : RightModule A) (e : ShiftComparison A n M S) :
    (localization.commShiftIso n).hom.app ((homotopyQuotient A).obj M) =
      localization.map (HomotopyStructure.shiftIso n M S e).inv ≫
        factorIso.hom.app S ≫ (DerivedStructure.shiftIso n M S e).hom ≫
          (factorIso.inv.app M)⟦n⟧'
  [exact : localization.IsTriangulated]
  admissible (K L M : RightModule A) (S : GradedSplitShortExact A K L M) :
    ∃ δ : (Q A).obj M ⟶ ((Q A).obj K)⟦(1 : ℤ)⟧,
      Triangle.mk ((Q A).map S.inclusion) ((Q A).map S.projection) δ ∈
        distTriang (Derived A)

/-- Every associative unital DG algebra over the integers has the standard
triangulated derived category, its homotopy localization is exact, and every
short exact sequence split on graded right modules gives a distinguished triangle.
Source: Stacks, dga.tex, Tags 09KJ, 09K8, 09K6, 09KW, 09KX and 09KF
(blueprint: lem-sfb-dg-derived-admissible-triangles).

Proof plan, following the seven steps of the node:
1. DG maps modulo right A-linear degree-minus-one homotopies form an additive
category with zero and finite sums. Shifts change differentials and homotopies by
(-1)^k, retaining the right action. The cone has differential (dy+fx,-dx).
The identity cone contracts by h(y,x)=(0,y), proving TR1.
2. Apply lem-sfb-dg-cone-rotation to identify both rotations with standard cones.
Their last arrow is -f[1], giving TR2 with its required sign.
3. A square bf-f'a=dh+hd gives the cone map (y,x) maps to (by+hx,ax).
The homotopy equation is precisely its upper-right chain-map equation; all three
triangle squares follow. Conjugating by cone comparisons gives TR3.
4. Lem-sfb-dg-composite-cone-contraction gives the distinguished triangle on
C(f),C(gf),C(g), with maps (gy,x), (z,fx), (-y,0). The four octahedral squares
hold by substitution. Lem-sf-triangle-morphism-iso identifies arbitrary prescribed
cones with these standard cones, and conjugation gives their octahedron: TR4.
5. Homotopic maps induce equal cohomology maps. Forgetting to complexes of
abelian groups, apply lem-weil-pbc-complex-ses-homology-long-exact to the split
cone sequence. Its connecting map is H(f), so the cone is acyclic iff f is a
quasi-isomorphism. Acyclics are replete, shift-stable and closed under triangles.
6. Lem-trf-triangulated-subcategory-cone-system gives the multiplicative cone
class and both fraction calculi. It is precisely the quasi-isomorphisms by step 5.
Lem-pur-localization-triangles-05r6 triangulates its localization and makes the
homotopy localization exact. Its distinguished triangles are exactly localized
signed cone triangles. The explicit universe u bounds components; the formal
localization is formed in the larger universe, as def-weil-size-convention permits.
The shift comparison is induced by the specified DG shifts and factorization
isomorphism, giving the equation in shiftComparison. The coproducts bundled in
DerivedStructure are supplied by Stacks Tag 09QI (lemma-derived-products): the
Hom universal property follows by computing maps into a K-injective resolution,
where maps from a direct sum are a product of the individual Hom groups.
7. Choose graded splittings s and r with vs=1, ri=1, ir+sv=1 and rs=0.
Put delta=r d_L s. Its Leibniz cross-term vanishes by rs=0; d squared zero
makes it a DG map M to K[1]. On C(i), q(l,k)=v(l), t(m)=(s(m),-delta(m))
satisfy qt=1 and 1-tq=dH+Hd with H(l,k)=(0,r(l)). These maps and H are
right A-linear. The identities qi_i=v and (-p_i)t=delta give the triangle
isomorphism (1,1,q) in the homotopy category. Exact localization gives the
asserted distinguished triangle with first arrows Q(i),Q(v). No differential
compatibility of r or s is used. -/
theorem nonempty_derivedAdmissibleTriangles (A : Algebra.{u}) :
    Nonempty (DerivedAdmissibleTriangles A) := by
  sorry

end CategoryTheory.DgAlgebra
