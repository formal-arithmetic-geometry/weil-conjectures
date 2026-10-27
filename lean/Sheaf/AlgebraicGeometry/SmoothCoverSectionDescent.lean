module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Sections descend along smooth scheme covers of algebraic stacks

Source: Stacks Project, stacks-sheaves.tex, Tags 076S and 06WV(1), with the
big-fppf compatible-family convention of Tags 06TP and 06TR
(blueprint: lem-sfb-smooth-cover-section-descent).

Chart sections are literal precomposition restrictions. Compatibility is tested on
all objects of the recorded 2-fibre product, including all its comparison isomorphisms.
This computes equality on the relation algebraic space without choosing a presentation.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open AlgebraicGeometry CategoryTheory Opposite

namespace CategoryTheory

/-- Sections on a scheme chart are compatible families on all its scheme tests.
Source: Stacks Tags 06TP, 06TR, and 076S
(blueprint: lem-sfb-smooth-cover-section-descent). -/
abbrev moduliChartSections {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    {U : Over S} (p : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (A : Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w}) :=
  RingCat.sectionsSubring (p.toFunctor.op ⋙ A.obj ⋙ forget₂ CommRingCat RingCat)

/-- The compatible-family subring. On a relation test `x`, its comparison arrow
identifies the two pullbacks; every such arrow is included, also when `i = j`.
Source: Stacks Tags 076S and 06WV(1)
(blueprint: lem-sfb-smooth-cover-section-descent). -/
def moduliCompatibleChartSections {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {I : Type t} {U : I → Over S}
    (p : ∀ i : I, BasedFunctor (discreteModuli (yoneda.obj (U i))) F)
    (A : Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w}) :
    Subring (∀ i : I, moduliChartSections (p i) A) where
  carrier := {c | ∀ (i j : I) (x : (moduliTwoFiberProduct (p i) (p j)).obj),
    A.obj.map x.obj.hom.op ((c j).val (op x.obj.right)) =
      (c i).val (op x.obj.left)}
  one_mem' := by intro i j x; exact (A.obj.map x.obj.hom.op).hom.map_one
  mul_mem' := by
    intro a b ha hb i j x
    change A.obj.map x.obj.hom.op
      ((a j).val (op x.obj.right) * (b j).val (op x.obj.right)) = _
    rw [map_mul, ha i j x, hb i j x]
    rfl
  zero_mem' := by intro i j x; exact (A.obj.map x.obj.hom.op).hom.map_zero
  add_mem' := by
    intro a b ha hb i j x
    change A.obj.map x.obj.hom.op
      ((a j).val (op x.obj.right) + (b j).val (op x.obj.right)) = _
    rw [map_add, ha i j x, hb i j x]
    rfl
  neg_mem' := by
    intro a ha i j x
    change A.obj.map x.obj.hom.op (-(a j).val (op x.obj.right)) = _
    rw [map_neg, ha i j x]
    rfl

/-- Pullback gives the unique ring isomorphism to compatible chart sections.
Its component formula specifies the canonical restriction, and hence its naturality
in the algebra: every algebra-sheaf morphism commutes with both sides objectwise.
No chart or relation space is assumed affine or quasi-compact.
Source: Stacks Tags 076S and 06WV(1), with Tags 06TP and 06TR
(blueprint: lem-sfb-smooth-cover-section-descent).

Proof:
1. Interpret sections by the compatible-family convention of
   def-sfb-stack-quasi-coherent-algebra. Each object of the 2-fibre product in
   def-sfb-stable-pointed-moduli-groupoids gives a scheme test of the relation
   space and its specified comparison isomorphism. Thus the displayed compatibility
   is exactly equality of the two restrictions, including automorphisms.
2. For any object over T, represent each base change of a chart by an algebraic
   space. By lem-sfb-stack-smooth-permanence its projection is smooth. Choose
   surjective etale scheme charts using def-trf-algebraic-space. The hypotheses
   make their composites jointly surjective and smooth. By lem-pc-smooth-flat
   they are flat and locally of finite presentation, hence form the fppf covering
   of def-pc-fppf-site. No finite subcover is used.
3. Restrict the given chart sections to this cover. Their overlap agreement is
   step 1. The sheaf equalizer of def-weil-pbc-sites-and-cohomology glues a unique
   section. Common covering refinements show independence of every choice.
4. Pulling this construction back along any arrow gives the same local sections,
   so uniqueness gives compatibility along that arrow. The resulting global
   family restricts to the prescribed chart sections, by comparison with identity
   covers. This proves existence.
5. Two global families with the same chart restrictions agree on the covers of
   step 2 and therefore everywhere by the separated part of the sheaf condition.
   Restrictions preserve all ring operations, giving the normalized ring
   isomorphism. The normalization makes the isomorphism unique and natural in
   algebra maps. For an empty index set, joint surjectivity forces all test
   schemes with objects to be empty, where the empty fppf cover forces a unique
   section. Thus this case gives the one-element ring on both sides as well. -/
theorem smoothCover_section_descent
    (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F)
    (A : ModuliAlgebraSheaf F hF.1.1) (hA : IsQuasicoherentModuliAlgebra A)
    (I : Type t) (U : I → Over (Spec (.of k)))
    (p : ∀ i : I, BasedFunctor (discreteModuli (yoneda.obj (U i))) F)
    (hsmooth : ∀ (i : I) (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
      ∃ (Z : AlgebraicSpace (Spec (.of k))) (q : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange (p i) T t Z q ∧ SpaceMapIsSmooth Z T q)
    (hcover : ∀ (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) F) (x : T.left),
      ∃ (i : I) (Z : AlgebraicSpace (Spec (.of k))) (q : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange (p i) T t Z q ∧
          ∃ (V : Over (Spec (.of k))) (b : yoneda.obj V ⟶ Z.obj.obj),
            AlgebraicSpace.IsEtale b ∧ ∃ y : V.left, (yoneda.preimage (b ≫ q)).left y = x) :
    ∃! e : moduliGlobalSectionsRing A.right ≃+* moduliCompatibleChartSections p A.right,
      ∀ (s : moduliGlobalSectionsRing A.right) (i : I)
        (x : (discreteModuli (yoneda.obj (U i))).obj),
        ((e s).val i).val (op x) = s.val (op ((p i).obj x)) := by
  sorry

end CategoryTheory
