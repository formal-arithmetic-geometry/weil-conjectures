module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets

/-! # Topological images under adequate moduli spaces

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
arXiv:1005.2398v3, Theorem 5.3.1(1), (2), (4), printed pp. 29--30
(blueprint: lem-sfb-adequate-moduli-topological-images).

Point spaces and their topologies use the field-object quotient and the smooth-atlas
topology of `smooth_presentation_closed_subsets`, also for discrete algebraic spaces.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- An adequate moduli map is surjective, is closed after every algebraic-space base
change, and preserves intersections of images of closed substacks.
Source: Alper, arXiv:1005.2398v3, Theorem 5.3.1(1), (2), (4), printed pp. 29--30
(blueprint: lem-sfb-adequate-moduli-topological-images).

Proof:
1. Apply lem-sfb-adequate-moduli-universal-closed-topology over a surjective etale
scheme atlas of Y. Lift a point first to the atlas and then to the pulled-back stack
to obtain surjectivity. For a space T over Y, choose an etale scheme atlas W of T.
All 2-fibre products are algebraic by lem-sfb-algebraic-stack-fibre-products. A closed
subset D of the pullback stack is the support of its reduced closed substack by
lem-sfb-smooth-presentation-closed-subsets. That lemma's base-change image assertion
identifies the inverse image in W of the image of D with the image of its pullback.
The scheme assertion makes this closed; the atlas quotient topology descends closedness
to T. Continuity follows from the same smooth-presentation topology theorem.
2. Put Z = Z1 ×_X Z2 and C = phi(|Z|), closed by Step 1. The two projections give
C contained in the intersection of images. For y outside C take an affine etale
neighbourhood U of a lift of y inside Y minus C. The two pulled-back closed substacks
are disjoint on points by lem-sfb-smooth-presentation-closed-subsets. Apply
lem-sfb-disjoint-closed-substacks-algebra-quotient to obtain the surjection from the
structure algebra to the product of their two quotient algebras.
3. The power-lifting condition of def-sfb-adequate-moduli-space lifts a positive power
of (0,1), hence (0,1) itself, to a global function on X_U. The structure-sheaf isomorphism,
with the direct-image convention of def-sfb-stack-quasi-coherent-algebra, identifies
this function with a function a on U. If y lay in both images, base-change of images
would put its lift u in both images over U. Evaluate on field-valued representatives
above u. Injectivity of the residue-field embeddings would give a(u) = 0 and a(u) = 1
in the same field. This contradiction proves the reverse inclusion. -/
theorem adequate_moduli_topological_images (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F)
    (Y : AlgebraicSpace (Spec (.of k)))
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (hφ : IsAdequateModuliSpace F hF Y φ) :
    Function.Surjective (moduliPointMap φ) ∧
    (∀ (T : AlgebraicSpace (Spec (.of k))) (t : T ⟶ Y),
      @Continuous _ _
        (moduliSmoothPointTopology (moduliTwoFiberProduct φ (discreteModuliMap t.hom.hom)))
        (moduliSmoothPointTopology (discreteModuli T.obj.obj))
        (moduliPointMap (moduliTwoFiberSnd φ (discreteModuliMap t.hom.hom))) ∧
      @IsClosedMap _ _
        (moduliSmoothPointTopology (moduliTwoFiberProduct φ (discreteModuliMap t.hom.hom)))
        (moduliSmoothPointTopology (discreteModuli T.obj.obj))
        (moduliPointMap (moduliTwoFiberSnd φ (discreteModuliMap t.hom.hom)))) ∧
    (∀ Z₁ Z₂ : ClosedModuliSubstack F,
      (moduliPointMap φ '' Set.range (moduliPointMap Z₁.inclusion)) ∩
          (moduliPointMap φ '' Set.range (moduliPointMap Z₂.inclusion)) =
        moduliPointMap φ '' Set.range (moduliPointMap
          ((moduliTwoFiberFst Z₁.inclusion Z₂.inclusion).comp Z₁.inclusion))) := by
  sorry

end CategoryTheory
