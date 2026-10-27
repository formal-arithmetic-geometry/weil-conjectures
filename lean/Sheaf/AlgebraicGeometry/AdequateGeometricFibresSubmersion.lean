/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Sheaf.AlgebraicGeometry.ModuliSchemeBaseChange
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Topology and geometric fibres of an adequate moduli space

Source: Alper, arXiv:1005.2398v3, Section 2 and Theorem 5.3.1(3),(5), pp. 29--30
(blueprint: lem-sfb-adequate-geometric-fibres-submersion).

Geometric closures are taken after the actual change of base to the specified field.
The diagonal hypotheses are tested on algebraic-space presentations of their scheme
base changes, including the projection, quasi-compactness and separatedness.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry Opposite

namespace CategoryTheory

/-- The point of the scalar extension represented by a specified field-valued object.
The scalar extension retains the object, the identity scheme over the field, and the
canonical isomorphism of their bases. No object or map is chosen.
Source: Alper, Theorem 5.3.1(5); Stacks, Tags 003R and 04XG
(blueprint: lem-sfb-adequate-geometric-fibres-submersion). -/
def moduliScalarPoint {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (Ω : Type u) [Field Ω] (g : Spec (.of Ω) ⟶ S)
    (x : Functor.Fiber F.p (Over.mk g)) : ModuliPoints (moduliSchemeBaseChange F g) :=
  Quot.mk _ ⟨⟨⟨x.val, Over.mk (𝟙 (Spec (.of Ω))),
    eqToHom (x.property.trans (by
      change Over.mk g = Over.mk (𝟙 _ ≫ g)
      rw [Category.id_comp]))⟩, inferInstance⟩,
    ⟨Ω, inferInstance, ⟨Iso.refl _⟩⟩⟩

/-- Universal submersiveness and the same-field classification by intersecting closures.
Source: Alper, arXiv:1005.2398v3, Section 2 and Theorem 5.3.1(3),(5), pp. 29--30
(blueprint: lem-sfb-adequate-geometric-fibres-submersion).

Proof:
1. For every algebraic-space base change use
lem-sfb-adequate-moduli-universally-submersive. It gives surjectivity and reflection
of open subsets without any hypothesis on the diagonal of the new base. The closed
surjection argument is supplied by lem-sfb-adequate-moduli-topological-images.
2. A field extension is flat: vector spaces are free and flat
(lem-weil-pbc-module-over-field-flat), and tensor with a flat module is exact
(lem-weil-pbc-flat-tensor-exact). Apply lem-sfb-adequate-flat-base-change to scalar
extension. The diagonal hypotheses are preserved, and the iso-comma description
identifies its field objects with the original objects over this very field.
3. The fibre over a rational point is nonempty by step 1 and quasi-compact by
adequacy (def-sfb-stack-qcqs-morphism). Its diagonal is quasi-compact and separated,
and its point map is universally closed by lem-sfb-adequate-moduli-topological-images.
Apply lem-sfb-universally-closed-stack-rational-point to get an object over the same
algebraically closed field. Passing to isomorphism classes gives surjectivity.
4. By lem-sfb-smooth-presentation-closed-subsets the two closures have reduced closed
substack structures. By lem-sfb-qs-space-rational-point-topology their image points
are closed and rational points inject into the point space. Continuity puts each
closure over its one image point. The intersection-of-images formula of
lem-sfb-adequate-moduli-topological-images gives nonempty intersection when the images
agree; the pointwise base-change assertion of the smooth-presentation lemma identifies
the substack intersection with the intersection of its supports. Conversely any point
in both closures maps to both rational image points, so those rational points agree. -/
theorem adequate_geometricFibres_submersion (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F) (Y : AlgebraicSpace (Spec (.of k)))
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (hφ : IsAdequateModuliSpace F hF Y φ)
    (hFdiag : ∀ (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T))
        (moduliTwoFiberProduct (moduliBaseStructure F) (moduliBaseStructure F))),
      ∃ (Z : AlgebraicSpace (Spec (.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange (moduliRelativeDiagonal (moduliBaseStructure F)) T t Z p ∧
          AlgebraicSpace.MapIsQuasiCompact p ∧ AlgebraicSpace.MapToSchemeIsSeparated Z T p)
    (hYdiag : ∀ (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T))
        (moduliTwoFiberProduct (moduliBaseStructure (discreteModuli Y.obj.obj))
          (moduliBaseStructure (discreteModuli Y.obj.obj)))),
      ∃ (Z : AlgebraicSpace (Spec (.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange
          (moduliRelativeDiagonal (moduliBaseStructure (discreteModuli Y.obj.obj))) T t Z p ∧
          AlgebraicSpace.MapIsQuasiCompact p ∧ AlgebraicSpace.MapToSchemeIsSeparated Z T p) :
    (∀ (Y' : AlgebraicSpace (Spec (.of k))) (g : Y' ⟶ Y),
      Function.Surjective
        (moduliPointMap (moduliTwoFiberSnd φ (discreteModuliMap g.hom.hom))) ∧
      ∀ V : Set (ModuliPoints (discreteModuli Y'.obj.obj)),
        IsOpen V ↔ IsOpen
          (moduliPointMap (moduliTwoFiberSnd φ (discreteModuliMap g.hom.hom)) ⁻¹' V)) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of k)),
      Function.Surjective ((moduliFiberMap φ (Over.mk g)).mapSkeleton.obj) ∧
      ∀ x₁ x₂ : Functor.Fiber F.p (Over.mk g),
        Nonempty ((moduliFiberMap φ (Over.mk g)).obj x₁ ≅
          (moduliFiberMap φ (Over.mk g)).obj x₂) ↔
        (closure ({moduliScalarPoint F Ω g x₁}) ∩
          closure ({moduliScalarPoint F Ω g x₂})).Nonempty := by
  sorry

end CategoryTheory
