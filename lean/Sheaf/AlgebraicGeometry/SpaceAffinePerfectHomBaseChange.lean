module

public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentRHomQuasiCoherent
import Sheaf.AlgebraicGeometry.SmallEnlargedEtaleModules
import Sheaf.SixFunctors.RingedPerfectInternalHomPullback
import WeilConjectures.AlgebraicGeometry.MixedExtensionSectionsUnit
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Flat affine base change of global Hom from a perfect algebraic-space complex

Source: Stacks Project, spaces-perfect.tex, Tag 0E4S, case (1), with flat f.
(blueprint: lem-sfb-space-affine-perfect-hom-base-change)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Flat affine base change for the canonical global-Hom arrow, including its unit
normalization. It is natural in both variables because the arrow is the component of
spaceAffineHomBaseChangeNat. The input Q is an arbitrary unbounded D_QCoh object.

Source: Stacks Project, Derived Categories of Spaces, Tag 0E4S, case (1)
(blueprint: lem-sfb-space-affine-perfect-hom-base-change).

Proof:
1. Put E = RHom(P,Q). Perfectness of P and quasi-coherence of Q imply that E has
quasi-coherent cohomology. Since X is qcqs and the target is affine, f is qcqs.
2. The internal Hom pullback comparison, defined as the transpose of pulled evaluation,
is invertible for perfect P. Work on the canonical enlarged ringed sites and compute on
bounded finite-projective representatives of P; no bound on Q is required.
3. Flatness of f makes the square Tor independent. Apply flat derived pushforward base
change to E. The result Rf_*E has quasi-coherent cohomology. On affine targets, derived
étale/Zariski comparison and affine derived realization identify pullback with derived
extension of scalars, with the scalar-one unit formula. Derived sections/direct-image
composition then gives an isomorphism from RHom(P,Q) tensor_A^L B to the derived sections
of Lh*E. Postcompose with sections of the internal Hom comparison from step 2.
4. To identify this iso with the stated arrow, transpose by scalar extension/restriction.
Substitute the counit-mate formula for pushforward base change. Naturality moves the
f-unit past the g-unit, and the adjacent f-unit/counit cancel by the triangle identity.
What remains is the h-unit followed by derived sections composition and the transpose
of pulled evaluation. This is spaceGlobalHomPullback. The scalar adjunction uniquely
identifies its B-linear extension with spaceAffineHomBaseChangeNat. The scalar-unit
identity follows from homEquiv and its inverse. All constructions are natural in both
arguments. Empty spaces, zero complexes, identity base change, nonflat A to B, and
negative degrees require no additional hypotheses. -/
theorem spaceAffinePerfectHomBaseChange
    {S : Scheme.{u}} [∀ Z : AlgebraicSpace S, HasDerivedCategory.{w} Z.SmallModules]
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (hp : IsPullback h.hom f'.hom f.hom ((Scheme.fppfTopology.over S).yoneda.map g))
    (hflat : MapIsFlat f)
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (P Q : X.DerivedQCoh)
    (hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf P.obj) :
    IsIso ((spaceAffineHomBaseChangeNat e e' g f h f'
      (ObjectProperty.hom_ext _ hp.w)).app (op P.obj, Q.obj)) ∧
    (Adjunction.ofIsRightAdjoint
      (RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g))).unit.app
        ((spaceGlobalHom Y e f).obj (op P.obj, Q.obj)) ≫
      (RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g)).map
        ((spaceAffineHomBaseChangeNat e e' g f h f'
          (ObjectProperty.hom_ext _ hp.w)).app (op P.obj, Q.obj)) =
      spaceGlobalHomPullback e e' g f h f' (ObjectProperty.hom_ext _ hp.w) P.obj Q.obj := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
