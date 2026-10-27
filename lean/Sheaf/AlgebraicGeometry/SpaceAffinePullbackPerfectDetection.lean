module

public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Affine pullbacks of perfect objects detect isomorphisms

Source: Stacks Project, Derived Categories of Spaces, Tags 09IY and 0E4R,
affine case (blueprint: lem-sfb-space-affine-pullback-perfect-detection).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w w'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Perfect tests pulled back along an affine morphism detect every isomorphism in
unbounded D_QCoh. The displayed function is postcomposition by the shifted morphism.
Source: Stacks, Tags 09IY and 0E4R, affine case
(blueprint: lem-sfb-space-affine-pullback-perfect-detection).

Proof:
1. Choose the perfect weak generator on Z from lem-sfb-space-perfect-weak-generator.
   Complete v to a distinguished triangle C -> D -> K -> C[1]. Its cone has
   quasi-coherent cohomology by lem-sfb-space-perfect-localizing-generation.
2. For each n test on P[n], which is again perfect, with j=0,1. Surjectivity at zero
   and injectivity at one imply Hom(Lh*(P[n]),K)=0: for t into K the boundary bt
   vanishes by injectivity; triangle exactness lifts t to s into D; surjectivity
   lifts s through v, and the consecutive triangle composite is zero. This uses
   lem-weil-pbc-hom-into-triangle-exact and requires no boundedness.
3. By the adjunction in lem-sfb-space-derived-etale-chart-calculus the vanishing is
   Hom(P[n],Rh_*K)=0. Affine pushforward preserves quasi-coherent cohomology and
   reflects isomorphisms by lem-sfb-space-affine-derived-pushforward-conservative.
   Weak generation gives Rh_*K=0. Apply conservativity to the zero endomorphism of
   K to deduce that it is invertible, hence id_K=0 and K is zero.
4. Exactness for this triangle and its rotation makes Hom(W,v) bijective for every W.
   With W=D obtain a right inverse r. With W=C injectivity gives rv=id_C, so r is
   an inverse. These are precisely the exactness clauses of
   lem-weil-pbc-hom-into-triangle-exact. -/
theorem affinePullbackPerfect_detectsIso
    {S : Scheme.{u}} {Z' Z : AlgebraicSpace S} (h : Z' ⟶ Z)
    (haffine : MapIsAffine h)
    (hqc' : CompactSpace (Point Z'.obj.obj))
    (hqs' : ∀ (U V : Over S) (a : yoneda.obj U ⟶ Z'.obj.obj)
      (b : yoneda.obj V ⟶ Z'.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (hqc : CompactSpace (Point Z.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ Z.obj.obj)
      (b : yoneda.obj V ⟶ Z.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    [HasDerivedCategory.{w'} Z'.SmallModules] [HasDerivedCategory.{w} Z.SmallModules]
    {C D : Z'.DerivedQCoh} (v : C ⟶ D)
    (htest : ∀ (P : Z.DerivedQCoh),
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u}
        Z.smallStructureSheaf P.obj →
      ∀ j : ℤ, Function.Bijective
        (fun a : (derivedTensorPullback h).obj P.obj ⟶ C.obj⟦j⟧ ↦
          a ≫ (shiftFunctor Z'.DerivedModules j).map v.hom)) :
    IsIso v := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
