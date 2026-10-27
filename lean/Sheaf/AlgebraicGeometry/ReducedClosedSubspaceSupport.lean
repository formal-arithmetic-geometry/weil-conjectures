module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.EtaleAtlasPresentation
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
import Sheaf.AlgebraicGeometry.InvariantClosedSubstackDescent
import Sheaf.AlgebraicGeometry.EtaleSheafSpaceAtlasBootstrap
import Sheaf.AlgebraicGeometry.SpaceSmoothReducedLocality

/-!
# Reduced closed subspaces and support after base change

Source: Stacks Project, Properties of Spaces, Tags 03IQ (lemma-reduced-closed-subspace),
03H4 (lemma-points-cartesian), 0ABJ (lemma-subspace-induced-topology), and Spaces,
Tag 02YW (lemma-base-change-immersions)
(blueprint: lem-sfb-space-reduced-closed-support).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every closed subset carries a unique reduced closed subspace structure. Its arbitrary
base changes are closed immersions whose canonical point maps identify their point spaces
homeomorphically with the inverse image of the given subset.

Source: Stacks Project, Tags 03IQ, 03H4, 0ABJ and 02YW
(blueprint: lem-sfb-space-reduced-closed-support).

Proof:
1. Choose a surjective etale scheme atlas U -> X. Its scheme relation R = U times_X U
has etale surjective projections s,t (lem-a1-etale-atlas-presentation). Continuity of
point maps makes T_U the closed inverse image of T, and ps = pt gives equal inverse
images of T_U under s and t (lem-a1-space-point-open-calculus).
2. Give T_U its reduced closed scheme structure D
(lem-weil-pbc-reduced-induced-closed-subscheme). Its two closed pullbacks to R are
etale over D, hence reduced (etale-proposition-etale-reduced and
lem-trf-space-representable-etale-scheme-tests). Their supports agree by step 1, so
uniqueness of the reduced induced scheme structure identifies them as closed subschemes.
3. Regard X as a discrete etale stack. Its representable diagonal and etale atlas make
it an algebraic stack, since etale maps are smooth
(lem-weil-pbc-etale-smooth-zero-dimensional-fibres). Invariant closed-substack descent
(lem-sfb-invariant-closed-substack-descent) descends D to a closed subfunctor F of X.
4. For a scheme V -> F, its pullback of D is V times_X U, a surjective etale scheme
cover of V. Thus lem-sfb-etale-sheaf-space-atlas-bootstrap makes F an algebraic space
Z, closed in X. Its atlas D -> Z makes Z reduced by
lem-sfb-space-smooth-reduced-locality, and its point image is T by
lem-a1-space-point-open-calculus.
5. Any other reduced closed subspace pulls back to a reduced closed subscheme of U
with support T_U, hence equals D there. Injectivity of invariant closed-substack descent
identifies it with Z as a subfunctor, equivalently as a subobject of X.
6. The sheaf pullback P = Z times_X W is an algebraic space by
lem-trf-space-fibre-products-etale-covers. Every scheme test of P -> W is a scheme test
of Z -> X, hence a closed immersion. No reducedness of P is needed.
7. Point lifting in fibre products (lem-a1-space-point-open-calculus) identifies the
image of P -> W with the inverse image of T. Pull back to a scheme atlas V -> W.
The scheme closed immersion P times_W V -> V is injective on points. Lifting two points
above the same point of W to a common point of V proves injectivity of P -> W.
8. For a closed subset C of P, its inverse image C_V is closed and its image in V is
closed under the scheme closed immersion. Point lifting identifies this image with the
inverse image in V of the image of C in W. The atlas point map is open and surjective,
so closedness is detected after this inverse image. Hence P -> W is closed on points.
Together with continuity and step 7 this gives the homeomorphism onto the inverse image.
-/
theorem exists_unique_reduced_closed_subspace {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Set (Point X.obj.obj)) (hT : IsClosed T) :
    ∃ C : ClosedSubspace X,
      IsReduced (C.val : AlgebraicSpace S) ∧
      pointImage C.val.arrow.hom.hom = T ∧
      (∀ D : ClosedSubspace X, IsReduced (D.val : AlgebraicSpace S) →
        pointImage D.val.arrow.hom.hom = T → D = C) ∧
      ∀ (W : AlgebraicSpace S) (q : W ⟶ X),
        IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
          (Limits.pullback.snd C.val.arrow.hom q.hom).hom ∧
        ∃ e : Point (Limits.pullback C.val.arrow.hom q.hom).obj ≃ₜ
            {w : Point W.obj.obj | mapPoint q.hom.hom w ∈ T},
          ∀ z : Point (Limits.pullback C.val.arrow.hom q.hom).obj,
            (e z).val = mapPoint (Limits.pullback.snd C.val.arrow.hom q.hom).hom z := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
