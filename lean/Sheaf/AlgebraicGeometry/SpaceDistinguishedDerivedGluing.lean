module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.ElementaryEtaleShriekExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Localization.Adjunction

/-! # Derived gluing along an elementary distinguished square

Source: Stacks Project, spaces-perfect.tex, Tags 08HB (lemma-glue), both assertions,
and 08GN (lemma-make-more-elementary-distinguished-squares), clause (2)
(blueprint: lem-sfb-space-distinguished-derived-gluing).

The equivalent small affine ringed models retain the original structure-sheaf module
universe. All restrictions below use the shared canonical total derived tensor pullback;
the overlap comparison is the tensor-normalized comparison for the cartesian square.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Arbitrary base change preserves an elementary distinguished square, with the reduced
complement formed after base change. Unbounded derived modules and compatible maps to a
fixed derived module glue along that square, with the prescribed overlap isomorphism.
There are no quasi-coherence, boundedness, perfectness or quasi-compactness assumptions.

Source: Stacks Project, spaces-perfect.tex, Tags 08HB and 08GN(2)
(blueprint: lem-sfb-space-distinguished-derived-gluing).

Proof:
1. Pull back the closed complement and then reduce it. Its radical ideal on each etale
scheme atlas defines the reduced complement of the pulled-back open. The isomorphism
above the original complement pulls back to this reduction. Open immersions and etale
maps are stable under arbitrary base change (lem-sfb-space-reduced-closed-support,
def-a1-space-open-subspace and lem-trf-space-chartwise-etale-permanence).
2. Rename the resulting square U -> X <- V, with overlap T and maps j,p,q,k. Exact
etale restriction is triangulated (lem-sfb-space-derived-etale-chart-calculus and
lem-weil-pbc-exact-functor-derived-factorization). Complete B -> Rk_*k*B to a triangle
Q -> B -> Rk_*k*B -> Q[1]. Its restriction to T has invertible middle map by the open
counit, so k*Q = 0 (def-weil-triangulated-category, lem-kun-distinguished-cone-zero).
3. Supported excision (lem-sfb-space-supported-etale-excision) gives H = Rp_*Q,
j*H = 0 and the counit isomorphism p*H = Q. Put J = Rj_*A. Etale base change and c
give v : p*J = Rk_*q*A -> Rk_*k*B. Transpose v under p* adjoint to Rp_* and compose
with Rp_* of the connecting map to form beta : J -> H[1]. Complete it to
H -> F -> J -> H[1]. These are the normalized chart-calculus comparisons.
4. Restrict to U; j*H = 0 and the open counit give f : j*F = A
(lem-kun-distinguished-cone-zero and the exact-functor derived factorization).
5. Counit naturality and the transpose identity give e[1] p*beta = delta v.
TR3 completes the endpoints e,v to a map of the rotated triangles. Both endpoints
are isomorphisms, so the middle map g : p*F = B is an isomorphism
(lem-sf-triangle-morphism-iso).
6. Restrict ug = v p*r to T and compose with the open counit. The unit/counit-normalized
base-change comparison gives exactly g|T = c f|T, with the displayed canonical
comparison between the two restrictions (lem-sfb-space-derived-etale-chart-calculus).
7. The signed extension-by-zero exact sequence (lem-sfb-space-elementary-shriek-exact)
applied termwise gives a distinguished triangle (lem-weil-pbc-complex-ses-triangle).
Its adjunctions descend with their units and counits (lem-sfb-adjunction-localization).
Apply Hom(-,M) exactness (lem-weil-pbc-hom-out-of-triangle-exact): a pair of maps on
U,V lifts when its difference on T is zero. Exact restriction and extension by zero
are computed termwise (lem-weil-pbc-exact-functor-derived-factorization).
8. The pair f followed by a, g followed by b has difference zero, since its restriction
is (a|T - b|T c) f|T. The lift is d with the two asserted restrictions, for the same
F,f,g. No degree bounds or finiteness conditions entered the construction.
-/
theorem space_distinguished_derived_gluing {S : Scheme.{u}}
    {W U V : AlgebraicSpace S} (j : U ⟶ W) (p : V ⟶ W)
    (hj : IsRepresentableWith (fun _ _ r ↦ IsOpenImmersion r.left) j.hom.hom)
    (hp : IsEtale p.hom.hom) (Z : ClosedSubspace W)
    (hZ : IsReduced (Z.val : AlgebraicSpace S))
    (hSupport : pointImage Z.val.arrow.hom.hom = (pointImage j.hom.hom)ᶜ)
    (hIso : IsIso (Limits.pullback.snd p.hom Z.val.arrow.hom))
    (W' U' V' T' : AlgebraicSpace S) (t : W' ⟶ W)
    (j' : U' ⟶ W') (p' : V' ⟶ W') (tU : U' ⟶ U) (tV : V' ⟶ V)
    (hU : IsPullback tU j' j t) (hV : IsPullback tV p' p t)
    (q : T' ⟶ U') (k : T' ⟶ V') (hT : IsPullback q k j' p')
    [HasDerivedCategory.{w} W'.SmallModules] [HasDerivedCategory.{w} U'.SmallModules]
    [HasDerivedCategory.{w} V'.SmallModules] [HasDerivedCategory.{w} T'.SmallModules] :
    IsRepresentableWith (fun _ _ r ↦ IsOpenImmersion r.left) j'.hom.hom ∧
    IsEtale p'.hom.hom ∧
    (∃ Z' : ClosedSubspace W', IsReduced (Z'.val : AlgebraicSpace S) ∧
      pointImage Z'.val.arrow.hom.hom = (pointImage j'.hom.hom)ᶜ ∧
      IsIso (Limits.pullback.snd p'.hom Z'.val.arrow.hom)) ∧
    ∀ (A : U'.DerivedModules) (B : V'.DerivedModules)
      (c : (spaceDerivedPullback q).obj A ≅ (spaceDerivedPullback k).obj B),
      ∃ (F : W'.DerivedModules)
        (f : (spaceDerivedPullback j').obj F ≅ A)
        (g : (spaceDerivedPullback p').obj F ≅ B),
        ((spaceDerivedPullbackComp j' q).symm ≪≫
          eqToIso (congrArg spaceDerivedPullback hT.w) ≪≫
          spaceDerivedPullbackComp p' k).hom.app F ≫
            (spaceDerivedPullback k).map g.hom =
          (spaceDerivedPullback q).map f.hom ≫ c.hom ∧
        ∀ (M : W'.DerivedModules)
          (a : A ⟶ (spaceDerivedPullback j').obj M)
          (b : B ⟶ (spaceDerivedPullback p').obj M),
          (spaceDerivedPullback q).map a =
            c.hom ≫ (spaceDerivedPullback k).map b ≫
              ((spaceDerivedPullbackComp j' q).symm ≪≫
                eqToIso (congrArg spaceDerivedPullback hT.w) ≪≫
                spaceDerivedPullbackComp p' k).inv.app M →
          ∃ d : F ⟶ M,
            (spaceDerivedPullback j').map d = f.hom ≫ a ∧
            (spaceDerivedPullback p').map d = g.hom ≫ b := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
