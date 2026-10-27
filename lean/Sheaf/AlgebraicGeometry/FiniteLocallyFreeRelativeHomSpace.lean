module

public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant
import Sheaf.AlgebraicGeometry.FiniteLocallyFreePrincipalBasisCover
import Sheaf.AlgebraicGeometry.AffineFiniteFreeHom
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenGluing
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Sites.Precoverage

/-! # Relative Hom algebraic spaces from finite locally free scheme sources

Source: Stacks Project, criteria.tex, Tags 05Y2 and 05Y7
(blueprint: lem-sfb-finite-locally-free-relative-hom-space).

The representing space is specified by equivalences on all scheme tests, with their
restriction law and their compatibility with the structural map to the base scheme.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The pairs `(a,b)` defining the relative Hom functor. By Yoneda, a section `b` of `X`
on the scheme fibre product is exactly a map from that scheme to `X`. The subtype equation
is `f b = a pr_U`.
Source: Stacks Project, criteria.tex, Tag 05Y2, description before equation-hom-functor
(blueprint: lem-sfb-finite-locally-free-relative-hom-space). -/
def relativeSpaceHomPairs {S : Scheme.{u}} {Z T : Over S} (p : Z ⟶ T)
    {X : AlgebraicSpace S} (f : X ⟶ schemeSpace T) (U : Over S) : Type u :=
  Σ a : U ⟶ T, {b : X.obj.obj.obj (op (Limits.pullback a p)) //
    f.hom.hom.app (op (Limits.pullback a p)) b = Limits.pullback.fst a p ≫ a}

/-- The canonical map `V ×_T Z → U ×_T Z` for `a' = v ≫ a`, retaining the equality
so restriction can be expressed without silently identifying different chosen pullbacks.
Source: Stacks Project, criteria.tex, Tag 05Y2, restriction in equation-hom-functor
(blueprint: lem-sfb-finite-locally-free-relative-hom-space). -/
def relativeSpaceHomBaseChange {S : Scheme.{u}} {Z T U V : Over S} (p : Z ⟶ T)
    (v : V ⟶ U) (a' : V ⟶ T) (a : U ⟶ T) (q : a' = v ≫ a) :
    Limits.pullback a' p ⟶ Limits.pullback a p :=
  Limits.pullback.map a' p a p v (𝟙 Z) (𝟙 T)
    (by simpa only [Category.comp_id] using q) (by simp)

/-- The relative Hom functor from a finite locally free scheme is an algebraic space.
The equivalences are natural by the displayed restriction equation. The structural map
`h` sends a pair to its first component. No condition on `f` is assumed.
Source: Stacks Project, criteria.tex, Tag 05Y7, proposition-hom-functor-algebraic-space,
specialized to scheme source and scheme base; Tag 05Y2, equation-hom-functor
(blueprint: lem-sfb-finite-locally-free-relative-hom-space).

Proof:
1. Glue the maps `a` and `b` uniquely along an fppf covering using fpqc descent for maps
into algebraic spaces (lem-trf-fppf-covering-is-fpqc,
lem-a1-algebraic-space-fpqc-sheaf, lem-galois-fpqc-covering-base-change).
2. Finite locally free morphisms remain so under base change, by finite, flat and
locally finitely presented permanence (lem-weil-pbc-finite-morphism-permanence,
lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence).
3. Cover the open-and-closed rank pieces by affine principal charts with finite bases
(lem-weil-pbc-finite-locally-free-degree-locally-constant,
lem-a1-finite-locally-free-principal-basis-cover). Rank zero is included.
4. The pullback universal property identifies the Hom functors after base change
(def-pc-fibre-product, lem-trf-space-fibre-products-etale-covers).
5. For a surjective étale scheme atlas of `X`, a lift of `b` is a section of its pullback
over `Z_U`. Its section space is étale and surjective over `U`
(lem-sfb-etale-sections-finite-locally-free, lem-sfb-finite-etale-cover-local-sections).
6. Over a finite free affine base chart, finite unions of affine target components
have affine Hom spaces (lem-weil-pbc-finite-affine-coproduct-spectrum,
lem-sfb-affine-finite-free-hom).
7. Their inclusions into the full Hom functor are open: the locus is the complement
of the finite image of the closed complement of the chosen target components
(lem-weil-pbc-scheme-coproduct-family, lem-weil-pbc-finite-closed-map-finite-fibres).
8. These opens cover on affine tests by quasi-compactness of `Z_U`. Their small
coproduct and open gluing give algebraicity for a disjoint union of affine targets
(lem-weil-pbc-affine-scheme-qcqs, def-weil-size-convention,
lem-trf-algebraic-space-coproduct, lem-trf-algebraic-space-open-gluing).
9. Choose an affine étale atlas of arbitrary `X` and apply the fppf atlas bootstrap
using Step 5 and the sheaf condition (lem-a1-space-affine-etale-cover,
def-weil-etale-morphism, lem-sfb-fppf-space-atlas-bootstrap).
10. Descend algebraicity from the finite free affine base charts using the natural
base-change identification (lem-sfb-fppf-local-algebraic-space). The smallness of the
covers and their atlases follows from the fixed universe convention. Throughout the
identification retains `a`, and pullback of `b` is restriction, yielding the asserted
natural equivalences and their compatibility with `h`.
-/
theorem exists_finiteLocallyFree_relativeHomSpace {S : Scheme.{u}}
    (Z T : Over S) (p : Z ⟶ T) [p.left.IsFiniteLocallyFree]
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace T) :
    ∃ (H : AlgebraicSpace S) (h : H ⟶ schemeSpace T)
      (e : ∀ U : Over S, H.obj.obj.obj (op U) ≃ relativeSpaceHomPairs p f U),
      (∀ (U : Over S) (c : H.obj.obj.obj (op U)),
        (e U c).1 = h.hom.hom.app (op U) c) ∧
      (∀ (U V : Over S) (v : V ⟶ U) (c : H.obj.obj.obj (op U)),
        ∃ q : (e V (H.obj.obj.map v.op c)).1 = v ≫ (e U c).1,
          X.obj.obj.map
              (relativeSpaceHomBaseChange p v
                (e V (H.obj.obj.map v.op c)).1 (e U c).1 q).op (e U c).2.val =
            (e V (H.obj.obj.map v.op c)).2.val) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
