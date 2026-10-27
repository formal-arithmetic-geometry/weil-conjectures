/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import WeilConjectures.AlgebraicGeometry.SeparatedAffineCoverCriterion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Mathlib.AlgebraicGeometry.Limits
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Scheme colimits tested against algebraic spaces

Source: Stacks Project, spaces-pushouts.tex, Tag 07SX, lemma-colimit-agrees
(blueprint: lem-sfb-scheme-colimit-upgrade-space-targets).

Cartesian natural transformations encode the coherent families of schemes in the
limit of the small etale sites. All maps and cocones are over the fixed base.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A scheme colimit satisfying etale base-change and effective descent for compatible
separated etale schemes has the same universal property for algebraic-space targets.

The cartesian squares identify each member with its base change, and the functor and
cocone laws retain all identity and composition coherence. In `hbaseChange`, arbitrary
choices of those pullbacks are allowed, since the colimit property is invariant under
their unique compatible isomorphisms. Separatedness is the closed relative diagonal.

Source: Stacks Project, spaces-pushouts.tex, Tag 07SX, lemma-colimit-agrees
(blueprint: lem-sfb-scheme-colimit-upgrade-space-targets).

Proof (the six steps of the DAG node):
1. Fix an algebraic space $Q/B$ and compatible maps $f_j:X_j\to Q$. By [lem-a1-space-affine-etale-
   cover] choose a surjective etale atlas $w:W\to Q$ with $W=\coprod_a W_a$ and each $W_a$ affine.
   This atlas is separated; here are the details needed to apply (iii). The summands are disjoint
   open and closed subschemes by [lem-weil-pbc-scheme-coproduct-family]. Apply [lem-weil-pbc-
   separated-affine-cover-criterion] to $W\to\operatorname{Spec}\mathbf Z$: for distinct summands
   their intersection is the empty affine scheme and its ring is zero; for a summand with ring
   $A$, the required multiplication $A\otimes_{\mathbf Z}A\to A$ is surjective since $a$ is the
   image of $a\otimes1$. Thus the absolute diagonal of $W$ is a closed immersion. The square with
   top arrow $\Delta_w:W\to W\times_QW$, bottom arrow the absolute diagonal $W\to W\times_{\mathbf
   Z}W$, and left arrow the identity, is cartesian: on every scheme test, two identical
   $W$-sections automatically have the same $Q$-image. Consequently $\Delta_w$ is a closed
   immersion, being a base change of the closed immersion $W\to W\times_{\mathbf Z}W$ [lem-weil-
   pbc-closed-immersion-base-change]. By the same lemma, for every scheme $T$ with a map $T\to
   W\times_QW$ the base change $T\times_{W\times_QW}W\to T$ of $\Delta_w$ is a closed immersion
   [def-weil-closed-immersion]; thus the diagonal of $w$ is a representable closed immersion, i.e.
   $w$ is separated. All the fibre products with two scheme sources over $Q$ are schemes by its
   representable diagonal [def-trf-algebraic-space].
2. Put $U_j=X_j\times_{Q,f_j}W$ and let $h_j:U_j\to W$ be the second projection. These are schemes
   and their maps to $X_j$ are surjective etale by [lem-trf-space-fibre-products-etale-covers];
   they are separated by base change of $w$, using [lem-sfb-space-separated-fp-composition]. For
   an arrow $j\to k$, a pair $(x_j,z)$ maps to $(x_k,z)$, giving $U_j\simeq X_j\times_{X_k}U_k$;
   these identifications satisfy identities and composition because both coordinates do. Hence
   (iii) supplies an etale scheme $p:U\to X$ and coherent identifications $U\times_X X_j\simeq
   U_j$. The $h_j$ form a compatible family of $B$-scheme maps. By (ii) applied to $U\to X$ there
   is a unique $B$-scheme map $h:U\to W$ restricting to all $h_j$.
3. Let $D=U\times_XU$, with projections $p_1,p_2$, and $D_j=U_j\times_{X_j}U_j$. Etale base change
   and composition [lem-sfb-scheme-etale-source-target-properties] show that $D\to X$ is etale.
   Its base change to $X_j$ is $D_j$, by the fibre-product universal property [def-pc-fibre-
   product]. Thus (ii) makes $D$ the colimit of the $D_j$ in $B$-schemes. Put $R=W\times_QW$, a
   scheme by the representable diagonal of $Q$ [def-trf-algebraic-space]. On $D_j$ the two maps
   $h_j\operatorname{pr}_1,h_j\operatorname{pr}_2$ have the same $Q$-image, namely $f_j$ composed
   with the structure map to $X_j$, so they define a compatible family $r_j:D_j\to R$. The scheme-
   colimit property produces $r:D\to R$. Its composite with $R\to W\times_BW$ equals
   $(hp_1,hp_2)$: both have the same restrictions to every $D_j$, and the target is a $B$-scheme.
   Therefore $whp_1=whp_2$.
4. The map $p:U\to X$ is surjective. Indeed, for $x\in X$, (i) supplies $j$ and $x_j\in X_j$
   mapping to $x$; surjectivity of $U_j\to X_j$ supplies $u_j$ above $x_j$, whose image in $U$
   maps to $x$. Since $p$ is etale, it is flat and locally of finite presentation [def-weil-etale-
   morphism], so $\{p\}$ is an fppf covering [def-pc-fppf-site]. The algebraic space $Q$ is an
   fppf sheaf [def-trf-algebraic-space]. Its sheaf equalizer [def-weil-pbc-sites-and-cohomology]
   for this covering, together with the equality on $D$ just proved, gives a unique section $f\in
   Q(X)$ restricting to $wh\in Q(U)$. A section of $Q$ on a scheme $T$ is the same as a morphism
   $h_T\to Q$: its value on a map $a:T'\to T$ is the restriction of the section along $a$, and
   conversely a natural transformation is determined by its value on $\mathrm{id}_T$. Thus $f$ is
   a $B$-morphism $X\to Q$. For every $j$, both $f|_{X_j}$ and $f_j$ restrict on the surjective
   etale map $U_j\to X_j$ to $wh_j$. Applying the same sheaf equalizer on $X_j$ gives
   $f|_{X_j}=f_j$.
5. To prove uniqueness, suppose $f,g:X\to Q$ have equal restrictions on every $X_j$. Pull back the
   atlas $W\to Q$ separately along $f$ and $g$ to get surjective etale schemes $A\to X$ and $C\to
   X$, with lifts $a:A\to W$ and $c:C\to W$ [lem-trf-space-fibre-products-etale-covers]. The
   scheme $T=A\times_X C$ is surjective etale over $X$: its projection to $A$ is a base change of
   the covering $C\to X$, and the composite of two surjective etale maps is surjective etale [lem-
   weil-pbc-etale-covering-composition]. Apply (ii) to $T\to X$, so $T$ is the colimit of
   $T_j=T\times_X X_j$. The pair of lifts $(a\operatorname{pr}_A,c\operatorname{pr}_C):T\to
   W\times_BW$ factors on each $T_j$ through the scheme $R=W\times_QW$, because
   $f|_{X_j}=g|_{X_j}$. These maps to $R$ are compatible by their two projections. The colimit of
   the $T_j$ gives $T\to R$, and uniqueness for the scheme target $W\times_BW$ identifies its
   composite with that pair of lifts. Hence $f|_T=g|_T$. The etale covering $T\to X$ is fppf by
   [def-weil-etale-morphism, def-pc-fppf-site], and the sheaf equalizer [def-weil-pbc-sites-and-
   cohomology] for $Q$ implies $f=g$.
6. Restriction along the given cocone always sends a map $X\to Q$ to a compatible family. Step 4
   proves that every compatible family is its restriction, and step 5 proves injectivity. This is
   the required bijection for every algebraic space $Q/B$, hence the claimed colimit universal
   property.
-/
theorem schemeColimit_has_algebraicSpace_targets
    {B : Scheme.{u}} {J : Type v} [SmallCategory J]
    (F : J ⥤ Over B) (c : Cocone F) (hc : IsColimit c)
    (hjoint : ∀ x : c.pt.left, ∃ (j : J) (y : (F.obj j).left),
      (c.ι.app j).left.base y = x)
    (hbaseChange : ∀ (E : J ⥤ Over B) (e : E ⟶ F) (d : Cocone E)
      (p : d.pt ⟶ c.pt), Etale p.left →
      (∀ j : J, IsPullback (d.ι.app j).left (e.app j).left
        p.left (c.ι.app j).left) → Nonempty (IsColimit d))
    (hdescent : ∀ (E : J ⥤ Over B) (e : E ⟶ F),
      (∀ j : J, Etale (e.app j).left ∧
        IsClosedImmersion (pullback.diagonal (e.app j).left)) →
      (∀ (j k : J) (a : j ⟶ k),
        IsPullback (E.map a).left (e.app j).left (e.app k).left (F.map a).left) →
      ∃ (d : Cocone E) (p : d.pt ⟶ c.pt), Etale p.left ∧
        ∀ j : J, IsPullback (d.ι.app j).left (e.app j).left
          p.left (c.ι.app j).left) :
    ∀ (Q : AlgebraicSpace B)
      (f : ∀ j : J, yoneda.obj (F.obj j) ⟶ Q.obj.obj),
      (∀ (j k : J) (a : j ⟶ k), yoneda.map (F.map a) ≫ f k = f j) →
      ∃! g : yoneda.obj c.pt ⟶ Q.obj.obj,
        ∀ j : J, yoneda.map (c.ι.app j) ≫ g = f j := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
