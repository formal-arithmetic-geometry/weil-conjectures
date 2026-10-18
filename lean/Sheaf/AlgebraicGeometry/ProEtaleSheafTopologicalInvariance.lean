/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.Topology.Homeomorph.Defs
import Sheaf.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.RingTheory.Etale.Basic
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Sheaf.RingTheory.FilteredColimitAlgebrasTensorElementwise
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.RingTheory.IndPrincipalZariski
import Mathlib.Algebra.Category.CommAlgCat.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.RingTheory.IndEtaleStability
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import WeilConjectures.CategoryTheory.SiteEquivalenceMorphismOfSites
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.SliceSiteLocalization
import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Topological invariance of the small pro-etale topos

Source: Stacks Project, Tag 09AB, `proetale-lemma-thickening`; Tag 04DF identifies
universal homeomorphisms with integral, universally injective, surjective morphisms
(blueprint: lem-trf-proetale-topological-invariance).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Universal homeomorphisms induce equivalences of the small pro-etale topoi of sets.
Both equivalence assertions concern the recorded inverse and direct image, and the last
clauses assert invertibility of the components of their specified adjunction.
Source: Stacks Project, Tag 09AB, `proetale-lemma-thickening`, with Tag 04DF
(blueprint: lem-trf-proetale-topological-invariance).

Proof (the expanded affine-basis argument of Tag 09AB):

1. First construct a cover by pairs of affine opens. Choose affine opens X_a covering X.
Since r is a homeomorphism, Y_a=r(X_a) is open, and r^{-1}(Y_a)=X_a. The restriction
r_a:X_a\to Y_a is a universal homeomorphism: each of its base changes is a base change of r.
In particular it is surjective and universally closed. Apply
[lem-weil-pbc-surjective-universally-closed-affine-target] to conclude that Y_a is affine.
Thus (X_a,Y_a) are matching affine covers, without assuming that r is finite or that either
scheme is quasi-separated. The argument below first treats an arbitrary universal homeomorphism
between affine schemes, and then applies it to each r_a.

2. Suppose now Y=\operatorname{Spec}A and X=\operatorname{Spec}B. Base change along r is
an equivalence of the categories of etale schemes by
[lemma-weil-pbc-universal-homeomorphism-site-equivalence]. It restricts to affine etale schemes:
base change of an affine scheme over an affine base is the spectrum of the tensor product, by
the ring-map and fibre-product universal properties [def-weil-affine-spectrum,
def-pc-fibre-product]. Conversely, if an etale V\to Y has affine pullback V_X, the map
V_X\to V is a universal homeomorphism and hence surjective and universally closed, so
[lem-weil-pbc-surjective-universally-closed-affine-target] makes V affine. By
[lem-weil-pbc-etale-algebra-finite-presentation-localization], the coordinate algebras of all
these affine etale objects are finitely presented. Taking opposites therefore gives an
equivalence E:C\mapsto B\otimes_A C between etale A-algebras and etale B-algebras, with a
functorial quasi-inverse on those categories.

3. For later use, if P is a finitely presented R-algebra and (D_j) a small filtered
diagram of commutative R-algebras, then
\varinjlim_j\operatorname{Hom}_R(P,D_j)\to\operatorname{Hom}_R(P,\varinjlim_jD_j) is
bijective. Surjectivity is exactly
[lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit], after
[lem-weil-pbc-filtered-colimit-algebras-elementwise] identifies the algebra colimit with the
ring colimit. For injectivity choose finitely many generators of P, put two representative
maps at a common index, and apply clause (2) of
[lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise] with N=R to their differences on
these generators, using D_j\otimes_RR=D_j. Filteredness puts the finitely many resulting
equalities at one later index, where the two homomorphisms are equal on every generator and
hence equal. This also handles zero generators; filtered categories are nonempty
[def-weil-pbc-category-colimit].

4. Extend the equivalence E of step 2 to ind-etale algebras [def-weil-pbc-ind-etale-algebra].
Tensor product commutes with these colimits: maps from either B\otimes_A\varinjlim_i C_i or
\varinjlim_i(B\otimes_A C_i) to a B-algebra are precisely compatible A-algebra maps C_i
into that algebra, so the canonical comparison is invertible by the colimit universal property
[def-weil-pbc-category-colimit]. For presentations C=\varinjlim_i C_i and D=\varinjlim_j D_j
with etale finitely presented terms, the universal property and step 3 give the natural formula
\operatorname{Hom}_A(C,D)=\varprojlim_i\varinjlim_j\operatorname{Hom}_A(C_i,D_j). The same
formula over B and the full faithfulness of E on each pair of terms prove full faithfulness
on ind-etale algebras. Given an ind-etale B-algebra D=\varinjlim_j D_j, apply the
quasi-inverse of E to the entire diagram, including its arrows, and form C=\varinjlim_j
E^{-1}(D_j); these colimits exist by [lem-weil-pbc-commutative-algebras-colimits-exist]. Its
base change is D, proving essential surjectivity. Opposite affine spectra give an equivalence
u:\mathcal B_Y\simeq\mathcal B_X of the affine ind-etale categories
[def-weil-pbc-ind-etale-basis]. All diagrams are small in the compatible universes of the item;
no fixed bound smaller than the allowed universe is imposed.

5. Verify the covering assertion omitted by the source. In either affine ind-etale category, a
finite family of arrows with target V is a covering exactly when it is jointly surjective.
Indeed every arrow is weakly etale by [lem-weil-pbc-ind-etale-stability], and every arrow
between affine schemes has affine inverse images of affine opens: on principal opens the inverse
images are the corresponding principal spectra, and the affine-morphism criterion
[pqf-lem-affine-local-target] extends this to all affine opens. Thus the finitely many inverse
images of any affine open of V themselves give the finite affine opens required in the fpqc
covering definition [def-weil-pbc-proetale-site]; necessity of surjectivity follows from that
same definition. For each V\in\mathcal B_Y, the projection V_X\to V and the analogous
projections for all domains are homeomorphisms by [def-weil-universal-homeomorphism]. Their
commuting squares identify the images of the arrows, so their union is all of V if and only if
the base-changed union is all of V_X. Consequently u preserves and reflects finite basis
coverings, including the empty covering of the empty object. Now let \{U_i\to V\}_{i\in I} be
an arbitrary family of arrows of \mathcal B_Y, with coverings induced from the pro-etale site
[def-weil-pbc-ind-etale-basis]. It is a covering if and only if some finite subfamily is jointly
surjective: if it is a covering, the covering definition applied to the affine open V itself
gives finitely many affine opens of some U_{i_1},\dots,U_{i_n} whose images cover V;
conversely, if a finite subfamily is jointly surjective, all arrows are weakly etale and, for
every affine open W\subset V, the affine inverse images of W in U_{i_1},\dots,U_{i_n} have
images covering W. The same holds in \mathcal B_X, and u preserves and reflects joint
surjectivity of finite subfamilies by the homeomorphism argument above. Therefore \{U_i\to V\}
is a covering of \mathcal B_Y if and only if \{u(U_i)\to u(V)\} is a covering of \mathcal
B_X. This is the family-level hypothesis of
[lem-weil-pbc-site-equivalence-is-morphism-of-sites] used in step 6. (This also agrees with
[lem-weil-pbc-ind-etale-basis]: every covering of a basis object refines to a finite basis
covering.)

6. Pass from the bases to sheaves with [lem-cbc-local-dense-ordinary-sheaves], applied to each
full inclusion \mathcal B_T\hookrightarrow T_{\mathrm{proet}}, T=X,Y. Its cover-density
hypothesis is supplied by [lem-weil-pbc-ind-etale-basis]. For full inclusions the sieves L_b
and E_{f,g} in the comparison statement are maximal: lift b by fullness, and use
faithfulness for f=g. The induced topology criterion follows because every ambient cover of a
basis object refines to a finite basis cover, again by [lem-weil-pbc-ind-etale-basis]. Sets in
the larger universe have all the small comma-category limits required by that theorem. Thus
restriction to each basis is an equivalence of categories of set sheaves. The equivalence of
bases from steps 4 and 5 induces a sheaf equivalence by
[lem-weil-pbc-site-equivalence-is-morphism-of-sites], clause (3). For G on X, the square of
these restriction functors commutes: on V\in\mathcal B_Y both composites have value G(V_X)
and the same restriction maps [def-weil-proetale-inverse-image]. Therefore the actual direct
image r_* is an equivalence when X,Y are affine.

7. In the affine case the actual adjunction L=r^{-1}\dashv R=r_*
[def-weil-proetale-inverse-image] has invertible unit and counit. To check this for its
specified maps, apply [lem-coef-adjunction-equivalence-counit-iso] to the opposite adjunction
R^{\mathrm{op}}\dashv L^{\mathrm{op}}: its left adjoint is an equivalence by step 6, so its
counit, which is the opposite of \eta, is invertible. The triangle
R(\varepsilon_G)\circ\eta_{RG}=1 then makes R(\varepsilon_G) invertible. Since R is fully
faithful, lift its inverse to a morphism G\to LRG; faithfulness checks both inverse
identities. Thus \varepsilon_G itself is invertible. These are the canonical adjunction maps,
rather than unspecified isomorphisms of the two composites.

8. Return to the matching affine covers of step 1. For an open immersion W\hookrightarrow T,
the small pro-etale site of W is the slice of T_{\mathrm{proet}} over W, by clause (1) of
[lem-weil-proetale-weakly-etale-localization], whose hypotheses explicitly include open
immersions and whose conclusion identifies the sites and their set sheaves. Apply
[lem-weil-pbc-slice-site-localization] to u_r and each Y_a. It identifies the restriction of
r_* with (r_a)_* and the restriction of r^{-1} with (r_a)^{-1}. These comparisons carry
the unit and counit to the localized adjunction maps: the direct-image comparison is the
identity on G(V_X), the unit on a presheaf section is the coprojection indexed by
(V,\mathrm{id}_{V_X}), and the counit on a representative [V,\phi,s] is G(\phi)(s), using
[def-weil-proetale-inverse-image]. Restriction keeps those formulas, and their sheafifications
are uniquely determined by them. Step 7 therefore makes the restricted unit and counit
invertible on every Y_a and X_a, respectively. The cover-local isomorphism criterion
[lem-sfb-sheaf-cover-local-isomorphism] makes them invertible globally: every object has its
covering obtained by pullback of these Zariski open covers. Hence r^{-1} and r_* with their
given adjunction are quasi-inverse equivalences as claimed. -/
theorem proEtaleSheaf_topological_invariance {X Y : Scheme.{u}} (r : X ⟶ Y)
    (hr : (topologically IsHomeomorph).universally r) :
    (proEtaleSheafInverseImage r (Type (u + 1))).IsEquivalence ∧
      (proEtaleSheafDirectImage r (Type (u + 1))).IsEquivalence ∧
      (∀ F : Sheaf (ProEt.topology Y) (Type (u + 1)),
        IsIso ((proEtaleSheafAdjunction r (Type (u + 1))).unit.app F)) ∧
      (∀ G : Sheaf (ProEt.topology X) (Type (u + 1)),
        IsIso ((proEtaleSheafAdjunction r (Type (u + 1))).counit.app G)) := by
  sorry

end AlgebraicGeometry.Scheme
