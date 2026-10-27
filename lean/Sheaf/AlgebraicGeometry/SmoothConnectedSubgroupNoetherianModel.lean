/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.RingTheory.FiniteType

import Sheaf.RingTheory.ColimitCategoryFpAlgebras
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import Sheaf.AlgebraicGeometry.DescendSmoothQcqs
import Sheaf.AlgebraicGeometry.GeometricComponentCountBaseChange
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.FiniteStability

/-!
# Simultaneous Noetherian models of smooth groups and connected subgroups

Source: Conrad, Reductive group schemes, proofs of Propositions 2.1.2 and 2.1.6,
printed pp.57 and 62, using EGA IV, 8.3.3, 9.7.9 and 17.8.7
(blueprint: lem-sfb-smooth-connected-subgroup-noetherian-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- A smooth affine group and its smooth geometrically connected closed subgroup descend
simultaneously to a finitely generated integer subalgebra of the base ring.

Source: Conrad, Reductive group schemes, proofs of Propositions 2.1.2 and 2.1.6,
printed pp.57 and 62 (EGA IV, 8.3.3, 9.7.9 and 17.8.7).
(blueprint: lem-sfb-smooth-connected-subgroup-noetherian-model).

`GrpObj` supplies the group diagrams; the models bundle these as `Grp (Over S₀)`.
`IsMonHom` preserves multiplication and identity, hence also inverse for group objects.
The pullback functor carries its canonical group structure, used by the two `IsMonHom` clauses.
`GeometricallyConnected` includes nonemptiness of every geometric fibre.
Affine smooth structure maps are of finite presentation; for a closed immersion finite
presentation is equivalent to local finite presentation. `IsNoetherian` means quasi-compact
and locally Noetherian.

Proof plan (the accepted DAG split):
1. Write $G=\operatorname{Spec}B$. The affine description of a closed immersion gives
$H=\operatorname{Spec}C$ for a quotient $u:B\twoheadrightarrow C$. Since both structure morphisms
are smooth, the affine smoothness criterion gives finite presentations
$B=A[x_1,\ldots,x_r]/(f_1,\ldots,f_s)$ and $C=A[y_1,\ldots,y_t]/(g_1,\ldots,g_v)$. Let $I$ be the
directed set of finitely generated integer subrings $A_i\subseteq A$; its ring colimit is $A$. A
single $A_i$ contains the coefficients of all the $f_a,g_b$. Define $B_i,C_i$ by these same
presentations over $A_i$. Tensoring their presentations with $A$ gives precisely $B,C$. Put
$G_i=\operatorname{Spec}B_i$, $H_i=\operatorname{Spec}C_i$. The affine fibre-product formula
identifies their base changes with $G,H$, using the specified presentation isomorphisms. The
spectra $S_i=\operatorname{Spec}A_i$ have affine transitions and scheme limit $S$. The
presentations give locally finite presentation on the full affine charts; these structure maps are
affine by the fibre-product formula and thus quasi-compact and separated by affine-morphism
permanence, so they are of finite presentation. Dependencies: def-weil-closed-immersion,
lem-weil-pbc-smooth-ring-map-iff-smooth-affine, lemma-nagata-ring-finite-type-subalgebras,
def-weil-pbc-finitely-presented-algebra, lem-weil-pbc-fibre-product-affine-spectra,
lem-weil-pbc-limit-affine-transition, def-weil-affine-spectrum,
def-sbc-locally-finite-presentation, lem-weil-pbc-affine-morphism-permanence.

2. Over the presentations from step 1, the inclusion and the three operations on each group are
seven specified affine morphisms: $H\to G$, $G\times_SG\to G$, $S\to G$, $G\to G$, and the
corresponding three maps for $H$. Contravariantly these are algebra maps among
$A,B,C,B\otimes_AB,C\otimes_AC$. The analogous stage algebras, including triple tensor powers when
needed, are finitely presented: base change and composition preserve finite presentation. The
affine fibre-product formula identifies all these stage and limit products with the required
schemes. Apply the arrow clause (2) of the algebra Hom-descent node to each of the seven maps.
Directedness gives a common stage for all seven. Denote the resulting scheme maps by
$j_i,m_{G,i},e_{G,i},v_{G,i},m_{H,i},e_{H,i},v_{H,i}$. Their pullbacks, under the fixed
isomorphisms of step 1, are exactly the original maps. Dependencies:
lem-weil-pbc-colimit-category-fp-algebras,
lem-weil-pbc-finite-presentation-base-change-composition,
lem-weil-pbc-fibre-product-affine-spectra.

3. For each $Q=G_i,H_i$, form the two sides of the following five equations using its descended
maps and the canonical product identifications: $m(m\times1)=m(1\times m)$ on $Q^3$;
$m(e\times1)=1_Q$ and $m(1\times e)=1_Q$ on $Q$; $m(v,1)=e\circ p_Q$ and $m(1,v)=e\circ p_Q$ on
$Q$, where the last two maps into $Q^2$ use its diagonal. Also form $j_i m_H=m_G(j_i\times j_i)$,
$j_i e_H=e_G$, and $j_i v_H=v_Gj_i$. All thirteen pairs become equal over $A$, since they are the
original group axioms and subgroup compatibilities. In coordinate rings each pair has finitely
presented source and target by step 2. Apply clause (3) of algebra Hom descent to each pair, then
take one upper bound of the thirteen stages. The equations now hold at that stage. Thus both
models are group objects and $j_i$ respects all operations. Each later base change preserves these
equations by functoriality and the universal property of fibre products. This argument does not
assume that $A$ is faithfully flat over $A_i$. Dependencies:
lem-weil-pbc-colimit-category-fp-algebras, def-pc-fibre-product.

4. The stage morphism $j_i:H_i\to G_i$ is locally of finite type: the finite set of algebra
generators of $C_i$ over $A_i$ also generates it over $B_i$ through the descended map. Both
schemes and $S_i$ are affine, hence quasi-compact and quasi-separated. Its limit base change is
the given closed immersion $H\hookrightarrow G$. Apply closed-immersion descent to obtain a later
stage where $j_i$ is a closed immersion. Work over the cofinal tail beginning at that stage.
Closedness persists under further scalar extension: on rings the quotient $B_i\twoheadrightarrow
C_i$ tensors to a surjection, since each tensor is a sum of pure tensors and every element of
$C_i$ lifts to $B_i$. The affine description of closed immersions gives the assertion at every
later stage. Dependencies: lem-weil-pbc-descend-closed-immersion, def-weil-closed-immersion,
lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-affine-scheme-qcqs.

5. Every $A_i$ is a finite type $\mathbf Z$-algebra, so the Noetherian finite-type-algebra theorem
applies, since every ideal of $\mathbf Z$ is principal. Thus $A_i$ is Noetherian; applying the
same theorem to $A_i\to B_i$ and $A_i\to C_i$ makes both coordinate rings Noetherian. The
finite-type-over-Noetherian-scheme theorem, starting with $\operatorname{Spec}\mathbf Z$, makes
$S_i,G_i,H_i$ Noetherian schemes. Finally $C_i$ is finite type over $B_i$ by the same generators
used in step 4. The finite-type-over-Noetherian-ring finite-presentation theorem therefore makes
$B_i\to C_i$ finitely presented. Consequently $j_i$ is a finitely presented closed immersion. The
assertions hold at every subsequent stage as well, since its base ring remains a finitely
generated integer subring and its two coordinate algebras retain finite presentations.
Dependencies: lem-weil-pbc-finite-type-algebra-noetherian,
lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-finite-type-noetherian-finite-presentation.

6. Apply eventual smoothness to each of $G_i\to S_i$ and $H_i\to S_i$. Its hypotheses hold: the
stages and both model schemes are affine and therefore quasi-compact and quasi-separated, the two
morphisms have finite presentations, and their pullbacks to $S$ are the given smooth structure
maps. Take a common upper bound of the two eventual-smoothness stages. Both structure maps are
smooth at every subsequent stage, as explicitly supplied by the cited statement. The operations
and the closed inclusion remain the base changes of those already constructed. Dependencies:
lem-weil-pbc-descend-smooth-qcqs, lem-weil-pbc-affine-scheme-qcqs.

7. At this smooth stage let $f_i:H_i\to S_i$ and let $E=\{s\in S_i:n_{f_i}(s)=1\}$, where
$n_{f_i}$ counts geometric connected components and assigns count zero to the empty fibre. Since
$f_i$ is finitely presented and $S_i$ is Noetherian, the geometric-component-locus theorem says
that $E$ is constructible. For any $s\in S$, component-count base change gives
$n_{H/S}(s)=n_{f_i}(s_i)$. The left side is one by the nonempty geometrically connected fibre
hypothesis. Thus the image of $S$ in $S_i$ lies in $E$. Apply constructible-image descent to the
affine-transition system $S_j$ on this tail. It gives $j\geq i$ such that the image of every
$S_k$, $k\geq j$, in $S_i$ lies in $E$. For any $t\in S_j$, base change again gives
$n_{H_j/S_j}(t)=n_{f_i}(t_i)=1$. A space with exactly one maximal nonempty connected component is
nonempty and connected: every point belongs to a connected component, so the unique component is
the whole space. Hence all the geometric fibres of $H_j\to S_j$ are nonempty and connected. This
treats count zero separately, rather than mistaking empty fibres for connected ones. Dependencies:
lem-sfb-geometric-connected-fibre-locus-constructible,
lem-weil-pbc-geometric-component-count-base-change, lem-weil-pbc-limit-contained-in-constructible,
lem-weil-pbc-affine-scheme-qcqs.

8. Take $A_0=A_j$, $S_0=S_j$, $G_0=G_j$ and $H_0=H_j$. Steps 3--6 give the group objects, finitely
presented closed subgroup, smoothness, and Noetherian assertions. Step 7 gives the required
geometric fibres. Throughout, the presentation isomorphisms of step 1 identify each descended
operation with its original after extension to $A$, and identify $j_j$ with $H\hookrightarrow G$.
Therefore those very isomorphisms are group-scheme isomorphisms preserving multiplication,
identity, inverse and the closed inclusions, which proves every clause.
-/
theorem exists_smooth_connected_subgroup_noetherian_model
    (A : Type u) [CommRing A] (G H : Over (Spec (CommRingCat.of A)))
    [GrpObj G] [GrpObj H] [IsAffine G.left] [Smooth G.hom]
    (j : H ⟶ G) [IsMonHom j] [IsClosedImmersion j.left]
    [LocallyOfFinitePresentation j.left] [Smooth H.hom] [GeometricallyConnected H.hom] :
    ∃ A₀ : Subalgebra ℤ A, A₀.FG ∧ IsNoetherianRing A₀ ∧
      ∃ G₀ H₀ : Grp (Over (Spec (CommRingCat.of A₀))),
        IsAffine G₀.X.left ∧ Smooth G₀.X.hom ∧ IsNoetherian G₀.X.left ∧
        ∃ j₀ : H₀ ⟶ G₀,
          IsClosedImmersion j₀.hom.hom.left ∧
          LocallyOfFinitePresentation j₀.hom.hom.left ∧
          Smooth H₀.X.hom ∧ GeometricallyConnected H₀.X.hom ∧
          ∃ eG : (Over.pullback (Spec.map (CommRingCat.ofHom A₀.val.toRingHom))).obj G₀.X ≅ G,
            ∃ eH : (Over.pullback (Spec.map (CommRingCat.ofHom A₀.val.toRingHom))).obj H₀.X ≅ H,
              IsMonHom eG.hom ∧ IsMonHom eH.hom ∧
              ((Over.pullback (Spec.map (CommRingCat.ofHom A₀.val.toRingHom))).map
                j₀.hom.hom).left ≫ eG.hom.left = eH.hom.left ≫ j.left := by
  sorry

end AlgebraicGeometry
