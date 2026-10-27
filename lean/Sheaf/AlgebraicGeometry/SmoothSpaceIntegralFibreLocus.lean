/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Constructible
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.EtaleAtlasPresentation
import Sheaf.AlgebraicGeometry.NormalEtaleComponentsClopen
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import WeilConjectures.AlgebraicGeometry.GenericComponentsSplit
import WeilConjectures.AlgebraicGeometry.GeometricGenericCoverModel
import Sheaf.AlgebraicGeometry.NoetherianAffineAtlasRelation
import Sheaf.AlgebraicGeometry.NoetherianConstructibleSubsetCriterion
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # Integral geometric fibres of a smooth algebraic space

Source: Stacks Project, More on Morphisms, Tags 055B and 055G; More on Morphisms of
Spaces, Tag 0E0A; Spaces over Fields, Tag 0A12. The algebraic-space extension of the
component-incidence argument is the proof in the DAG node
(blueprint: lem-sfb-smooth-space-integral-fibre-locus).

The fibre and its integral predicate are explicit helpers for this node's locus.
Point spaces and their topology are the existing field-valued point classes and atlas
topology. IrreducibleSpace includes nonemptiness; reducedness is tested on etale charts.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The actual presheaf fibre over a field-valued point of the scheme base.
Source: Stacks, Spaces, sheaf fibre products; More on Morphisms, Tag 055B
(blueprint: lem-sfb-smooth-space-integral-fibre-locus). -/
def fieldFibrePresheaf {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {B : Over S}
    (f : F ⟶ yoneda.obj B) (K : Type u) [Field K] (a : Spec (.of K) ⟶ B.left) :
    (Over S)ᵒᵖ ⥤ Type u :=
  Limits.pullback f (yoneda.map
    (Over.homMk (U := Over.mk (a ≫ B.hom)) (V := B) a rfl))

/-- Integrality of this field fibre: nonempty and irreducible in the atlas topology,
and reduced on every representable etale scheme chart. The fibre is not assumed schematic.
Source: Stacks, Properties of Spaces, reducedness and irreducibility; Tag 055B extension
(blueprint: lem-sfb-smooth-space-integral-fibre-locus). -/
def IsIntegralFieldFibre {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {B : Over S}
    (f : F ⟶ yoneda.obj B) (K : Type u) [Field K] (a : Spec (.of K) ⟶ B.left) : Prop :=
  IrreducibleSpace (Point (fieldFibrePresheaf f K a)) ∧
    ∀ (U : Over S) (p : yoneda.obj U ⟶ fieldFibrePresheaf f K a),
      IsEtale p → IsReduced U.left

/-- The integral geometric-fibre locus, using the canonical algebraic closure of each
residue field. The theorem below compares this choice with every other algebraic closure.
This definition also applies directly to the actual presheaf projection after base change.
Source: Stacks, More on Morphisms, Tag 055B and its algebraic-space extension
(blueprint: lem-sfb-smooth-space-integral-fibre-locus). -/
def integralGeometricFibreLocus {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {B : Over S}
    (f : F ⟶ yoneda.obj B) : Set B.left :=
  {b | IsIntegralFieldFibre f (AlgebraicClosure (B.left.residueField b))
    (Spec.map (CommRingCat.ofHom
      (algebraMap (B.left.residueField b) (AlgebraicClosure (B.left.residueField b)))) ≫
        B.left.fromSpecResidueField b)}

/-- The integral geometric-fibre locus of a smooth separated finitely presented algebraic
space over a Noetherian scheme is constructible, independent of algebraic closures,
and has exact inverse-image equality under every scheme base change.
Source: Stacks, Tags 055B, 055G, 0E0A, 0A12 and 053Z; algebraic-space adaptation below
(blueprint: lem-sfb-smooth-space-integral-fibre-locus).

Proof (the eight steps of the source DAG node):
1. Choose an affine surjective etale atlas $p:U\to X$ by [lem-sfb-qc-space-affine-etale-atlas] and
   put $R=U\times_XU$, with projections $s,t$. The base is quasi-compact and $f$ is quasi-compact,
   so $X$ is quasi-compact. Smoothness tested on etale charts makes $U\to B$ locally finitely
   presented. Since $U$ is affine and $B$ is quasi-separated, being locally Noetherian [lem-weil-
   pbc-locally-noetherian-quasi-separated], [lem-weil-pbc-qcqs-morphism-permanence] makes $U\to B$
   finitely presented, hence finite type; [lem-weil-pbc-finite-type-over-noetherian] makes $U$
   Noetherian. Every etale scheme chart of $X$ is locally of finite type over the locally
   Noetherian $B$, hence locally Noetherian by [pqf-def-locnoeth]; $X$ is quasi-separated by the
   assumed finite presentation and separatedness, so [lem-sfb-noetherian-affine-atlas-relation]
   applies: $R$ is a Noetherian scheme. Its maps to $U$ are etale, hence locally finitely
   presented, so $R\to B$ is locally finitely presented by [lem-sfb-space-separated-fp-
   composition]. Quasi-compactness and quasi-separatedness of the Noetherian $R$ [lem-weil-pbc-
   locally-noetherian-quasi-separated] and the same permanence lemma make $R\to B$ finitely
   presented. By [lem-a1-space-affine-etale-cover] the point map of $p$ is an open continuous
   quotient surjection. The presentation and all its etale surjections persist after base change
   by [lem-trf-space-fibre-products-etale-covers].

2. For any algebraically closed geometric point of $B$, let $Y$ denote its fibre and $V$ the
   pulled-back atlas. It is smooth by [lem-sfb-space-smooth-surjective-fppf-locality], so $V$ is a
   smooth finite-type scheme over that field. By [lem-trf-smooth-geometrically-normal], $V$ is
   normal and reduced. It has finitely many irreducible components by [lem-sc-noetherian-finite-
   irreducible-components] and [lem-weil-pbc-finite-type-over-noetherian]; applying
   [lem-a1-normal-etale-components-clopen] to $\mathrm{id}_V$ makes each component open and
   closed. Their images in $Y$ are nonempty irreducible open subsets by continuity and openness of
   the atlas [lem-a1-space-affine-etale-cover]. Reducedness of $Y$ is the etale-chart condition
   that its chart local rings are reduced, which holds here. Consequently $Y$ is integral if and
   only if it is connected: indeed a finite irreducible-open cover of a connected space has
   connected overlap graph, since a partition of this graph gives disjoint nonempty open unions
   covering the space. Overlapping irreducible open subsets have irreducible union: any nonempty
   open in either meets their overlap, and two such opens then meet by irreducibility. Induct
   along a spanning tree of the graph. Conversely every irreducible space is nonempty and
   connected. The empty atlas gives an empty fibre, which satisfies neither property.

3. Let $b'\mapsto b$ under any $h:B'\to B$. Choose algebraic closures $K$ of $\kappa(b)$ and $K'$
   of $\kappa(b')$. By [lem-weil-common-extension-fields] they embed over $\kappa(b)$ into a
   common field $M$. Associativity of the sheaf fibre products [lem-trf-space-fibre-products-
   etale-covers] identifies the two fibres after extension to $M$. Apply [lem-sfb-space-sepclosed-
   components-base-change] separately to the fibres over $K$ and $K'$: each is connected if and
   only if this common extension is connected. Step 2 therefore makes their integrality
   equivalent. Its finite-type smooth atlas exists for both fibres, independently of whether $B'$
   is Noetherian, by base change of $U\to B$ and [lem-weil-pbc-qcqs-morphism-permanence];
   smoothness persists by [lem-sfb-space-smooth-surjective-fppf-locality]. This proves the claimed
   equality of loci under every base change, as well as independence of the chosen algebraic
   closures, before proving constructibility.

4. Fix a nonempty irreducible closed subset $Z\subseteq |B|$. Give it the reduced induced scheme
   structure by [lem-weil-pbc-reduced-induced-closed-subscheme]; this is an integral Noetherian
   scheme with generic point $\eta$. Apply [lem-sbc-generic-components-split] to the finite-type
   generic fibre of $U_Z\to Z$. It gives a finite etale field extension $L/\kappa(\eta)$ over
   which the irreducible components $A_1,\ldots,A_n$ are geometrically irreducible. There are
   finitely many, by [lem-weil-pbc-finite-type-over-noetherian] over the field $L$ and [lem-sc-
   noetherian-finite-irreducible-components]. They form a closed cover, with the empty list
   permitted when the fibre is empty. Apply [lem-sbc-geometric-generic-cover-model] with these
   supplied data. It gives an etale $g:T\to Z$, a generic point $\xi$ above $\eta$, and a finite
   closed cover $C_i$ of $P=U_Z\times_ZT$ whose traces on every field-extended fibre are nonempty
   and irreducible. Restrict $T$ to an affine neighbourhood of $\xi$. Since $Z$ is locally
   Noetherian, hence quasi-separated [lem-weil-pbc-locally-noetherian-quasi-separated], it is
   finitely presented over $Z$ by [lem-weil-pbc-qcqs-morphism-permanence] and is Noetherian by
   [lem-weil-pbc-finite-type-over-noetherian]. Its image $W=g(T)$ is open and contains $\eta$ by
   [lem-a1-space-affine-etale-cover]. No identification of the $C_i$ with the original generic
   components is needed.

5. Set $Q=R\times_BT$, with projections $s,t:Q\to P$. Both $P$ and $Q$ are finitely presented over
   $T$ by step 1 and [lem-weil-pbc-qcqs-morphism-permanence], hence Noetherian by [lem-weil-pbc-
   finite-type-over-noetherian]. For each ordered pair $(i,j)$ form the closed subset
   $D_{ij}=s^{-1}(C_i)\cap t^{-1}(C_j)\subseteq Q$ and give it the reduced induced closed scheme
   structure by [lem-weil-pbc-reduced-induced-closed-subscheme]. The map $D_{ij}\to T$ is quasi-
   compact and locally finitely presented: on Noetherian affine charts its closed immersion has
   finitely generated defining ideal, and it is followed by the finitely presented $Q\to T$, so
   the composite is locally finitely presented by [lem-sfb-space-separated-fp-composition]. Thus
   [lem-weil-pbc-chevalley-constructible-image] makes its image $H_{ij}\subseteq T$ constructible.
   For a geometric point $\bar t$ over $t$, its fibre is nonempty exactly when $t\in H_{ij}$: a
   field-valued point of an ordinary fibre and the geometric field have a common extension by
   [lem-weil-common-extension-fields], so nonemptiness persists after the field extension; the
   converse follows by projection.

6. For a geometric point $\bar t$, put a graph on $\{1,\ldots,n\}$ with edge $ij$ when $t\in
   H_{ij}$. It is symmetric since the relation has an inverse [lem-a1-etale-atlas-presentation].
   The closed irreducible nonempty sets $(C_i)_{\bar t}$ cover $P_{\bar t}$. Their images cover
   $X_{\bar t}$ and are connected, by continuity of the atlas [lem-a1-space-affine-etale-cover].
   Two images meet exactly when there is an edge: two representatives of one space point agree
   over a common field extension, precisely the point relation defined by $P\times_XP$ [lem-trf-
   space-fibre-products-etale-covers, def-a1-space-point-topology]. If the graph is nonempty and
   connected, the images form an intersecting connected chain along each path, so their union is
   connected. Conversely, if the graph has a partition into two nonempty parts with no crossing
   edge, the corresponding finite unions of $(C_i)_{\bar t}$ are disjoint closed sets covering
   $P_{\bar t}$. They are saturated for the atlas relation, since no point in the first can be
   related to a point in the second. The quotient topology therefore gives a partition of $X_{\bar
   t}$ into two nonempty closed, hence also open, subsets. Thus $X_{\bar t}$ is connected exactly
   when this finite graph is nonempty and connected. If $n=0$, $P$ and $X_T$ are empty and the
   condition is false.

7. For fixed $n>0$, graph connectedness is a finite Boolean condition on the edge sets: for every
   nonempty proper subset $J\subset\{1,\ldots,n\}$ require $t\in\bigcup_{i\in J,\ j\notin
   J}H_{ij}$. Take the intersection of these finitely many unions; for $n=1$ the empty
   intersection is $T$, and for $n=0$ use the empty subset. By [def-weil-constructible-subset]
   this defines a constructible subset $F\subseteq T$. Steps 2 and 6 identify $F$ with the
   integral geometric-fibre locus over $T$. Step 3 identifies it with $g^{-1}(E_f\cap Z)$. Since
   $g$ is surjective onto $W$, we have $g(F)=E_f\cap W$. By [lem-weil-pbc-chevalley-constructible-
   image], applied to the finitely presented scheme map $g:T\to Z$ with $Z$ quasi-compact and
   quasi-separated [lem-weil-pbc-locally-noetherian-quasi-separated], this is constructible in
   $Z$.

8. There is now a nonempty relatively open $V\subseteq Z$ which is wholly in $E_f$ or wholly
   outside it. Indeed $W$ contains the generic point $\eta$ of $Z$ and $E_f\cap W$ is a finite
   union of locally closed sets by [def-weil-constructible-subset]. If it contains $\eta$, a
   locally closed term containing $\eta$ has closed factor all of $Z$, hence contains an open
   neighbourhood of $\eta$. If it does not, the closure of each locally closed term is proper: a
   locally closed set dense in irreducible $Z$ is open in $Z$ and contains $\eta$. Remove these
   finitely many proper closed subsets from $W$. This proves the required alternative for every
   irreducible closed $Z$. The Noetherian scheme $B$ has a finite affine cover by Noetherian rings
   by its quasi-compactness and local Noetherianity. Therefore [lem-trf-noetherian-constructible-
   subset-criterion] applies and makes $E_f$ constructible. Together with step 3 this proves every
   assertion, including empty fibres and arbitrary non-Noetherian base changes.
-/
theorem isConstructible_integralGeometricFibreLocus
    {S : Scheme.{u}} (X : AlgebraicSpace S) (B : Over S) [IsNoetherian B.left]
    (f : X.obj.obj ⟶ yoneda.obj B)
    (hsmooth : MapToSchemeIsLocally (@Smooth) X B f)
    (hsep : MapToSchemeIsSeparated X B f)
    (hlfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) X B f)
    (hqc : MapIsQuasiCompact f) (hqs : MapIsQuasiCompact (pullback.diagonal f)) :
    Topology.IsConstructible (integralGeometricFibreLocus f) ∧
      (∀ (b : B.left) (K : Type u) [Field K] [Algebra (B.left.residueField b) K]
        [IsAlgClosure (B.left.residueField b) K],
        IsIntegralFieldFibre f K
          (Spec.map (CommRingCat.ofHom (algebraMap (B.left.residueField b) K)) ≫
            B.left.fromSpecResidueField b) ↔ b ∈ integralGeometricFibreLocus f) ∧
      ∀ (B' : Over S) (h : B' ⟶ B),
        integralGeometricFibreLocus (Limits.pullback.snd f (yoneda.map h)) =
          h.left ⁻¹' integralGeometricFibreLocus f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
