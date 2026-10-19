/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.FiberDegreeBound
import Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange
import Sheaf.AlgebraicGeometry.BoundsFiberDegreesFieldPoints
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Sheaf.AlgebraicGeometry.QuasiAffineBaseChange
import Sheaf.AlgebraicGeometry.SpaceSeparatedLqfPermanence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.FppfSheafRepresentabilityDescentData
import Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage

/-!
# Étale quasi-affine image is schematic

Source: Stacks Project, Spaces and Morphisms, Tag 03XW.
(blueprint: lem-a1-etale-quasi-affine-image-scheme).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A scheme over `S` is a spectrum of a field, up to an isomorphism of schemes.
Source: Stacks Project, Spaces and Morphisms, Tag 03XW.
(blueprint: lem-a1-etale-quasi-affine-image-scheme).
-/
def IsFieldSpectrum {S : Scheme.{u}} (U : Over S) : Prop :=
  ∃ (K : Type u) (_ : Field K), Nonempty (U.left ≅ Spec (.of K))

/-- Two scheme-valued points represent the same field-valued point class when they
agree after a common field-spectrum refinement. For a field-spectrum test `U`, a map
`E → U` is a field extension contravariantly; `E → V` is the lifted point.
Source: Stacks Project, Properties of Spaces, Tag 03BU, and Spaces and Morphisms,
Tag 03XW (blueprint: lem-a1-etale-quasi-affine-image-scheme). -/
def FieldPointImage {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : Over S) (g : yoneda.obj U ⟶ X.obj.obj)
    (V : Over S) (v : yoneda.obj V ⟶ X.obj.obj) : Prop :=
  ∃ (E : Over S) (i : E ⟶ U) (j : E ⟶ V),
    IsFieldSpectrum E ∧ yoneda.map i ≫ g = yoneda.map j ≫ v

/-- The image of a quasi-affine open after an affine étale base change is a
quasi-compact open represented by a scheme.

Source: Stacks Project, Spaces and Morphisms, Tag 03XW.
(blueprint: lem-a1-etale-quasi-affine-image-scheme).

Proof (the eleven steps of the DAG node):

1. Put $X'=X\times_TT'$ and let $r:X'\to X$ be the projection. By
[lem-trf-space-fibre-products-etale-covers] and [lem-trf-space-chartwise-etale-permanence], $r$ is
representable etale. The open inclusion $V'\to X'$ is representable etale: on every scheme base
change it is an open immersion, hence etale by clause (1) of
[lem-weil-pbc-etale-composition-cancellation]. Thus $q:V'\to X$ is representable etale by the same
algebraic-space permanence statement. Since $T'$ is affine, the given factorization of $V'\to T'$
is a quasi-compact open immersion into an affine scheme, using clause (2) of
[lem-weil-pbc-affine-morphism-permanence]. That affine scheme is quasi-compact by
[lem-weil-pbc-affine-scheme-qcqs], so $V'$ is quasi-compact. Apply [lem-a1-space-etale-open-image]
to $q$ to obtain the quasi-compact open subspace $W\subseteq X$ with $|W|=q(|V'|)$. It remains to
prove that this particular $W$ is a scheme.

2. For each integer $n\geq0$, let $P(n)$ assert the claimed schematicity for every diagram in the
statement whose affine etale map $a$ has fibre degrees bounded by $n$
[def-weil-pbc-fibre-degree-bound]. These quantify over all schemes and diagrams, so they may be
applied with a new target. The map $a$ is locally quasi-finite: every etale scheme chart of $T'$
has etale composite to $T$ by [lem-weil-pbc-etale-composition-cancellation], so
[lem-a1-etale-space-locally-quasi-finite], applied to the scheme $T'$ as an algebraic space and
then its identity chart, gives this. Its source $T'$ is quasi-compact by
[lem-weil-pbc-affine-scheme-qcqs]. Hence [lem-weil-pbc-lqf-qc-source-bounded-fibres] supplies such
an $n$. We prove $P(n)$ by strong induction. If $n=0$, every fibre is the spectrum of the zero
algebra, hence empty; a point of $T'$ would lie in a nonempty fibre. Thus $T'=\varnothing$,
$V'=\varnothing$, and $W$ is the empty scheme. In the remaining steps fix $n\geq1$ and assume
$P(m)$ for $m<n$.

3. Let $T''=T'\times_TT'$ with projections $\pi_0,\pi_1$. It is affine by
[lem-weil-pbc-fibre-product-affine-spectra]. The map $a$ is affine, hence separated, by
[lem-weil-pbc-morphism-affine-schemes-affine] and clause (3) of
[lem-weil-pbc-affine-morphism-permanence]; separated means its diagonal is closed
[def-weil-proper-morphism]. Its diagonal $\delta:T'\to T''$ is also open, since etale implies
unramified [def-weil-etale-morphism], and [def-weil-unramified-morphism] defines unramified using
the open diagonal. Therefore $T''=\delta(T')\amalg T^*$ as open and closed subschemes. The
complement $T^*$ is affine: on $T''=\operatorname{Spec}R$ its clopen subset is $D(e)$ for an
idempotent $e$ by [lem-weil-pbc-spec-clopen-idempotent], represented by $\operatorname{Spec}R_e$
by [lem-weil-pbc-principal-localization-open-immersion]. The restriction $b=\pi_1|_{T^*}:T^*\to
T'$ is etale, since $\pi_1$ is a base change of $a$ and the inclusion of $T^*$ is open; use
[lem-trf-space-chartwise-etale-permanence] and [lem-weil-pbc-etale-composition-cancellation].

4. The fibre degrees of $\pi_1:T''\to T'$ are bounded by $n$ by
[lem-weil-pbc-fibre-degree-base-change]. For any field-valued point $\operatorname{Spec}K\to T'$,
[lem-weil-pbc-fibre-degree-bound-field-points] makes its fibre a finite $K$-scheme of degree at
most $n$. The clopen decomposition of step 3 pulls back to the disjoint union of the diagonal
section $\operatorname{Spec}K$ and the fibre of $T^*$. A finite scheme over a field is affine; its
coordinate algebra therefore decomposes as $K\times C$, where $C$ is the finite-dimensional
algebra of the complementary fibre. The vector-space identity $\dim_K(K\times C)=1+\dim_K C$ gives
$\dim_K C\leq n-1$. The converse direction of [lem-weil-pbc-fibre-degree-bound-field-points],
applied to $b$, now bounds every fibre degree of $b$ by $n-1$. This calculation works over every
field without assuming that residue fields are algebraically closed.

5. If $n=1$, the previous calculation forces $T^*=\varnothing$ (a point of $T^*$ would give a
nonempty fibre). Hence $\delta:T'\to T''$ is an isomorphism. The fibre-product universal property
then says $a$ is a monomorphism: any pair of maps with equal composites through $a$ gives a map to
$T''$, which factors uniquely through $\delta$, so the two maps agree. The etale definition
[def-weil-etale-morphism] supplies flatness and local finite presentation. By
[lem-pe-flat-lfp-monomorphism-open], $a$ is an open immersion. Its base change $r:X'\to X$ is an
open immersion: each scheme test is a base change of $a$, hence is an open immersion by
[lem-weil-pbc-open-immersion-base-change]. Thus the composite open inclusion $V'\to X$ identifies
$W$ with the scheme $V'$. This proves $P(1)$. We may now assume $n>1$.

6. Write $X''=X\times_TT''$, $X^*=X\times_TT^*$, and let $p_i:X''\to X'$ be induced by $\pi_i$.
Put $Z=p_0^{-1}(V')\cap X^*$. As a space over $T^*$ this is the scheme $T^*\times_{\pi_0,T'}V'$.
Its map to $T^*$ is quasi-affine by [lem-trf-quasi-affine-base-change]; the base change here uses
$\pi_0$, whereas $X^*\to X'$ uses $\pi_1$. The space $Z$ is open in $X^*=T^*\times_{b,T'}X'$,
because it is the pullback of the open $V'\subseteq X'$ along the other projection. By
[lem-a1-space-separated-lqf-permanence], $X'\to T'$ is separated and chartwise locally
quasi-finite. The map $b:T^*\to T'$ is etale between affine schemes and its fibre degrees are
bounded by $n-1$. All hypotheses of $P(n-1)$ therefore hold for $(T',T^*,X',Z)$. It gives a
quasi-compact open scheme $H\subseteq X'$ with $|H|=p_1(|Z|)$.

7. Apply the base-change image clause of [lem-a1-space-etale-open-image] to $q:V'\to X$ and
$r:X'\to X$. It identifies the inverse image $P=W\times_XX'=T'\times_TW$ with the image open of
$V'\times_XX'\to X'$. The latter source is $p_0^{-1}(V')\subseteq X''$, mapping by $p_1$. On the
diagonal component of $X''=X'\amalg X^*$ its image is $V'$, and on the complementary component its
image is $H$ by step 6. The inclusion-preserving open-subspace correspondence in the same lemma
therefore gives $P=V'\cup H$. This is a Zariski covering by two open schemes: after a map from any
scheme, the two open pullbacks cover that scheme, since their point sets do. The sheaf $P$ is an
algebraic space, hence an fppf sheaf by [def-trf-algebraic-space], and in particular a Zariski
sheaf. Apply [lem-pc-schemes-criterion] to the two open subfunctors $V',H\subseteq P$ to obtain a
scheme representing $P$. Its underlying space is quasi-compact, as a union of two quasi-compact
open subsets.

8. Apply [lem-a1-space-separated-lqf-permanence] to $W\subseteq X$ and to base change by $T'\to
T$. It makes the scheme map $P\to T'$ separated and locally quasi-finite. The target $T'$ is
quasi-separated by [lem-weil-pbc-affine-scheme-qcqs], and $P$ is quasi-compact by step 7, so
[lem-weil-pbc-qcqs-morphism-permanence], clause (1), makes $P\to T'$ quasi-compact. By
[lem-weil-pbc-lqf-locally-finite-type] it is locally of finite type. The four hypotheses of
[lemma-nagata-quasi-affine-morphism-of-quasi-finite] now hold for this scheme map, so $P\to T'$ is
quasi-affine. No Noetherian, finite-presentation, or finiteness assumption on $X$ has been
inserted.

9. Let $B\subseteq T$ be the open image of $a$, supplied by [lem-a1-space-etale-open-image]
applied to schemes. Then $p:T'\to B$ is surjective etale. It is also affine: $T'\times_TB=T'$
since $a$ factors through $B$, and affineness follows by base change from the affine map $a$ using
[lem-weil-pbc-affine-morphism-permanence]. The sheaf $W$ factors through $B$: its point image in
$T$ lies in $B$, since $|W|=q(|V'|)$ and $V'\to T$ factors through $T'$. Thus $W\cap(X\times_TB)$
and $W$ have the same point subset of $X$, and the open-subspace correspondence of that same image
lemma identifies them. For every affine open $C\subseteq B$, $p^{-1}(C)$ is affine and surjects
onto $C$. With flatness and local finite presentation from [def-weil-etale-morphism], this
verifies the singleton fpqc-covering condition [def-weil-pbc-fpqc-covering] and the fppf-covering
condition [def-pc-fppf-site]. The base $B$ need not be affine.

10. Regard $W$ over $B$ as the sheaf assigning to $Q\to B$ the $S$-morphisms $Q\to W$ compatible
with the maps to $B$. This is an fppf sheaf: compatible maps to $W$ glue uniquely because $W$ is
an algebraic space [def-trf-algebraic-space], and equality of their composites to $B$ is also
local. Its pullback along $p$ is represented by $P=T'\times_BW=T'\times_TW$, the scheme of step 7.
Apply [lem-trf-fppf-sheaf-representability-descent-data] to the fppf covering $\{p:T'\to B\}$. It
gives a scheme descent datum on $P/T'$. On the double overlap its comparison is the natural
interchange of $P\times_BT'$ with $T'\times_BP$ representing the same sheaf
$T'\times_BW\times_BT'$; on the triple overlap both composites keep the same section of $W$ and
the same three base coordinates. This is its cocycle. The statement of the cited node, rather than
a claim that fpqc is a site, supplies both this datum and the criterion that its effectivity is
equivalent to representability of the sheaf $W$ over $B$.

11. The map $p:T'\to B$ is an fpqc covering by step 9, and $P\to T'$ is quasi-affine by step 8.
Apply [lem-trf-quasi-affine-fpqc-effective-descent] to the datum of step 10. It is effective. The
representability-if-effective clause of [lem-trf-fppf-sheaf-representability-descent-data] now
represents $W$ by a scheme over $B$, hence over $S$. We have proved $P(n)$ under the induction
hypotheses. Strong induction and the bound from step 2 prove schematicity for the original
diagram. Together with step 1 this is exactly the quasi-compact open image asserted in the
statement.
-/
theorem etale_quasiAffine_image_scheme
    {S : Scheme.{u}} (T T' : Over S) [IsAffine T.left] [IsAffine T'.left]
    (a : T' ⟶ T) [Etale a.left]
    (X : AlgebraicSpace S)
    (f : X.obj.obj ⟶ yoneda.obj T)
    (hlocal : ∀ (U : Over S) (g : yoneda.obj U ⟶ X.obj.obj)
      (q : U ⟶ T), AlgebraicSpace.IsEtale g → yoneda.map q = g ≫ f →
        Scheme.Hom.IsLocallyQuasiFinite q.left)
    (hdiag : AlgebraicSpace.IsRepresentableWith
      (fun _ _ p ↦ IsClosedImmersion p.left) (Limits.pullback.diagonal f))
    (V' : Over S) (v : yoneda.obj V' ⟶ X.obj.obj)
    (b : V' ⟶ T') (hcomm : v ≫ f = yoneda.map b ≫ yoneda.map a)
    (hvopen : AlgebraicSpace.IsRepresentableWith
      (fun _ _ p ↦ IsOpenImmersion p.left)
      (Limits.pullback.lift v (yoneda.map b) hcomm))
    (hvquasi : ∃ (Y : Over S) (j : V' ⟶ Y) (c : Y ⟶ T'),
      j ≫ c = b ∧ IsOpenImmersion j.left ∧ QuasiCompact j.left ∧ IsAffineHom c.left) :
    ∃ (W : Over S) (w : yoneda.obj W ⟶ X.obj.obj),
      CompactSpace W.left ∧
      AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) w ∧
      ∀ (U : Over S) (g : yoneda.obj U ⟶ X.obj.obj), IsFieldSpectrum U →
        (FieldPointImage U g V' v ↔ FieldPointImage U g W w) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
