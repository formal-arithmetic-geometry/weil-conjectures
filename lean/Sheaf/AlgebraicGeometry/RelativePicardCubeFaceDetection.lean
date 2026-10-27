/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import Sheaf.AlgebraicGeometry.RelativeGroupUnitAxisFactorization
import Sheaf.AlgebraicGeometry.ProperFlatGlobalSections
import Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed
import Sheaf.AlgebraicGeometry.PicardLocusClosed
import Sheaf.AlgebraicGeometry.PicardProductOpen
import Sheaf.AlgebraicGeometry.GeneralTheoremOfCube
import WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorDecomposition
import WeilConjectures.AlgebraicGeometry.Descent

/-!
# Relative Picard detection by the three identity faces

Source: Moret-Bailly, Pinceaux de varietes abeliennes, I 2.6, geometric cube input;
Stacks Project, Tag 0BF4; Conrad, Semistable Reduction, Definition 2.2 and Theorem 3.1
(blueprint: lem-sfb-relative-picard-cube-face-detection).

The geometric semiabelian hypothesis uses the shared definition
`HasSemiabelianGeometricFibres`, with its split-torus kernel and fppf-locally
surjective abelian quotient. No choice of face trivializations or cubical
structure occurs in the statement.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- The identity face of a triple product, parametrized by the other two factors.
The component in coordinate `i` is the identity section composed with the structure map;
every other component is the corresponding product projection.
Source: Moret-Bailly, I 2.6, geometric cube input
(blueprint: lem-sfb-relative-picard-cube-face-detection). -/
noncomputable def groupIdentityFace {S : Scheme.{u}} (G : Fin 3 → Over S)
    [∀ i : Fin 3, CommGrpObj (G i)] (i : Fin 3) :
    (∏ᶜ (fun j : { j : Fin 3 // j ≠ i } ↦ G j.1)) ⟶ ∏ᶜ G :=
  Pi.lift (fun j ↦ if h : j = i then 1 else
    Pi.π (fun j : { j : Fin 3 // j ≠ i } ↦ G j.1) ⟨j, h⟩)

/-- A line trivial on all three identity faces is trivial under either geometric hypothesis.

Source: Moret-Bailly, I 2.6, geometric cube input; Stacks Project, Tag 0BF4;
Conrad, Semistable Reduction, Definition 2.2 and Theorem 3.1
(blueprint: lem-sfb-relative-picard-cube-face-detection).

Proof plan (the numbered steps are the accepted DAG proof):

1. We use the following geometry throughout, also after restricting the base to an open or
extending a residue field. Smoothness, flatness and local finite presentation are stable under
base change and composition by [lem-sfb-stack-chartwise-smooth-etale-calculus]; finite
presentation and separatedness are preserved by products using
[lem-sfb-space-flat-proper-fp-locality, lem-sfb-space-separated-fp-composition]. Thus every
finite product of the $G_i$ is smooth, separated and finitely presented. In case (a) its
structure map is proper by [lem-weil-pbc-proper-composition] and proper base change in the
locality node. Its fibres are geometrically connected: a product projection is open by
[lem-weil-pbc-flat-lfp-open], flatness and local finite presentation above, and surjective by
its identity section, with connected fibres, so a clopen partition of its source descends to a
clopen partition of its connected target (the two images are disjoint open sets); iterate after
every field extension. Each nonempty smooth geometrically connected scheme over a field is
geometrically integral: apply [lem-sbc-smooth-connected-generic-geometry-core] over that field,
and again over every extension field. The identity sections ensure nonemptiness. In particular
all products used below have geometrically integral fibres.

2. Here is the unit test needed for uniqueness. Write $H=G_1\times_SG_2\times_SG_3$. If a unit
$u$ on $P=H$ restricts to $1$ on each single-coordinate axis, pull it back to $H^3$ by
$r(h_1,h_2,h_3)=((h_1)_1,(h_2)_2,(h_3)_3)$. Its restriction to each $H$-axis is $1$. Apply
[lem-sfb-relative-group-unit-axis-factorization] with group $H$ and $n=3$. Step 1 checks its
smoothness, finite-presentation, connected-fibre and proper hypotheses in (a); in (b), normality
implies reducedness since an integrally closed domain has no nonzero nilpotents. Thus $r^*u=1$.
Pull back by $a(g_1,g_2,g_3)=((g_1,e_2,e_3),(e_1,g_2,e_3),(e_1,e_2,g_3))$, for which
$ra=\mathrm{id}_P$, to obtain $u=1$. This test applies over open subschemes and over fields. In
particular two generating sections of the same line that agree on all three faces are equal:
their quotient is a global unit, and each axis is contained in a face.

3. Fix, once on $S$, generating sections $b_i$ of $M|_{F_i}$ supplied by the three triviality
assumptions, with $F_i=j_i(\prod_{h\ne i}G_h)$ interpreted through its parameter scheme. The
section $r_0=b_1|_{(e_1,e_2,e_3)}$ generates the identity pullback. Choose a generating section
$c_k$ of $M$ on each axis by restricting any $b_i$ with $i\ne k$, then multiplying by the
pullback of its identity-value ratio so that $c_k(e)=r_0$. For $\{i,j,k\}=\{1,2,3\}$ define
units $a_{ij}=c_j/(b_i|_{\text{axis }j})$, $a_{ik}=c_k/(b_i|_{\text{axis }k})$ and
$d_i=r_0/b_i(e)$ on the indicated axes or on $S$. Both $a_{ij}$ and $a_{ik}$ have identity value
$d_i$. Replace $b_i$ by $b_i'=b_i\,\pi_j^*a_{ij}\,\pi_k^*a_{ik}/p^*d_i$ on $F_i$. Restriction to
axis $j$ cancels $a_{ik}(e)=d_i$, giving $c_j$; similarly for $k$. The new face sections
therefore agree on every pairwise intersection (an axis) and on the triple intersection. These
operations are pullback, tensor multiplication and division in local rank-one bases, so commute
with every base change.

4. Whenever $M$ has a generating section $t$ over $P_U$, it can be made to equal all three
$b_i'$ there. Let $z_i:P_U\to P_U$ replace coordinate $i$ by its identity, and for a nonempty
subset $I$ write $z_I=\prod_{i\in I}z_i$. Put $f_I=(b_i'/t)|_{F_I}$ with $F_I$ the face where
every coordinate in $I$ is the identity, choosing any $i\in I$; step 3 makes this independent of
$i$. Pull these units to $P_U$ using $z_I$. Define
$$v=\frac{\prod_{|I|=1}z_I^*f_I}{\prod_{|I|=2}z_I^*f_I}\,z_{\{1,2,3\}}^*f_{\{1,2,3\}}.$$ On
$F_j$, the factors indexed by $I$ and $I\cup\{j\}$ cancel whenever $j\notin I$, leaving
precisely $f_{\{j\}}$. Hence $tv$ is a generating section with the prescribed face restrictions.
Here $z_I^*$ on $f_I$ means pullback from the parameter scheme $F_I$. This gives existence of
normalized sections from triviality, using no cubical structure on $M$.

5. First suppose (a). Regard $P$ as $(G_1\times_SG_3)\times_{G_3}(G_2\times_SG_3)$ and write
$q:P\to G_3$. Step 1 and [lem-sc-proper-flat-global-sections] give universal structure-sheaf
pushforward for $G_1$, $G_2$, their product and all their base changes. Apply
[lem-sc-picard-diagonal-locally-closed] to $q,M$ to get an immersion $C\hookrightarrow G_3$
representing the locus where $M$ is pulled back from the parameter. Its finite locally free base
module necessarily has rank one, by restriction along the section $(e_1,e_2,\mathrm{id})$. The
geometrically integral fibres in step 1 let [lem-sc-picard-locus-closed] make $C$ closed. At a
point $c\in C$, $M_c$ is trivial, since a line over a field is free. The two identity slices
$F_1,F_2$ are trivial by hypothesis. Thus [lem-sc-picard-product-open], applied over $G_3$,
gives an open neighbourhood $U$ of $c$ with $M|_{P_U}$ trivial. Its universal property makes
$U\to G_3$ factor through $C$ scheme-theoretically. Consequently $C$ is also open, with its open
subscheme structure, not merely open as a set.

6. The third face says $M|_{G_1\times_SG_2\times_Se_3(S)}$ is trivial, so the universal property
gives a factorization $e_3:S\to C$. For each $s\in S$, the clopen subset $C\cap(G_3)_s$ of the
connected fibre contains $e_3(s)$ and is therefore the whole fibre. Thus the open subscheme $C$
of step 5 has all points of $G_3$, hence equals $G_3$. Its representing property now gives
$M\simeq q^*N$ for a line $N$ on $G_3$. Pull back along $(e_1,e_2,\mathrm{id})$: the left side
is trivial since this map factors through $F_1$, and the right side is $N$. Thus $N$ and $M$ are
trivial. This proves (a), with no connectedness assumption on $S$ and no reducedness assumption
on $S$.

7. For (b), first work over an arbitrary field $k$ with three groups satisfying the geometric
semiabelian hypothesis, and a line $M$ trivial on their identity faces. Apply
[lem-sfb-geometric-semiabelian-split-quotient] successively to the three groups, enlarging the
field each time. After these three finite Galois extensions, take the normal closure of the
composite over $k$; finite separability ensures it is again a finite Galois extension $K/k$. We
have split-torus torsors $q_i:(G_i)_K\to A_i$ with $A_i$ abelian varieties. Their product
$q:P_K\to A_1\times_KA_2\times_KA_3=:A$ is a torsor under the product split torus: flatness,
surjectivity and finite presentation follow from base change and composition, and the torsor
isomorphism is the product of the displayed kernel-action isomorphisms. By step 1 the target $A$
is a smooth separated finite-type $K$-scheme. Apply [lem-sfb-split-torus-torsor-line-pullback]
to obtain an invertible module $N$ on $A$ and an isomorphism $q^*N\simeq M_K$.

8. For $I\subseteq\{1,2,3\}$ let $z_I:A\to A$ set the coordinates in $I$ equal to the
corresponding identity; $z_\varnothing=\mathrm{id}$. Define
$$C(N)=\bigotimes_{I\subseteq\{1,2,3\}}(z_I^*N)^{(-1)^{|I|}},$$ where exponent $-1$ denotes the
dual line. On the $j$-th identity face the factors for $I$ not containing $j$ pair with those
for $I\cup\{j\}$: the two maps agree there, and the exponents are opposite. Evaluation of a line
with its dual gives a trivial line, so all three face restrictions of $C(N)$ are trivial. Each
$q_i$ preserves the identity, hence $qz_I=z_Iq$. The tensor-pullback formula gives
$q^*C(N)\simeq C(q^*N)\simeq C(M_K)$. For each nonempty $I$, $z_I$ on $P_K$ factors through an
identity face, making $z_I^*M_K$ trivial. Therefore $C(M_K)\simeq M_K$ as invertible modules.
The trivializations used in this cancellation need no compatibility.

9. Apply [lem-sc-general-theorem-of-cube] over $K$ to $X=A_1$, $Y=A_2$, $Z=A_3$, the identity
points and the line $C(N)$. The first two varieties are proper and geometrically integral by
step 1, the third is connected, and its identity is a $K$-point at which the third face of
$C(N)$ is trivial by step 8. It follows that $C(N)$ is trivial. Pulling back gives
$M_K\simeq\mathcal O_{P_K}$. Notice that the cube theorem has been applied to the proper abelian
quotient; no properness of $(G_i)_K$ has been asserted.

10. The normalized face sections $b_i'$ of step 3 are defined over $k$. Normalize a generating
section of $M_K$ by step 4, obtaining $t_K$ restricting to their base changes. For every
$\gamma\in\operatorname{Gal}(K/k)$, the canonical descent comparison identifies $\gamma^*M_K$
with $M_K$, and $\gamma^*t_K$ and $t_K$ have identical face restrictions. Step 2, over $K$,
implies they are equal. The algebra isomorphism in
[lem-exc-finite-galois-tensor-decomposition](1), $K\otimes_kK\cong\prod_\gamma K$, identifies
the two pullbacks of $t_K$ on the overlap with exactly these equal sections. Thus the generating
section and its inverse map agree on the fpqc overlap. Apply [lem-pc-fpqc-descent] to the finite
faithfully flat field cover of $P$: its full faithfulness descends the section and its inverse,
giving $M\simeq\mathcal O_P$ over $k$. This proves the field assertion over the original residue
field, including imperfect fields.

11. Return to (b) over the given normal $S$. For every $s\in S$, the residue-field groups
$(G_i)_s$ are smooth separated geometrically connected and geometrically semiabelian. The face
trivializations pull back to their identity faces. Steps 7--10, applied over $\kappa(s)$, prove
$M_s$ trivial over that field, not just after algebraic closure. The smooth separated finitely
presented morphism $P\to S$ has nonempty geometrically connected fibres by step 1. Hence
[lem-sfb-normal-base-fibrewise-line-locality] gives an open cover $\{U_a\}$ of $S$ and lines
$N_a$ with $M|_{P_{U_a}}\simeq p^*N_a$. Pullback along the all-identity section makes $N_a$
isomorphic to $M$ at the identity, which is trivial by any face. Thus $M|_{P_{U_a}}$ is trivial.
This is the only passage from field fibres to a possibly non-Noetherian normal base, and it is
supplied by the cited locality statement.

12. For each $a$, use step 4 to choose a generating section $t_a$ of $M|_{P_{U_a}}$ restricting
to the fixed $b_i'$. On $P_{U_a\cap U_b}$ their quotient is a unit equal to $1$ on all faces,
hence on all axes. The unit test of step 2 gives $t_a=t_b$. The sheaf axiom glues these sections
to a global section $t$; their local inverse maps glue as well, so $t$ generates $M$ globally.
This proves (b). If $S$ is empty the sheaf is uniquely trivial; if one group is the trivial
group, the corresponding face already equals the product, so the same argument includes that
case. No face trivialization, symmetry or cubical structure is added to the conclusion or
hypotheses: choices made in step 3 are only proof data.
-/
theorem relative_picard_cube_face_detection {S : Scheme.{u}} (G : Fin 3 → Over S)
    [∀ i : Fin 3, CommGrpObj (G i)]
    [∀ i : Fin 3, Smooth (G i).hom] [∀ i : Fin 3, IsSeparated (G i).hom]
    [∀ i : Fin 3, LocallyOfFinitePresentation (G i).hom]
    [∀ i : Fin 3, QuasiCompact (G i).hom]
    [∀ i : Fin 3, GeometricallyConnected (G i).hom]
    (hbase : (∀ i : Fin 3, IsProper (G i).hom) ∨
      ((∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)) ∧
        ∀ i : Fin 3, HasSemiabelianGeometricFibres (Grp.mk (G i))))
    (M : (∏ᶜ G).left.Modules) [M.IsInvertible]
    (hfaces : ∀ i : Fin 3, Nonempty
      ((Scheme.Modules.tensorPullback (groupIdentityFace G i).left).obj M ≅
        SheafOfModules.unit _)) :
    Nonempty (M ≅ SheafOfModules.unit _) := by
  sorry

end AlgebraicGeometry
