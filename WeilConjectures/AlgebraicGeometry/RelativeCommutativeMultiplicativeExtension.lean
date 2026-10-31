/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMultiplicativeType
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.RingDiagonalizableGroup
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

import Mathlib.CategoryTheory.Sites.Precoverage
import WeilConjectures.AlgebraicGeometry.FppfAffineRefinement
import WeilConjectures.RingTheory.SubgroupAlgebraCosetPresentation
import WeilConjectures.AlgebraicGeometry.CompleteLocalDiagonalizableFibreHomLift
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.RingTheory.ColimitFlatRingMap
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.AlgebraicGeometry.CommutativeMultiplicativeTypeExtension
import WeilConjectures.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.FiniteFamilyJointSurjectivityStage
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Commutative extensions of relative groups of multiplicative type

Source: Conrad, Reductive group schemes, Corollary B.4.2(2), printed pp.299--301
(blueprint: lem-sfb-relative-commutative-multiplicative-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A commutative affine extension of groups of multiplicative type of finite presentation
is of multiplicative type of finite presentation over an arbitrary scheme. The kernel has
its scheme-theoretic fibre-product construction and its induced group structure.

Source: Conrad, Reductive group schemes, Corollary B.4.2(2), printed pp.299--301
(blueprint: lem-sfb-relative-commutative-multiplicative-extension).

Proof plan (the node's twelve steps):
1. The assertion is local for the fppf topology by the definition of multiplicative type: compose
   a covering on which the assertion holds with its diagonalizing coverings. Restrict to affine
   opens and then successive splitting covers for $D$ and $N$; [lem-trf-fppf-covering-base-change]
   retains the first splitting under the second cover, and [lem-pc-fppf-affine-refinement] lets us
   work on affine charts. Thus assume $S=\operatorname{Spec}A$, $D=D_A(Q)$ and $N=D_A(P)$ with
   $P,Q$ finitely generated. The empty base has nothing to prove. Fppf covering composition is the
   covering axiom of [def-pc-fppf-site].
2. Write $E=\operatorname{Spec}C$. By [lem-sfb-subgroup-algebra-coset-presentation] with $L=0$,
   $A[Q]$ and $A[P]$ are finitely presented $A$-algebras. They are free over $A$ on their
   displayed group bases. Tensoring a module map with either algebra is a direct sum of copies of
   that map, so kernels and images are computed coordinatewise; the nonempty basis also detects
   zero modules. Thus these algebras are flat. The affine flatness dictionary
   [lem-weil-pbc-flat-ring-map-iff-flat-affine] applies. The given locally finitely presented map
   $p$ makes $A[Q]\to C$ finitely presented by
   [lem-weil-pbc-lfp-affine-opens-finite-presentation]; composition
   [lem-weil-pbc-finite-presentation-base-change-composition] makes $C$ finitely presented over
   $A$. The affine map $A[Q]\to C$ is flat, and composition [lem-weil-pbc-flat-ring-map-comp]
   makes $C$ flat over $A$. In particular $E$ is flat of finite presentation over $A$.
3. Use the system of finitely generated integer subrings $A_i\subseteq A$ of
   [lemma-nagata-noetherian-inverse-system-affine]. By [thm-pd-spreading-out], descend $E$, its
   multiplication, inverse, identity, $p:E\to D_A(Q)$ and the specified isomorphism $D_A(P)\simeq
   E\times_{D_A(Q)}S$ to one stage. For affineness choose a finite algebra presentation of $C$ and
   descend its finitely many coefficients, giving affine models $E_i$ from the outset. The group
   diagrams, commutativity, homomorphism diagrams and both inverse equations for the kernel
   isomorphism are finitely many equalities of arrows; the equality clause puts all of them at a
   common later stage. The kernel is modelled by the same fibre product, whose coordinate ring is
   the tensor product of [lem-weil-pbc-fibre-product-affine-spectra]. All schemes in these finite
   diagrams are finitely presented over the base: tensor a finite algebra presentation for the
   fibre products, using [lem-weil-pbc-finite-presentation-base-change-composition]. They are
   affine and hence qcqs by [lem-weil-pbc-affine-scheme-qcqs]. This verifies the limit lemma's
   size and qcqs hypotheses.
4. For the model $p_i:E_i\to D_{A_i}(Q)$, local finite presentation holds: a finite set of algebra
   generators for $A_i[Q]$ can be expressed in the chosen finite presentation of $C_i$, so
   adjoining equations equating those expressions to the generators gives a finite presentation of
   $C_i$ over $A_i[Q]$. Apply [lem-weil-pbc-colimit-flat-ring-map] to the system $A_i[Q]\to C_i$
   to arrange that $p_i$ is flat, using [lem-weil-pbc-flat-ring-map-iff-flat-affine]. Apply
   [lem-weil-pbc-descend-surjective] to arrange surjectivity as well. Its schemes and bases are
   affine qcqs by [lem-weil-pbc-affine-scheme-qcqs]. The kernel is still $D_{A_i}(P)$ at later
   stages. By [lem-weil-pbc-finite-type-over-noetherian], the finite-type integer base is
   Noetherian. It suffices to prove the assertion for these Noetherian split models: a
   diagonalizing fppf covering then pulls back to the original base by
   [lem-trf-fppf-covering-base-change]. Rename the model's base ring $A$.
5. Fix a prime $\mathfrak p\subset A$ and let $R=A_{\mathfrak p}$. It is Noetherian by
   [lem-weil-pbc-localization-noetherian]. Let $B=R^{\mathrm{sh}}$ be the ring of
   [lem-weil-pbc-strict-henselization-triples]; it is local with separably closed residue field
   $k$. It is Noetherian by [lem-sc-strict-henselization-noetherian] and faithfully flat over $R$
   by [lem-sc-strict-henselization-faithfully-flat]. Put $V=\widehat B$. By
   [lem-weil-pbc-adic-completion-noetherian], [lem-weil-pbc-local-completion-local-ring] and
   [lem-weil-pbc-adic-completion-mod-ideal], $V$ is complete Noetherian local with the same
   residue field $k$; it is faithfully flat over $B$ by
   [lem-weil-pbc-local-completion-faithfully-flat]. All the given group structures and kernel
   identifications pull back. The base-changed quotient remains fppf by
   [lem-trf-fppf-covering-base-change]. Thus $E_V$ is flat of finite presentation by the argument
   of step 2 over $V$.
6. Let $K$ be an algebraic closure of $k$. Over $K$, apply
   [lem-sfb-commutative-multiplicative-type-extension] to $E_K\to D_K(Q)$ with kernel $D_K(P)$.
   Its groups are affine of finite type, and its coordinate map is faithfully flat: $p_K$ is the
   base change of the fppf map $p_V$, hence flat and surjective by
   [lem-trf-fppf-covering-base-change]; flatness of the ring map is the affine dictionary, and
   surjectivity gives faithful flatness by
   [lem-weil-pbc-flat-surjective-spectrum-faithfully-flat]. Consequently $E_K\simeq D_K(M)$ for
   some finitely generated abelian $M$. This is also a closed subgroup of a finite power of
   $\mathbf G_m$: choose generators of $M$, hence a surjection $\mathbf Z^t\twoheadrightarrow M$,
   and apply the closed-immersion clause of [lem-sfb-relative-diagonalizable-character-duality].
   Thus $E_k$ satisfies exactly the geometric multiplicative-type hypothesis of
   [lem-sfb-multiplicative-character-antiduality], which gives a splitting over a finite separable
   extension of $k$. Since $k$ is separably closed, [lem-pc-sepclosed-finite-sep-trivial] makes
   that extension trivial. Choose $j_0:D_k(M)\xrightarrow{\sim}E_k$. No perfection or smoothness
   of $k$-groups has been used.
7. Write $p_kj_0:D_k(M)\to D_k(Q)$ as $D_k(a)$ for $a:Q\to M$ using
   [lem-sfb-relative-diagonalizable-character-duality]. Its fppf image is all of $D_k(Q)$. The
   image formula therefore makes $a$ injective: otherwise $k[Q]\to k[\operatorname{im}a]$
   identifies distinct basis vectors and cannot be an isomorphism. The kernel formula identifies
   $\ker(p_kj_0)$ with $D_k(M/a(Q))$. This kernel is the specified $D_k(P)$, so character duality
   gives an isomorphism $M/a(Q)\simeq P$ under which the inclusion of the kernel is $D_k(b)$ for a
   surjection $b:M\twoheadrightarrow P$. Hence $0\to Q\xrightarrow{a}M\xrightarrow{b}P\to0$ is
   exact. Put $q=D_V(a):D_V(M)\to D_V(Q)$ and $i=D_V(b):D_V(P)\hookrightarrow D_V(M)$. The same
   node gives that $q$ is faithfully flat and finitely presented and that its kernel is exactly
   $i(D_V(P))$.
8. Apply [lem-sfb-complete-local-diagonalizable-fibre-hom-lift] to the flat finite-type $V$-group
   $E_V$ and $j_0$. It gives an open and closed immersion $j:D_V(M)\to E_V$. Both $j\circ i$ and
   the specified kernel inclusion $n:D_V(P)\to E_V$ reduce to the same map on $k$. The injectivity
   of the Hom restriction map in that node, now with source $D_V(P)$ and target $E_V$, proves
   $j\circ i=n$. Also $p_V\circ j=q$: both are maps between split diagonalizable groups, and their
   character homomorphisms are locally constant by
   [lem-sfb-relative-diagonalizable-character-duality]. A local ring has connected spectrum, since
   any open containing its closed point contains a basic open $D(f)$ with $f$ a unit and hence
   contains the whole spectrum. Thus each locally constant character map is constant and is
   determined by its special fibre. The two special fibres here are $p_kj_0=D_k(a)$.
9. For any $V$-scheme $T$ and $x\in E_V(T)$, the fppf cover obtained by pulling back $q$ along
   $p_V(x)$ has a section $y$ of $D_V(M)$ with $q(y)=p_V(x)$. On that cover $xj(y)^{-1}$ lies in
   $\ker p_V=N_V$, hence equals $n(z)=j(i(z))$ for a unique $z\in D_V(P)$. Therefore $x=j(i(z)y)$
   fppf-locally. The cover is surjective, so applying this to points shows that every point of
   $E_V$ lies in the image of $j$. Since $j$ is an open immersion, its image is an open subscheme
   isomorphic to its source; surjectivity says this open subscheme is all of $E_V$. Thus $j$ is an
   isomorphism and $E_V=D_V(M)$. This step uses the fppf quotient supplied in step 7, not an
   assumption that every open subgroup containing the special fibre is the whole group.
10. The affine faithfully flat maps $\operatorname{Spec}V\to\operatorname{Spec}B$ and
   $\operatorname{Spec}B\to\operatorname{Spec}R$ are singleton fpqc covers. Indeed
   [lem-weil-pbc-flat-ring-map-iff-flat-affine] and
   [lem-weil-pbc-faithfully-flat-surjective-spectrum] give flatness and surjectivity; over any
   affine open $W$ of the target, its inverse image is the fibre product of $W$ with an affine
   scheme over an affine scheme, hence affine by [lem-weil-pbc-fibre-product-affine-spectra], and
   by surjectivity its image is all of $W$; so they satisfy [def-weil-pbc-fpqc-covering]. Apply
   [lem-sfb-multiplicative-type-fpqc-descent] first to $E_B$, then to $E_R$. Their affineness and
   finite presentation follow by tensoring their finite algebra presentations, and their flatness
   follows from the quotient and the free group algebra exactly as in step 2. We conclude that
   $E_R$ is of multiplicative type for each prime $\mathfrak p$ of the Noetherian model $A$.
11. Spread this conclusion from $R=A_{\mathfrak p}$ to a neighborhood of $\mathfrak p$ as follows.
   By [lem-pc-fppf-affine-refinement], choose finitely many affine charts
   $T_l\to\operatorname{Spec}R$ of a diagonalizing cover, with $E_{T_l}\simeq D_{T_l}(M_l)$. Each
   chart's algebra is finitely presented by [lem-weil-pbc-lfp-affine-opens-finite-presentation].
   The ring $R$ is the directed colimit of $A_f$, $f\notin\mathfrak p$. Descend these finite
   algebra presentations to some $A_f$ and descend the group isomorphisms, their inverses and
   their group diagrams by [thm-pd-spreading-out], using its equality clause for both inverse
   identities. The sources are affine fp schemes, hence qcqs by [lem-weil-pbc-affine-scheme-qcqs].
   Apply [lem-weil-pbc-colimit-flat-ring-map] to make each of the finitely many chart maps flat at
   a common later stage. Apply [lem-weil-pbc-finite-family-joint-surjectivity-stage] to make the
   chart family jointly surjective there. All its maps are lfp because the chart algebras are
   finitely presented. This is a diagonalizing fppf cover of $\operatorname{Spec}A_f$, with
   $f\notin\mathfrak p$. Thus the neighborhoods so obtained cover $\operatorname{Spec}A$, proving
   the assertion for the Noetherian model.
12. Pull the resulting diagonalizing coverings back from the model of steps 3-4 to the original
   split affine base, using [lem-trf-fppf-covering-base-change]. Then compose with the splitting
   and affine-refinement covers of step 1. The fppf covering axiom [def-pc-fppf-site] gives a
   cover of the original $S$ on which $E$ is $D(M)$ with $M$ finitely generated. This is precisely
   the asserted multiplicative type of finite presentation. For the finite-presentation
   terminology, the group algebras are finitely presented by step 2; local finite presentation
   descends across fppf covers by [lem-trf-fppf-covering-is-fpqc] and
   [lem-weil-pbc-fpqc-descend-locally-finite-presentation]. An affine morphism which is lfp is of
   finite presentation: on affine opens of the base it is a map of affine schemes with a finite
   algebra presentation. This proves every claimed case without adding a smoothness, reducedness,
   connectedness or characteristic assumption.
-/
theorem relative_commutative_multiplicativeType_extension
    {S : Scheme.{u}} (E D : Over S) [GrpObj E] [GrpObj D]
    [IsAffineHom E.hom] [IsCommMonObj E]
    (p : E ⟶ D) [IsMonHom p]
    [Flat p.left] [Surjective p.left] [LocallyOfFinitePresentation p.left]
    (hN : IsRelativeMultiplicativeType (Grp.mk (GrpObj.ker p)))
    (hD : IsRelativeMultiplicativeType (Grp.mk D)) :
    IsRelativeMultiplicativeType (Grp.mk E) := by
  sorry

end AlgebraicGeometry
