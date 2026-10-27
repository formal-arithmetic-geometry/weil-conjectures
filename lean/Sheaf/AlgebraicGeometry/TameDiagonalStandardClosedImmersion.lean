/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.FSLogGroupAction
public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.RootsOfUnity.Basic
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import Sheaf.AlgebraicGeometry.FineLogStalkChartSpreading
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteStrictHenselianAlgebraEtaleSection
import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.PieceSection
import Sheaf.TraceFormula.FiniteBaseStrictLocalization
import Sheaf.RingTheory.FilteredColimitFiniteData
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# The strict closed immersion of a tame diagonal chart

Source: ILO, Exposé VI Proposition 3.5(b), p.74, and proof 3.7(b), pp.75--76,
diagrams (3.b)--(3.c) (blueprint: lem-per-tame-diagonal-standard-closed-immersion).

Monoids use multiplicative notation. A pairing on the abelianization tensor the
completion is equivalently a homomorphism from the completion to characters of H.
Ring pushouts are the tensor products of commutative rings. Stalk maps are specified
on every relative pointed étale test; these normalizations uniquely determine them.
Stabilizer actions on stalks use inverse pullback, the canonical left action.
Strictness of the comparison to the Q-chart is expressed by the source Q-chart
condition, which identifies its log structure with the associated pullback log structure.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical ring map on geometric stalks, specified on all pointed relative
étale tests. Every target test pulls back to a source test, so these equations uniquely
determine the map. Source: ILO VI 3.7(b), (3.b)
(blueprint: lem-per-tame-diagonal-standard-closed-immersion). -/
def IsPointedRingStalkMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (t : Spec (.of Ω) ⟶ Y)
    (φ : strictLocalRing Y t →+* strictLocalRing X s) : Prop :=
  s ≫ f = t ∧ ∀ (W : Y.Etale) (V : X.Etale)
    (w : (Scheme.pointSmallEtale t).fiber.obj W)
    (v : (Scheme.pointSmallEtale s).fiber.obj V)
    (k : V.left ⟶ W.left), k ≫ W.hom = V.hom ≫ f → v.left ≫ k = w.left →
    ∀ z : Γ(W.left, ⊤),
      φ (strictLocalGerm Y t W w z) = strictLocalGerm X s V v (k.appTop z)

/-- The canonical log-stalk map, normalized on every relative pointed test.
This presents the actual map, including its action on units, without choosing an
unrelated monoid action. Source: ILO VI 3.4 and 3.7(b)
(blueprint: lem-per-tame-diagonal-standard-closed-immersion). -/
def EtaleLogHom.IsPointedStalkMap {X Y : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X.scheme) (t : Spec (.of Ω) ⟶ Y.scheme)
    (φ : Y.logStructure.toEtalePrelogStructure.stalk t →*
      X.logStructure.toEtalePrelogStructure.stalk s) : Prop :=
  s ≫ f.base = t ∧ ∀ (W : Y.scheme.Etale) (V : X.scheme.Etale)
    (w : (Scheme.pointSmallEtale t).fiber.obj W)
    (v : (Scheme.pointSmallEtale s).fiber.obj V)
    (k : V.left ⟶ W.left) (hk : k ≫ W.hom = V.hom ≫ f.base),
    v.left ≫ k = w.left → ∀ z : Y.logStructure.monoidSheaf.obj.obj (op W),
      φ (Y.logStructure.toEtalePrelogStructure.germ t W w z) =
        X.logStructure.toEtalePrelogStructure.germ s V v (f.sectionMap W V k hk z)

/-- The lattice L is the kernel of the character pairing on Q's group completion.
Source: ILO VI 3.7(b), P' preceding (3.b)
(blueprint: lem-per-tame-diagonal-standard-closed-immersion). -/
def tameDiagonalLattice {Q : Type u} [CommMonoid Q] {H : Type v} [Group H]
    {A : Type u} [CommRing A] {n : ℕ}
    (χ : Algebra.GrothendieckGroup Q →* (H →* rootsOfUnity n A)) :
    Subgroup (Algebra.GrothendieckGroup Q) := χ.ker

/-- P is Q intersected with L, using the canonical completion map.
Source: ILO VI 3.7(b), P preceding (3.b)
(blueprint: lem-per-tame-diagonal-standard-closed-immersion). -/
def tameDiagonalMonoid {Q : Type u} [CommMonoid Q] {H : Type v} [Group H]
    {A : Type u} [CommRing A] {n : ℕ}
    (χ : Algebra.GrothendieckGroup Q →* (H →* rootsOfUnity n A)) : Submonoid Q :=
  (tameDiagonalLattice χ).toSubmonoid.comap (Algebra.GrothendieckGroup.of (M := Q))

/-- A realization of the prescribed strict-local charts on pointed étale neighbourhoods.
The invariant log structure N need not be fs globally. Its displayed P-chart and the
source Q-chart are required on every geometric stalk, not only the marked points.
The latter is exactly strictness relative to the target's associated Q-chart.
Source: ILO VI 3.5(b), 3.7(b), (3.b)--(3.c)
(blueprint: lem-per-tame-diagonal-standard-closed-immersion). -/
structure TameDiagonalChartRealization {G : Type v} [Group G]
    {X : FineSaturatedLogScheme.{u}} (action : FSLogGroupAction G X)
    {Y : Scheme.{u}} (q : X.scheme ⟶ Y) (N : EtaleLogStructure Y)
    (D : action.InvariantDirectImage q N)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
    {Q : Type u} [CommMonoid Q] (P : Submonoid Q)
    (a : Q →* X.logStructure.toEtalePrelogStructure.stalk t)
    (b : P →* strictLocalRing Y (t ≫ q)) where
  V : X.scheme.Etale
  W : Y.Etale
  v : (Scheme.pointSmallEtale t).fiber.obj V
  w : (Scheme.pointSmallEtale (t ≫ q)).fiber.obj W
  lift : V ⟶ logInvariantTest q W
  pointed : v.left ≫ lift.left ≫ pullback.fst W.hom q = w.left
  chartX : Q →* X.logStructure.monoidSheaf.obj.obj (op V)
  chartY : P →* N.monoidSheaf.obj.obj (op W)
  source_chart : X.logStructure.IsChart V chartX
  target_chart : N.IsChart W chartY
  source_germ : (X.logStructure.toEtalePrelogStructure.germ t V v).hom.comp chartX = a
  target_germ : (strictLocalGerm Y (t ≫ q) W w).hom.toMonoidHom.comp
    ((N.alpha.app (op W)).hom.comp chartY) = b
  compatible : ∀ p : P,
    X.logStructure.monoidSheaf.obj.map lift.op (D.pullbackMap W (chartY p)) = chartX p.val
  square : (lift.left ≫ pullback.fst W.hom q) ≫ N.chartToSpec W chartY =
    X.logStructure.chartToSpec V chartX ≫
      Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ P.subtype))

/-- The canonical chart comparison, with the log structure associated to Q on its
target. Its source log structure is its pullback by `source_chart`.
Source: ILO VI 3.7(b), (3.c)
(blueprint: lem-per-tame-diagonal-standard-closed-immersion). -/
noncomputable def TameDiagonalChartRealization.comparison {G : Type v} [Group G]
    {X : FineSaturatedLogScheme.{u}} {action : FSLogGroupAction G X}
    {Y : Scheme.{u}} {q : X.scheme ⟶ Y} {N : EtaleLogStructure Y}
    {D : action.InvariantDirectImage q N}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {t : Spec (.of Ω) ⟶ X.scheme}
    {Q : Type u} [CommMonoid Q] {P : Submonoid Q}
    {a : Q →* X.logStructure.toEtalePrelogStructure.stalk t}
    {b : P →* strictLocalRing Y (t ≫ q)}
    (c : TameDiagonalChartRealization action q N D t P a b) :
    c.V.left ⟶ pullback (N.chartToSpec c.W c.chartY)
      (Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ P.subtype))) :=
  pullback.lift (c.lift.left ≫ pullback.fst c.W.hom q)
    (X.logStructure.chartToSpec c.V c.chartX) c.square

/-- The tame diagonal chart comparison is a strict closed immersion, and its strict-local
ring comparison is surjective with the prescribed value on every pure tensor.
Source: ILO VI Proposition 3.5(b), p.74, and proof 3.7(b), pp.75--76
(blueprint: lem-per-tame-diagonal-standard-closed-immersion).

Proof:
1. Work over an affine open neighbourhood of the image of $\bar y$ in $Y$. Its finite inverse
image in $X$ is quasi-compact and locally Noetherian, hence Noetherian. The finite-quotient
strict-local identification gives $N_{\bar y}=M_{\bar x}^H$, respecting units and structural maps,
as well as the assumed $B=A^H$ and finiteness. The strict local rings $A,B$ are strictly henselian
local and Noetherian: apply Noetherianity of strict henselization to the Noetherian local rings at
the underlying points. Since $H$ fixes the geometric point, it fixes the residue field of $A$: the
residue-field embedding into the geometric-point field is injective and commutes with the action.
Uses: lem-per-finite-quotient-strict-local-invariants, lem-weil-pbc-strict-henselization-local-
structure, lem-sc-strict-henselization-noetherian.
2. Fine-log chart spreading represents the prescribed germ $a$ by a chart on a pointed etale
neighbourhood. Pull that neighbourhood back to $\operatorname{Spec}A$. Its image contains the
closed point; etale maps are open, and an open subset of a local spectrum containing its closed
point is the whole spectrum. Hence this etale map is surjective. The strict-henselian etale-
section lemma, with the finite algebra $A$ over itself, gives a section. Pulling back the chart
along it represents $a$ on $\operatorname{Spec}A$. Equivariance there is the assumed equality in
the geometric stalk.
Uses: lem-trf-fine-log-stalk-chart-spreading, lem-weil-pbc-etale-morphism-open-map, lem-sbc-
finite-strict-henselian-algebra-etale-section, def-trf-fs-log-blowup.
3. The pairing gives $nQ^{\rm gp}\subset L$. Choose monoid generators $q_1,\ldots,q_r$ of $Q$. For
any $p\in P$, write its generator coefficients as $nc_i+e_i$, $0\le e_i<n$. The remainder $\sum
e_iq_i$ still lies in $L$, because $nQ\subset L$. Thus $P$ is generated by the $nq_i$ and the
finitely many remainders lying in $L$. It is integral and sharp as a submonoid of $Q$, and
saturated in its group completion: if $mv\in P$ and $v\in P^{\rm gp}$, then $v\in L$, and
saturation of $Q$ gives $v\in Q$. Therefore $P$ is fs. For $v\in L$, write $v=u-w$ with $u,w\in
Q$; then $v+nw=u+(n-1)w\in P$ and $nw\in P$, so $P^{\rm gp}=L$. At the closed invariant stalk, a
fixed section has the unique form $u a(q)$ with $u\in A^\times$. Reducing $h(u)\chi_q(h)=u$ to the
residue field forces $\chi_q(h)=1$: if a root $z\in\mu_n(A)$ reduces to 1, then
$(z-1)(1+\cdots+z^{n-1})=0$ and the second factor is a unit, so $z=1$. Hence $M_{\bar x}^H=P\oplus
B^\times$. This is only a closed-stalk calculation; the neighbourhood chart will be proved below.
Uses: def-trf-fs-log-blowup, lem-per-finite-quotient-strict-local-invariants.
4. Put $D=B[a(u):u\in Q]\subseteq A$, the image of $\phi:B\otimes_{\mathbf Z[P]}\mathbf Z[Q]\to
A$. The relation $a(p)=b(p)$ for $p\in P$ makes $\phi$ well-defined. For $x\in A$, set
$R(x)=n^{-1}\sum_{h\in H}h(x)$. The inverse of $n$ is invariant, so $R(x)\in B$. Triviality on
$A/I$ gives $x-R(x)=n^{-1}\sum_h(x-h(x))\in I$. Therefore $A=B+I$. This is the source's surjection
onto the stratum, proved by the explicit averaging formula.
Uses: def-per-fs-log-smooth-etale.
5. Choose nonzero monoid generators $q_1,\ldots,q_r$ of $Q$, with the empty list if $Q=0$. Then
$I=(a(q_1),\ldots,a(q_r))A$, since a nonzero monoid element is a sum containing a generator. Each
$a(q_i)$ is in $\mathfrak m_A$, since $Q$ identifies with the sharp characteristic at the point.
Also $a(q_i)^n=a(nq_i)$ is invariant: each character value has $n$-th power one. Hence
$a(q_i)^n\in B\cap\mathfrak m_A=\mathfrak m_B$. Here an invariant element invertible in $A$ has
invariant inverse, which proves the equality of maximal ideals by intersection. If $r>0$, take
$N=r(n-1)+1$; every product of $N$ generators contains one at least $n$ times, so
$I^N\subseteq\mathfrak m_BA$. If $r=0$, $I=0$ and take $N=1$.
Uses: def-trf-fs-log-blowup.
6. Prove $A=D+I^k$ by induction on $k\ge1$. For $k=1$, use $A=B+I$ and $B\subseteq D$. Write an
element of $I^k$ as a finite sum of $k$-fold products of the $a(q_i)$ with coefficients $c\in A$.
Write each $c=b+i$ using $A=B+I$. The terms with coefficient $b\in B$ lie in $D$; those with
coefficient $i\in I$ lie in $I^{k+1}$. Thus $I^k\subseteq D+I^{k+1}$ and the induction follows.
The exponent of Step 5 gives $A=D+\mathfrak m_BA$.
7. The image $D$ is a $B$-submodule of the finite $B$-module $A$, and its image in $A/\mathfrak
m_BA$ is all of that quotient. The submodule form of local Nakayama gives $D=A$, so $\phi$ is
surjective. The finite module in this application is $A$, exactly as assumed in the item; no
finiteness of the submodule $D$ is needed.
Uses: lem-weil-pbc-nakayama-local-generators.
8. By the chart-square construction the strict-local comparison is $\operatorname{Spec}\phi$,
whose pullback takes $b\otimes z^u$ to $b\,a(u)$. Surjectivity makes this a closed immersion by
the affine characterization. The target has the log structure associated to its chart $Q$. Pulling
it back gives the log structure associated to $a:Q\to A$, namely the given log structure on
$\operatorname{Spec}A$; hence the comparison is strict.
Uses: def-per-fs-log-smooth-etale, def-weil-closed-immersion, def-trf-fs-log-blowup.
9. First spread a compatible prelog chart, without assuming $N$ is fine. Represent $a$ on a
pointed source neighbourhood by fine-log chart spreading. Finite-pointed-piece refinement supplies
a finite clopen source piece $X_0$ over an affine pointed etale $Y_0$, mapping to that
neighbourhood. Arrange that the pieces are permuted by $G$ as the geometric fibre is: over
$\operatorname{Spec}B$ this follows from finite-base strict localization, and the finitely many
equalities of their idempotents descend by finite-data descent. The chosen piece is then
$H$-stable and the full pullback is the disjoint union of its $G/H$ translates. The finite
identities $h(a(q_i))=\chi_{q_i}(h)a(q_i)$ for the chart generators and $h\in H$ hold at its
marked stalk. Represent their equality on a common pointed etale neighbourhood and use finite-
piece refinement again; the idempotent permutation identities persist under base change. Represent
the finitely many root coefficients and their relations on $Y_0$ as well, including inverses of
the differences of distinct roots and of $n$. The resulting chart on $X_0$ is diagonal under $H$.
On each etale test over $Y_0$, restriction to the chosen piece identifies $G$-invariant sections
with $H$-invariant sections. Thus $\mathcal O_{Y_0}=(f_*\mathcal O_{X_0})^H$ and
$N|_{Y_0}=(f_*M_{X_0})^H$. In particular the fixed sections $a(p)$ define a prelog map $b:P\to
N|_{Y_0}$, with the prescribed germ.
Uses: lem-trf-fine-log-stalk-chart-spreading, def-weil-pbc-geometric-stalks, lem-sbc-finite-
pointed-piece-refinement, lem-trf-finite-base-strict-localization, lemma-nagata-filtered-colimit-
finite-data, lemma-weil-pbc-affine-neighbourhood-cofinal, lem-sbc-strict-local-roots-of-unity.
10. Write $Y_0=\operatorname{Spec}B_0$, $X_0=\operatorname{Spec}A_0$. Finite-base strict
localization identifies $X_0\times_{Y_0}\operatorname{Spec}B$ with $\operatorname{Spec}A$: the
chosen clopen piece contains exactly the chosen geometric-fibre point. Its comparison becomes
$\phi$. Choose finite $B_0$-module generators $t_1,\ldots,t_s$ of $A_0$. Surjectivity of $\phi$
gives finite expressions $t_j=\sum_u b_{ju}a(u)$ in $A$, with $b_{ju}\in B$. Represent the
finitely many coefficients on a common affine pointed etale refinement of $Y_0$. The differences
$t_j-\sum_u b_{ju}a(u)$ have zero geometric germ, so vanish on a common pointed etale
neighbourhood of the chosen point of the finite source, by the stalk definition. Apply finite-
pointed-piece refinement to that finite source and this neighbourhood. Denote the new affine base
and its chosen piece by $Y',X'$. All these identities hold on $X'$. The previous chosen piece has
only one point in the marked geometric fibre. Its new chosen clopen piece is H-stable after
removing base images of the other pieces: the morphism from each discarded clopen piece to the
base is finite, hence proper by [lem-weil-pbc-finite-proper], and has closed image by [lem-weil-
pbc-proper-closed-image]; these images miss the marked point. Thus the quotient and diagonal
identities of Step 9 persist.
Uses: lem-trf-finite-base-strict-localization, def-weil-pbc-geometric-stalks, lem-sbc-finite-
pointed-piece-refinement, lemma-weil-pbc-affine-neighbourhood-cofinal, lem-weil-pbc-finite-proper,
lem-weil-pbc-proper-closed-image.
11. The images of the $t_j$ still generate $\Gamma(X',\mathcal O_{X'})$ over $\Gamma(Y',\mathcal
O_{Y'})$: scalar extension preserves their generating expressions, and a clopen piece is the
quotient by an idempotent ideal, which also preserves them. The identities of Step 10 put these
generators in the image of the comparison ring map. It is therefore surjective, so $X'\to
Y'\times_{\operatorname{Spec}\mathbf Z[P]}\operatorname{Spec}\mathbf Z[Q]$ is a closed immersion.
Pullback of its chart $Q$ is $a$ on $X'$, proving strictness as in Step 8. Both structural maps to
$X,Y$ are pointed etale neighbourhoods by Steps 9–10. The strict-local ring formula is exactly
$\phi$.
Uses: def-weil-closed-immersion, def-per-fs-log-smooth-etale, def-trf-fs-log-blowup.
12. Retain the finite $H$-quotient $f:X'\to Y'$ and its diagonal chart from Steps 9–11. Its ring
of functions is generated over that of $Y'$ by the monomials $a(q)$. The action therefore factors,
on functions and on the chart log structure, through the finite abelian group $E$ which is the
image of $H\to\operatorname{Hom}(Q^{\rm gp},\mu_n(A))$. Its exponent divides $n$. Fix any
geometric point $t$ of $X'$ over $s$ of $Y'$, and let $K\le E$ be its stabilizer. Put $F=\{q\in
Q:a(q)\text{ is a unit at }t\}$. It is a face. An element of $E$ fixes $t$ exactly when it fixes
all nonzero monomial values at $t$, because the monomials generate the algebra over the base. Thus
$K=\bigcap_{f\in F}\ker\chi_f$. The chosen root differences are units, so reduction at $t$ does
not identify distinct root values. The finite-quotient strict-local identification at $(t,s)$
gives $N_s=M_t^K$ and $(\mathcal O_{X',t}^\times)^K=\mathcal O_{Y',s}^\times$. Passing from $H$ to
$E$ discards only an action kernel and does not change these invariants.
Uses: lem-per-finite-quotient-strict-local-invariants, def-trf-fs-log-blowup.
13. Let $D_F$ be the subgroup of characters of $E$ generated by $\chi_f$ for $f\in F$. Apply
finite-character annihilator duality to $E$ with target the original strict local ring $A$. Its
root hypotheses hold: $\mu_n(A)$ is cyclic of order $n$; for $e=\exp(E)\mid n$, its $e$-torsion is
cyclic with a primitive element obtained by raising a primitive $n$-th root to $n/e$. Any $e$-th
root is an $n$-th root. Since $K=D_F^\perp$, the cited duality gives $K^\perp=D_F$. Therefore if
$\chi_q$ is trivial on $K$, there are $f_1,f_2\in F$ with $\chi_{q+f_1-f_2}=1$ on $E$. In that
case $p=q+f_1+(n-1)f_2$ belongs to $P$ and $p-q\in F$. This is the precise character extension
needed at a generization, rather than an inference from the closed stalk alone.
Uses: lem-per-finite-character-annihilator-duality, lem-sbc-strict-local-roots-of-unity.
14. Every section of $M_t$ is represented by $u a(q)$, $u\in\mathcal O_{X',t}^\times$, $q\in Q$,
by the chart definition. If it is $K$-invariant, integrality of the fs log monoid permits
cancellation of $a(q)$, so reduction of $h(u)\chi_q(h)=u$ to the residue field forces
$\chi_q|_K=1$, since $K$ fixes that residue field and distinct roots remain distinct. Step 13
supplies $p\in P$ with $p=q+f$, $f\in F$. Then $u a(q)=(u/a(f))a(p)$. The new coefficient is a
unit and is $K$-fixed because both the section and $a(p)$ are fixed. It belongs to $\mathcal
O_{Y',s}^\times$ by Step 12. Consequently the log structure associated to $b:P\to\mathcal O_{Y'}$
maps surjectively to $N$ at every geometric stalk $s$. This includes points whose stabilizer is
smaller than the original $H$.
Uses: def-trf-fs-log-blowup, lem-per-finite-quotient-strict-local-invariants.
15. For injectivity put $F_P=P\cap F$. One has $L\cap F^{\rm gp}=F_P^{\rm gp}$: if $v=f_1-f_2\in
L$ with $f_i\in F$, then $v+nf_2=f_1+(n-1)f_2$ and $nf_2$ both lie in $F_P$. If $u a(p)=v a(p')$
in $M_t$ for $p,p'\in P$ and base units $u,v$, the chart by $Q$ gives $p-p'\in F^{\rm gp}$. It
lies in $L$ as well, hence in $F_P^{\rm gp}$. Write $p-p'=e_1-e_2$ with $e_i\in F_P$. The
associated-log relations for $P$ identify $p$ and $p'$ using the base units $b(e_i)$; the equality
of the remaining unit coefficients follows after mapping into the source units, where the base-
unit inclusion is injective. Thus the map is also injective on every geometric stalk. Geometric
stalks detect isomorphisms of etale sheaves, so $b$ is a chart of the actual invariant log
structure $N$ on $Y'$. It is an fs chart by Step 3. This completes the target-chart assertion and,
together with Steps 8 and 11, the required strict closed immersion without citing the local Kummer
quotient node.
Uses: def-trf-fs-log-blowup, lem-weil-pbc-sets-etale-iso-on-geometric-stalks.
-/
theorem exists_tameDiagonal_standard_closedImmersion
    {G : Type v} [Group G] [Finite G] (X : FineSaturatedLogScheme.{u})
    (action : FSLogGroupAction G X) {Y : Scheme.{u}} [IsNoetherian Y]
    (q : X.scheme ⟶ Y) (hquot : IsAdmissibleFiniteSchemeQuotient action.baseAction q)
    (N : EtaleLogStructure Y) (D : action.InvariantDirectImage q N)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ t ≫ (action.baseAction g).hom = t)
    (ρ : H →* (strictLocalRing X.scheme t ≃+* strictLocalRing X.scheme t))
    (logActionStalk : H →* MulAut (X.logStructure.toEtalePrelogStructure.stalk t))
    (hρ : ∀ h : H, IsPointedRingStalkMap (action.baseAction h.val⁻¹).hom t t
      (ρ h).toRingHom)
    (hlogActionStalk : ∀ h : H, (action.logMap h.val⁻¹).IsPointedStalkMap t t
      (logActionStalk h).toMonoidHom)
    (i : strictLocalRing Y (t ≫ q) →+* strictLocalRing X.scheme t)
    (hi : IsPointedRingStalkMap q t (t ≫ q) i)
    (hinj : Function.Injective i)
    (hinvariants : ∀ z : strictLocalRing X.scheme t,
      (∀ h : H, ρ h z = z) ↔ ∃ y : strictLocalRing Y (t ≫ q), i y = z)
    (hfinite : i.Finite) (hn : IsUnit (Nat.card H : strictLocalRing X.scheme t))
    {Q : Type u} [CommMonoid Q] (hQ : IsFineSaturatedMonoid Q)
    (hsharp : ∀ z : Q, IsUnit z → z = 1)
    (a : Q →* X.logStructure.toEtalePrelogStructure.stalk t)
    (ha : X.logStructure.IsStalkChart t a)
    (hcharacteristic : Function.Bijective (Associates.mkMonoidHom.comp a))
    (hfixed : ∀ (h : H) (m : X.logStructure.toEtalePrelogStructure.stalk t),
      Associates.mk (logActionStalk h m) = Associates.mk m)
    (χ : Algebra.GrothendieckGroup Q →*
      (H →* rootsOfUnity (Nat.card H) (strictLocalRing X.scheme t)))
    (hroots : ∀ (h : H) (ζ : rootsOfUnity (Nat.card H) (strictLocalRing X.scheme t)),
      ρ h (ζ.val : strictLocalRing X.scheme t) = (ζ.val : strictLocalRing X.scheme t))
    (hdiagonal : ∀ (h : H) (r : Q), logActionStalk h (a r) =
      X.logStructure.unitsIn t (χ (Algebra.GrothendieckGroup.of r) h).val * a r)
    (hstratum : ∀ (h : H) (z : strictLocalRing X.scheme t),
      ρ h z - z ∈ X.logStructure.nonunitIdeal t) :
    ∃ b : tameDiagonalMonoid χ →* strictLocalRing Y (t ≫ q),
      i.toMonoidHom.comp b =
        (X.logStructure.toEtalePrelogStructure.stalkAlpha t).comp
          (a.comp (tameDiagonalMonoid χ).subtype) ∧
      (∃ φ : pushout
          (CommRingCat.ofHom (MonoidAlgebra.lift ℤ (strictLocalRing Y (t ≫ q))
            (tameDiagonalMonoid χ) b).toRingHom)
          (CommRingCat.ofHom
            (MonoidAlgebra.mapDomainRingHom ℤ (tameDiagonalMonoid χ).subtype)) ⟶
          strictLocalRing X.scheme t,
        Function.Surjective φ ∧
        ∀ (y : strictLocalRing Y (t ≫ q)) (r : Q),
          φ (pushout.inl
              (CommRingCat.ofHom (MonoidAlgebra.lift ℤ (strictLocalRing Y (t ≫ q))
                (tameDiagonalMonoid χ) b).toRingHom)
              (CommRingCat.ofHom
                (MonoidAlgebra.mapDomainRingHom ℤ (tameDiagonalMonoid χ).subtype)) y *
            pushout.inr
              (CommRingCat.ofHom (MonoidAlgebra.lift ℤ (strictLocalRing Y (t ≫ q))
                (tameDiagonalMonoid χ) b).toRingHom)
              (CommRingCat.ofHom
                (MonoidAlgebra.mapDomainRingHom ℤ (tameDiagonalMonoid χ).subtype))
              (MonoidAlgebra.single r 1)) =
            i y * X.logStructure.toEtalePrelogStructure.stalkAlpha t (a r)) ∧
      ∃ c : TameDiagonalChartRealization action q N D t (tameDiagonalMonoid χ) a b,
        IsClosedImmersion c.comparison := by
  sorry

end AlgebraicGeometry
