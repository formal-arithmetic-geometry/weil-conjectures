/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Data.Fin.Tuple.Basic
import Sheaf.Topology.ProfiniteMetricFunctionQuotients
import Sheaf.NumberTheory.Padics.CountableClosedFiniteCover
import Sheaf.NumberTheory.Padics.NormOneFiniteSubfieldProjection
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Descent of continuous scalar cochain boundaries from the completion

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
agent-formulated scalar analytic input; an exact norm-topological reference is WANTED.
(blueprint: lem-sfb-parameter-cochain-completion-boundary-descent).

The differential is displayed pointwise on all continuous functions. Its last face is
`Fin.contractNth` at the last index, which drops the last coordinate. No closure of
coboundaries, locally constant restriction, or derived-invariants comparison is used.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace ContinuousCohomology

/-- A continuous cocycle that has a continuous primitive in the norm completion has
continuous primitives over a finite jointly surjective family of profinite parameter sets.
The degree is `n + 1`, so `n = 0` includes degree one and its zero degree-zero differential.
The extending norm is specified by `NormedAlgebra`; no completeness of Ω is assumed.

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
agent-formulated scalar analytic input; exact reference WANTED
(blueprint: lem-sfb-parameter-cochain-completion-boundary-descent).

Proof (the thirteen steps of the DAG):
1. If $S=\varnothing$, use the empty family. If $n=1$, then $db=d^0b=0$; the embedding $\iota$
is injective, so $z=0$, and the zero degree-zero cochain is already a primitive. Henceforth
$S\ne\varnothing$ and $n\geq2$. We construct a primitive on $S$ itself; the required cover will
be the single identity map. Identify $\Omega$ with its isometric image in $B=\widehat\Omega$
using [lem-sfb-normed-field-completion]. The strong triangle inequality holds in $\Omega$: any
two algebraic elements lie in one finite extension, where [lem-weil-l-adic-extension-absolute-
value] applies. It holds in $B$ by passage to limits, as does scalar norm homogeneity over
$\mathbf Q_\ell$.

2. Read the profinite set $S$ as a compact Hausdorff totally disconnected space; it has a basis
of clopen sets by [lem-weil-pbc-profinite-clopen-basis]. By [lem-sfb-profinite-group-open-
normal-subgroup-basis], the original compact Hausdorff totally disconnected group $G$ has a
neighbourhood basis of open normal subgroups. Thus $S$ and $G$ satisfy the hypotheses of the
next input. Apply [lem-sfb-profinite-metric-function-quotients], with $r=n$ and the product
metric target $\Omega\times B$, to
$$F(s;g_1,\ldots,g_n)=(z(s;g_1,\ldots,g_n),b(s;g_1,\ldots,g_{n-1})).$$
It gives continuous
surjections $p:S\to S_0$, $q:G\to G_0$, the latter a homomorphism, with $S_0,G_0$ metrizable
profinite. The first component descends $z$; evaluating the last group argument at $1$ in the
second component descends $b$. Its independence of that argument follows by surjectivity of
$p,q$. Surjectivity on all powers shows $dz_0=0$ and $db_0=\iota z_0$. A primitive on these
quotients pulls back to the original spaces. Rename them $S,G,z,b$ in the rest of the proof.

3. Apply [lem-sfb-algcl-countable-closed-finite-cover] with $E=\mathbf Q_\ell$ and choose
increasing closed finite fields $F_N$ covering $\Omega$. Set
$$f(s;g_0,\ldots,g_n)=z(s;g_0^{-1}g_1,\ldots,g_{n-1}^{-1}g_n).$$
For each $s$, the closed sets
$f(s,-)^{-1}(F_N)$ cover the nonempty compact Hausdorff $G^{n+1}$. By [lem-sfb-baire-closed-
cover-interior] one has nonempty interior. A product neighbourhood in that interior contains
$Ha_0\times\cdots\times Ha_n$ for some open normal subgroup $H$: intersect finitely many
translated neighbourhoods of $1$ and apply [lem-sfb-profinite-group-open-normal-subgroup-basis].
Thus every $s$ has a certificate consisting of such a rectangle and a field $F_N$. No
neighbourhood of $s$ is asserted to have that certificate.

4. A compact metric profinite space has a countable clopen basis: for each positive integer $t$,
choose clopen neighbourhoods of diameter $<2^{-t}$ and take a finite subcover. The union of
these finite covers is a basis. Every clopen subset is a finite union of basis members, by
compactness. Apply this to $G$: there are countably many open subgroups and their cosets, hence
countably many coset rectangles. Enumerate all rectangle/field pairs with nonempty certificate
sets as $(B_j,N_j)$, $j\geq1$, repeating entries if the list is finite, and put
$$A_j=\{s:f(s,B_j)\subseteq F_{N_j}\}.$$
Each $A_j$ is closed, as an intersection of inverse
images of the closed field $F_{N_j}$ under continuous evaluation maps. The preceding step gives
$S=\bigcup_{j\geq1}A_j$, with every $A_j$ nonempty. Write $B_j=H_ja_{j,0}\times\cdots\times
H_ja_{j,n}$. Each $H_j$ has finite index: its disjoint open cosets cover compact $G$, hence
admit a finite subcover.

5. Choose finite clopen partitions $\mathcal P_t$ of $S$ refining each other, with all atom
diameters $<2^{-t}$. Obtain them from finite clopen covers at each scale by taking their finite
Boolean refinements and then common refinements. Map $S$ to $D=\prod_t\mathcal P_t$ by its atom
at each level. This map $e$ is continuous. It is injective because the mesh tends to zero; its
inverse on its image is continuous because fixing the $t$th coordinate confines the inverse to
one atom of diameter $<2^{-t}$. For each $j$, $e(A_j)$ is compact and closed in the Hausdorff
space $D$: a point outside this compact set has neighbourhoods separating it from each of its
points, and finitely many of the latter neighbourhoods cover the set. Apply [lem-sfb-countable-
discrete-product-closed-retraction] to the nonempty closed subset $e(A_j)\subseteq D$. Restrict
the resulting map to $e(S)$ and compose with $e^{-1}$. This gives a continuous $\rho_j:S\to A_j$
fixing $A_j$ pointwise.

6. For $i\geq1$ let $U_{j,i}$ be the union of the atoms of $\mathcal P_i$ meeting $A_j$. These
are clopen, decrease with $i$, and have intersection $A_j$: a point outside the closed $A_j$ has
positive distance from it and is eventually in an atom disjoint from it. Let $k_i(s)$ be the
least $j\leq i$ with $s\in U_{j,i}$, or $1$ when none exists. This is locally constant with
finite range. For each $s$, let $j(s)$ be the least $j$ with $s\in A_j$. Eventually all $j<j(s)$
are excluded from $U_{j,i}$, while $s\in U_{j(s),i}$ always. Thus $k_i(s)=j(s)$ for all
sufficiently large $i$.

7. For each rectangle $B_j$ choose the operator $T_j$ of [lem-sfb-finite-index-rectangle-
primitive-operator], with $C_j=|[G:H_j]|_\ell^{-1}$. It works for every coefficient field used
below and for profinite parameter families. In particular, for every cocycle $c$ with
homogeneous function zero on $B_j$, one has $dT_jc=c$. All $C_j$ are finite, even when the
subgroup index is divisible by $\ell$. Put $D_t=\max(1,C_1,\ldots,C_t)$ for $t\geq1$ and
$\delta_i=2^{-i}/D_{i+1}$ for $i\geq0$.

8. For every $N$, [lem-sfb-norm-one-finite-subfield-projection] gives a $\mathbf Q_\ell$-linear
contraction $p_N:\Omega\to F_N$ fixing $F_N$. The finite field $F_N$ is complete by [lem-weil-l-
adic-extension-complete]. Apply [lem-sfb-dense-subspace-contractive-extension] to the dense
normed $\mathbf Q_\ell$-subspace $\Omega\subseteq B$, with target $F_N$. It extends $p_N$ to a
linear contraction $P_N:B\to F_N$, still fixing $F_N$. Density here is the defining density of
the canonical inclusion in the metric completion; no continuous retraction $B\to\Omega$ is used.

9. For each $i\geq0$, compactness of the images of $z$ and $b$ gives finite $\delta_i$-nets with
centres in $\Omega$ (use its density in $B$ for the image of $b$). Choose strictly increasing
$L_i\geq i$ so that $F_{L_i}$ contains all these centres and $L_i\geq N_j$ for $j\leq i+1$. This
is possible since the increasing $F_N$ cover $\Omega$. Put $P_i=P_{L_i}$. If $a\in F_{L_i}$ is a
chosen centre within $\delta_i$ of $x$, contractivity and $P_ia=a$ give
$$|P_ix-x|\leq\max(|P_i(x-a)|,|a-x|)\leq\delta_i.$$
Consequently $\|P_iz-z\|_\infty\leq\delta_i$
and $\|P_ib-b\|_\infty\leq\delta_i$. The same choice controls both maps and all the first $i+1$
rectangle constants.

10. Set $P_{-1}=0$, $e_i=(P_i-P_{i-1})z$ and $c_i=(P_i-P_{i-1})b$ for $i\geq0$. All are
continuous $F_{L_i}$-valued cochains; the linear coefficient maps commute with every finite sum
in $d$, so $dc_i=e_i$ and $de_i=0$. Their telescoping sums are $\sum_{h=0}^ie_h=P_iz\to z$. For
$i\geq1$, both supremum norms are at most $\max(\delta_i,\delta_{i-1})$. At any fixed input
$(s,y)$ of $z$, $e_i(s,y)$ is eventually zero: the algebraic value $z(s,y)$ lies in one $F_N$
and both projections eventually fix it. This last assertion is made only for $z$, not for the
completed primitive $b$.

11. For $i\geq1$ and $j\leq i$ put $v_{i,j}=c_i-T_je_i$ and define
$$B_{i,j}(s,x)=(T_je_i)(s,x)+v_{i,j}(s,x)-v_{i,j}(\rho_j(s),x).$$
These are continuous
$F_{L_i}$-valued cochains. At $a\in A_j$, the homogeneous values of $z(a,-)$ on $B_j$ lie in
$F_{N_j}$, which both $P_i$ and $P_{i-1}$ fix since $L_{i-1}\geq N_j$. Thus the homogeneous
function of $e_i(a,-)$ vanishes there. The rectangle operator gives $dT_je_i(a,-)=e_i(a,-)$, so
$dv_{i,j}(a,-)=0$. Therefore
$$dB_{i,j}=dT_je_i+(e_i-dT_je_i)-0=e_i.$$
Also
$B_{i,j}(s,-)=T_je_i(s,-)$ for $s\in A_j$, because $\rho_j(s)=s$. Its supremum norm is at most
$\max(\|c_i\|_\infty,C_j\|e_i\|_\infty)$, by the ultrametric inequality and the operator bound.

12. Let $b_0=c_0$. For $i\geq1$ define $b_i(s,x)=B_{i,k_i(s)}(s,x)$. The finitely many clopen
pieces of $k_i$ make this a continuous $F_{L_i}$-valued cochain with $db_i=e_i$. Since
$k_i(s)\leq i$, the preceding bound and $D_i\max(\delta_i,\delta_{i-1})\leq2^{-(i-1)}$ give
$\|b_i\|_\infty\leq2^{-(i-1)}$. Here $D_i\delta_{i-1}=2^{-(i-1)}$ and $D_i\delta_i\leq2^{-i}$.
Fix $(s,x)$. Eventually $k_i(s)=j(s)$ and $s\in A_{j(s)}$, so
$$b_i(s,x)=T_{j(s)}e_i(s,x)=\sum_{a=1}^{u_{j(s)}}\alpha_{j(s),a}e_i(s,\psi_{j(s),a}(x)).$$
This
is one fixed finite list of evaluations. Each term is eventually zero by step 10. Hence
$b_i(s,x)=0$ for all sufficiently large $i$.

13. The partial sums $\sum_{i=0}^Nb_i$ are uniformly Cauchy into the complete field $B$: by the
ultrametric inequality every tail has norm at most the largest norm of its terms, and those
norms tend to zero. Their pointwise limits therefore give a uniform limit $b_*:S\times
G^{n-1}\to B$. For continuity, approximate $b_*$ uniformly within any prescribed positive error
by one continuous partial sum and use the strong triangle inequality near the point in question.
Step 12 makes every value a finite sum in $\Omega$; the isometric subspace topology then makes
$b_*$ continuous into $\Omega$ itself. At a fixed input $d$ is a finite sum of evaluations, so
$$db_*=\lim_Nd\Big(\sum_{i=0}^Nb_i\Big)=\lim_NP_Nz=z.$$
Pull back this cochain by $p\times
q^{n-1}$ from step 2. It is a genuine $\Omega$-valued continuous primitive on the original $S$.
Choose $S_1=S$, $u_1=\mathrm{id}_S$. This proves the requested assertion with actual equality of
cochains.
-/
theorem parameter_cochain_completion_boundary_descent
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [NormedField Ω]
    [NormedAlgebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (G : ProfiniteGrp.{w}) (S : Profinite.{v}) (n : ℕ)
    (z : C(S × (Fin (n + 1) → G), Ω))
    (hz : ∀ (s : S) (g : Fin (n + 2) → G),
      z (s, fun i ↦ g i.succ) +
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j.val + 1) •
          z (s, Fin.contractNth j (· * ·) g) = 0)
    (hb : ∃ b : C(S × (Fin n → G), UniformSpace.Completion Ω),
      ∀ (s : S) (g : Fin (n + 1) → G),
        b (s, fun i ↦ g i.succ) +
          ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) •
            b (s, Fin.contractNth j (· * ·) g) =
              UniformSpace.Completion.coeRingHom (z (s, g))) :
    ∃ (m : ℕ) (T : Fin m → Profinite.{v}) (a : ∀ j : Fin m, C(T j, S))
      (b : ∀ j : Fin m, C(T j × (Fin n → G), Ω)),
      (∀ s : S, ∃ (j : Fin m) (t : T j), a j t = s) ∧
      ∀ (j : Fin m) (t : T j) (g : Fin (n + 1) → G),
        b j (t, fun i ↦ g i.succ) +
          ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
            b j (t, Fin.contractNth k (· * ·) g) = z (a j t, g) := by
  sorry

end ContinuousCohomology
