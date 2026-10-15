/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Sheaf.RingTheory.GlobalDimension
public import Sheaf.RingTheory.Depth
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Regular.RegularSequence
import Sheaf.RingTheory.DepthQuotSMulTop
import Sheaf.RingTheory.MinimalFiniteFreeResolutionLocal
import Mathlib.Algebra.Module.Projective
import Sheaf.Algebra.ProjectiveDimensionWellDefined
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.AlgebraicGeometry.ExactFreeComplexLastMinors
import Sheaf.RingTheory.DepthInSES
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Sheaf.Algebra.Homology.FlatResolutionTorComparison
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Sheaf.RingTheory.DepthOverQuotientRing

/-!
# The Auslander–Buchsbaum depth formula

Source: Stacks Project, Algebra, Tag 090V, proposition-Auslander-Buchsbaum
(blueprint: lem-weil-pbc-auslander-buchsbaum).
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- The Auslander–Buchsbaum formula for a nonzero finite module of finite projective dimension
 over a commutative Noetherian local ring. Both depths use the unique maximal ideal.
Source: Stacks Project, Algebra, Tag 090V, proposition-Auslander-Buchsbaum
(blueprint: lem-weil-pbc-auslander-buchsbaum).

Proof:
1. First justify induction on the depth of the module, uniformly over all Noetherian local rings.
Nakayama gives $\mathfrak mM\ne M$, since $M$ is finite and nonzero and the Jacobson radical of a
local ring is its unique maximal ideal. If $\operatorname{depth}(M)=0$ it is already finite.
Otherwise the supremum definition of depth supplies a regular sequence of positive length in
$\mathfrak m$; its first element $y$ is injective on $M$. The depth-drop lemma applied to $y$
explicitly says that $\operatorname{depth}(M)$ is a finite integer. Thus put
$t=\operatorname{depth}(M)\in\mathbf N$ and use strong induction on $t$ for the asserted formula
for every pair $(R,M)$ satisfying the hypotheses. Uses: lem-weil-pbc-nakayama-jacobson,
def-weil-pbc-depth, def-weil-pbc-regular-sequence, lem-weil-pbc-depth-drops-by-one.

2. Put $e=\operatorname{pd}_R(M)$. By the resolution-length definition, part (2) of the
projective-dimension well-definedness lemma, and the minimal finite free resolution lemma choose
an exact resolution $0\to F_e\to\cdots\to F_0\to M\to0$ with $F_i=R^{n_i}$ and every differential
between free terms having entries in $\mathfrak m$. If $e>0$, $n_e>0$: otherwise deleting the zero
top term gives a shorter projective resolution, contradicting the definition of $e$. If $e=0$,
$F_0\cong M$ and $n_0>0$ since $M\ne0$. Uses: def-weil-pbc-finite-global-dimension,
lem-weil-pbc-minimal-finite-free-resolution-local, def-weil-pbc-projective-module,
lem-weil-pbc-projective-dimension-well-defined.

3. A nonzero finite free module $R^n$, $n>0$, has the same depth as $R$: quotienting
coordinatewise by each prefix of a sequence gives $(R/J)^n$, multiplication is injective on this
module exactly when it is injective on $R/J$, and $(R/J)^n\ne0$ exactly when $R/J\ne0$. Therefore
the regular sequences, and hence their length suprema, coincide. For $e=0$ this proves the desired
formula immediately. For $e>0$ define $Z_0=M$ and $Z_i=\operatorname{im}(F_i\to F_{i-1})$ for
$1\le i\le e$, identifying $Z_e$ with $F_e$. Exactness gives $0\to Z_{i+1}\to F_i\to Z_i\to0$ for
$0\le i<e$. Each $Z_i$ is finite by the Noetherian-submodule lemma (and $Z_0$ is finite by
hypothesis). Each is nonzero: $Z_i=0$, $i\ge1$, would allow truncation to a projective resolution
of $M$ of length at most $i-1<e$. Consequently every $F_i$ in these sequences is nonzero too.
These checks ensure that all three modules in every application of the depth lemma are nonzero
finite modules. Uses: def-weil-pbc-regular-sequence, def-weil-pbc-depth, def-weil-pbc-free-module,
def-weil-pbc-finite-global-dimension, lem-weil-pbc-noetherian-submodule-finite.

4. For $e>0$ apply the exact-free-complex last-minors lemma to the unaugmented free complex. Its
top rank $n_e$ is positive. Every $n_e$-minor of the top matrix is a sum of products of $n_e$
entries in $\mathfrak m$, so the ideal $I$ of these minors is contained in $\mathfrak m$ and
cannot equal $R$. The lemma therefore supplies an $R$-regular sequence of length $e$ in
$I\subseteq\mathfrak m$. The depth definition gives $d:=\operatorname{depth}(R)\ge e$. In
particular $d>0$; the depth-drop lemma applied to the first element of this regular sequence shows
that $d$ is finite. Uses: lem-weil-pbc-exact-free-complex-last-minors-regular-sequence,
def-weil-pbc-depth, lem-weil-pbc-depth-drops-by-one.

5. Base case $t=0$, with $e>0$. Start with $\operatorname{depth}(Z_e)=d$. In $0\to Z_{i+1}\to
F_i\to Z_i\to0$ the second inequality of the depth lemma gives
$\operatorname{depth}(Z_i)\ge\min\{d,\operatorname{depth}(Z_{i+1})-1\}$. Descending induction from
$i=e-1$ to $i=0$ yields $\operatorname{depth}(Z_i)\ge d-(e-i)$, because $d\ge e$ and
$\operatorname{depth}(F_i)=d$. If a syzygy has infinite depth its contribution to the minimum is
$d$, so the same bound remains valid. Hence $0=t=\operatorname{depth}(Z_0)\ge d-e$. Together with
$d\ge e$ this gives $d=e=e+t$. Uses: lem-weil-pbc-depth-in-ses.

6. Induction step $t>0$, with $e>0$. The split short exact sequence $0\to R\to R\oplus M\to M\to0$
has nonzero finite terms. The first inequality of the depth lemma gives
$\operatorname{depth}(R\oplus M)\ge\min\{d,t\}>0$. Nakayama ensures $\mathfrak m(R\oplus M)\ne
R\oplus M$, so the depth definition supplies a regular sequence of positive length on $R\oplus M$
in $\mathfrak m$. Let $x$ be its first term. Multiplication by $x$ is injective on each summand,
so $x$ is a common nonzerodivisor on $R$ and $M$. Uses: lem-weil-pbc-depth-in-ses,
lem-weil-pbc-nakayama-jacobson, def-weil-pbc-depth, def-weil-pbc-regular-sequence.

7. Set $S=R/xR$ and $N=M/xM$. The depth-drop lemma gives $N\ne0$. The ring $S$ is nonzero local
with maximal ideal $\mathfrak m/xR$: its maximal ideals correspond to maximal ideals of $R$
containing $xR$, and $x\in\mathfrak m$. It is Noetherian since every ideal of $S$ is the image of
an ideal of $R$, whose finite generators map to generators; $N$ is finite since generators of $M$
descend. Reduction of the resolution modulo $x$ remains exact, as follows explicitly. In each
$0\to A\to B\to C\to0$ of Step 3, multiplication by $x$ is injective on $C$: for $C=M$ this was
proved in Step 6, and the other $C$ are submodules of finite free modules, on which $x$ is
injective because it is injective on $R$. If $a\in A$ becomes zero in $B/xB$, write $a=xb$; the
image of $b$ in $C$ is killed by $x$, hence is zero, so $b\in A$ and $a\in xA$. To check exactness
in the middle, if $b\in B$ maps to $xc$ in $C$, lift $c$ to $b_1\in B$ and observe that $b-xb_1\in
A$. Surjectivity follows by lifting representatives. Thus $0\to A/xA\to B/xB\to C/xC\to0$ is
exact. Splicing these sequences gives $0\to S^{n_e}\to\cdots\to S^{n_0}\to N\to0$. Its
differential entries still lie in the maximal ideal of $S$ and $n_e>0$. Uses:
lem-weil-pbc-depth-drops-by-one, def-weil-pbc-exact-sequence, def-weil-pbc-noetherian-ring,
def-weil-pbc-free-module.

8. The reduced resolution has shortest possible length $e$, not merely length at most $e$. Indeed
let $k=S/(\mathfrak m/xR)$. Finite free modules are flat by the finite-free flatness lemma, so the
flat-resolution Tor comparison applied to the reduced resolution, extended by zero above $e$,
identifies $\operatorname{Tor}^S_e(N,k)$ with its degree-$e$ tensor homology. Tensoring a free
term $S^n$ with $k$ gives $k^n$ by sending the basis vectors to the standard coordinate vectors;
all differential entries become zero. Hence this homology is $k^{n_e}\ne0$. If
$q=\operatorname{pd}_S(N)<e$, part (2) of the projective-dimension well-definedness lemma and the
minimal finite free resolution lemma would give a finite free resolution of $N$ of length $q$. Its
terms are again flat, and the same Tor comparison computes $\operatorname{Tor}^S_e(N,k)=0$ since
its degree-$e$ term is zero. This contradiction proves $\operatorname{pd}_S(N)=e$. All resolutions
used here are augmented exact complexes of modules, so their augmentations induce an isomorphism
on degree-zero homology and have zero higher homology, exactly the hypothesis of the comparison
theorem. Uses: lem-sc-affine-standard-cover-finite-free-local-fp-flat,
lem-pc-flat-resolution-tor-comparison, def-weil-pbc-module-chain-complex-homology,
def-weil-pbc-finite-global-dimension, lem-weil-pbc-minimal-finite-free-resolution-local,
lem-weil-pbc-projective-dimension-well-defined.

9. Apply the depth-drop lemma to $x$ on $R$ and on $M$: as $R$-module depths,
$\operatorname{depth}_R(S)=d-1$ and $\operatorname{depth}_R(N)=t-1$. The depth-over-quotient-ring
lemma, for the ideal $xR\subseteq\mathfrak m$ and the modules $S,N$ annihilated by it, identifies
these with $\operatorname{depth}(S)$ and $\operatorname{depth}_S(N)$ respectively. Step 7 verified
that $S$ is Noetherian local and $N$ is finite nonzero; Step 8 verified finite projective
dimension $e$. Strong induction, uniform over rings, therefore applies to $(S,N)$ at depth $t-1<t$
and gives $d-1=e+(t-1)$. Since $d,t$ are finite integers, adding one proves $d=e+t$. Together with
the free case and the depth-zero case this completes the induction. Uses:
lem-weil-pbc-depth-drops-by-one, lem-weil-pbc-depth-over-quotient-ring. -/
theorem depth_eq_projectiveDimension_add_depth
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Nontrivial M] [Module.Finite R M]
    (h : ModuleCat.HasFiniteProjectiveDimension (ModuleCat.of R M)) :
    depth (R := R) R =
      (ModuleCat.projectiveDimension (ModuleCat.of R M) h : ℕ∞) + depth (R := R) M := by
  sorry

end IsLocalRing
