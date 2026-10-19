/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.FieldTheory.TameRootsProduct
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.GroupTheory.Index
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity
import Sheaf.FieldTheory.FiniteDVRTameInertia
import Sheaf.FieldTheory.FiniteTameCharacterTower
import Sheaf.GroupTheory.InfiniteTameInverseLimit
import Sheaf.NumberTheory.DvrGaloisDegreeData
import Sheaf.RingTheory.DvrCharZeroTangentKernel
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.RingTheory.HenselianLocalRootLifting

/-!
# The canonical tame character of a strictly henselian trait

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, section 1.2,
printed page 259; Stacks Project, Tag 0BUB
(blueprint: lem-per-trait-tame-algebra).

The inverse limit and its topology are the existing `TameRoots.limitSubgroup` and
`TameRoots.limitTopology`. The coordinate formula specifies one map simultaneously for
all uniformizers and compatible root choices. Exactness uses its actual subgroup kernel.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z q

namespace IsDiscreteValuationRing

/-- The canonical continuous tame character is surjective, has pro-p kernel (trivial
in residue characteristic zero), and its target has compatible primitive generators.
Source: Travaux de Gabber, Expose XVII, section 1.2, printed page 259; Stacks Tag 0BUB
(blueprint: lem-per-trait-tame-algebra).

Proof (the numbered steps are the DAG proof, with its dependency names):
1. Write $D=\{d\in\mathbf Z_{>0}:(d,p)=1\}$. Every $d\in D$ is a unit in $R$. For $u\in R^\times$,
   the separable polynomial $X^d-\bar u$ has a root in the separably closed field $k$, and its
   derivative there is nonzero. Apply [lem-weil-pbc-henselian-local-root-lifting] to obtain $b\in
   R^\times$ with $b^d=u$. Also [lem-sbc-strict-local-roots-of-unity] gives exactly $d$ roots of
   $X^d-1$ in $R$, forming a cyclic group, with distinct residues. These are all its roots in
   $\Omega$, by the degree bound for a polynomial over a field. Thus $\mu_d(\Omega)\subset
   R^\times\subset K^\times$, and reduction identifies it with $\mu_d(k)$. Here and below the
   finite root groups have their discrete topology.
2. For each $d\in D$ the roots of $X^d-\pi$ form a nonempty finite set $A_d$ in
   $K^{\mathrm{sep}}$: the polynomial is separable, since $d$ is nonzero in $K$, and splits in the
   separable closure. If $d\mid e$, taking the $(e/d)$th power maps $A_e$ onto $A_d$, since an
   $(e/d)$th root of any $\alpha_d$ is a root of $X^e-\pi$. These maps obey the identity and
   composition laws. The divisibility poset $D$ is nonempty and directed by least common
   multiples. Apply [lem-galois-inverse-limit-surjective] to choose a compatible family
   $\alpha_d=\pi^{1/d}$. Put $K_d=K(\alpha_d)$. The ring $R[T]/(T^d-\pi)$ is a domain by
   [lem-sbc-dvr-uniformizer-root-algebra]; localizing it at $R\setminus\{0\}$ gives the domain
   $K[T]/(T^d-\pi)$, so this polynomial is irreducible over $K$. Its roots are $\zeta\alpha_d$
   with $\zeta\in\mu_d(K)$ by Step 1. Apply [lem-exc-kummer-binomial-splitting-field]: $K_d/K$ is
   cyclic Galois of degree $d$, and its character $h\mapsto h(\alpha_d)/\alpha_d$ bijects its
   Galois group with $\mu_d(K)$. Indeed this character is injective since $\alpha_d$ generates,
   and both groups have $d$ elements.
3. For every finite Galois $L/K$ in $K^{\mathrm{sep}}$, let $B_L$ be the integral closure of $R$
   in $L$. A DVR is a PID by [def-sc-discrete-valuation-ring], hence is Noetherian and normal by
   [lem-weil-pbc-pid-noetherian-normal]. Thus
   [lem-weil-pbc-noetherian-normal-separable-integral-closure-finite] makes $B_L$ finite over $R$.
   It is a nonzero domain with fraction field $L$ by
   [lem-weil-pbc-integral-closure-finite-extension-normal]. The product decomposition of
   [lem-weil-pbc-finite-over-henselian-local-product] has exactly one nonzero factor: two factors
   would give a nontrivial idempotent in a domain. Consequently $B_L$ is local, with unique
   maximal ideal $\mathfrak n_L$ over that of $R$. By [lem-exc-dvr-galois-degree-data], $B_L$ is a
   DVR, its residue field $k_L$ is finite over $k$, and $[L:K]=e_L[k_L:k]$, where $e_L=v_L(\pi)>0$
   and $v_L$ gives a uniformizer value $1$. Every $K$-automorphism preserves $B_L$ by its monic
   equations and preserves its unique maximal ideal.
4. If $p>1$, [lem-pc-kbar-pure-insep] implies that $k_L/k$ is purely inseparable: embed this
   finite algebraic extension in an algebraic closure of $k$ and restrict the stated purely
   inseparable extension. Each $x\in k_L$ therefore has $x^{p^a}\in k$ for some $a$, and any
   $k$-automorphism fixes $x$ because $X^{p^a}-x^{p^a}$ has at most one root in a field of
   characteristic $p$. If $p=1$, every irreducible polynomial over $k$ is separable (its
   derivative is nonzero and coprime to it in characteristic zero); separable closedness gives
   $k_L=k$. In either case every $K$-automorphism of $L$ acts trivially on $k_L$. Thus its
   decomposition and inertia groups are both $\operatorname{Gal}(L/K)$.
5. Apply Step 3 to $L=K_d$. In $B_{K_d}$ one has $d\,v(\alpha_d)=v(\pi)=e_{K_d}$, so $d\mid
   e_{K_d}$. But Step 3 and $[K_d:K]=d$ imply $e_{K_d}\le d$. Hence $e_{K_d}=d$ and $\alpha_d$ is
   a uniformizer. Also $[k_{K_d}:k]=1$. This uses no excellence, perfection, or completeness
   assumption.
6. For $h\in H$, put $t_d(h)=h(\alpha_d)/\alpha_d$. Its $d$th power is $1$, so it lies in
   $\mu_d(K)$ by Step 1. Since $H$ fixes this root group, $t_d(hh')=t_d(h)t_d(h')$. Compatibility
   of the $\alpha_d$ gives $t_d=t_e^{e/d}$ for $d\mid e$, hence a homomorphism $t:H\to G$. It is
   continuous: $t_d$ depends only on restriction to the finite Galois field $K_d$, and these
   restrictions are continuous for the Krull topology. The latter topology is the inverse-limit
   topology on finite Galois restrictions by [lem-exc-galois-krull-finite-limit]. Continuity of
   all coordinates is continuity into the subspace inverse limit.
7. Changing $\alpha_d$ for fixed $\pi$ multiplies it by an element of $\mu_d(K)$, fixed by $H$, so
   $t_d$ is unchanged. For a second uniformizer $\pi'=u\pi$, Step 1 supplies $b_d\in R^\times$
   with $b_d^d=u$. Any chosen root $\alpha'_d$ of $\pi'$ equals $b_d\alpha_d\zeta_d$ for
   $\zeta_d\in\mu_d(K)$, so $h(\alpha'_d)/\alpha'_d=h(\alpha_d)/\alpha_d$. This calculation works
   at each $d$ and does not require the $b_d$ to have been chosen compatibly. Thus the map to the
   intrinsic root limit, rather than to a chosen untwisted integer group, is independent of the
   uniformizer and all root choices.
8. Let $(z_d)_d\in G$. Step 2 gives a unique $K$-automorphism $a_d$ of $K_d$ with
   $a_d(\alpha_d)=z_d\alpha_d$. If $d\mid e$, its restriction is $a_d$, because
   $(z_e\alpha_e)^{e/d}=z_d\alpha_d$. Thus these automorphisms glue to a $K$-automorphism $a$ of
   $K_t=\bigcup_d K_d$; the compatible inverse automorphisms give its inverse. The field $K_t/K$
   is normal: each of its elements lies in a finite normal $K_d$, so its minimal polynomial splits
   there. The separable closure $K^{\mathrm{sep}}/K$ is also normal: the conjugates of a separable
   algebraic element are again separable algebraic and belong to this closure. Apply
   [lem-weil-pbc-normal-subextension-automorphism-extends] to extend $a$ to $h\in H$. Then
   $t(h)=(z_d)_d$. This proves surjectivity in both residue characteristics.
9. Assume now $p>1$. For each finite Galois $L/K$, Step 4 identifies its inertia group with
   $H_L=\operatorname{Gal}(L/K)$. Apply [lem-exc-finite-dvr-tame-inertia]: with a uniformizer
   $w_L$ of $B_L$, $\chi_L(h)=\overline{h(w_L)/w_L}$ is a surjective character to
   $\mu_{n_L}(k_L)$, whose kernel $P_L$ is a finite $p$-group, where $e_L=q_Ln_L$, $q_L$ is a
   $p$-power and $(n_L,p)=1$. Step 1 identifies $\mu_{n_L}(k_L)$ with $\mu_{n_L}(k)$: it already
   supplies $n_L$ distinct roots in $k$, which exhaust the roots in $k_L$. Define
   $\theta_L=\chi_L^{q_L}$, which has the same kernel and is surjective since raising to $q_L$ is
   an automorphism of a cyclic group of order $n_L$.
10. For $M\supseteq L$ finite Galois, the maximal ideal of $B_M$ contracts to that of $B_L$: its
   residue field is a finite-dimensional domain over $k$, and so is a field; uniqueness in Step 3
   applies. Thus [lem-exc-finite-tame-character-tower] applies to these very primes. It gives
   surjective restrictions $H_M\to H_L$ and $P_M\to P_L$, $n_L\mid n_M$, and
   $\theta_L(h|_L)=\theta_M(h)^{n_M/n_L}$. The root-group transition maps obey the identity and
   composition laws because their exponents multiply; the group and kernel transitions are
   restriction. The indexing set of finite Galois subfields is nonempty and directed, and
   $H\cong\varprojlim H_L$ topologically, by [lem-exc-galois-krull-finite-limit]. Apply
   [lem-exc-infinite-tame-inverse-limit]. We obtain a continuous surjection $\theta:H\to
   C=\varprojlim_L\mu_{n_L}(k)$ with kernel $P=\varprojlim P_L$, and every finite continuous
   quotient of $P$ has $p$-power order.
11. Every $d\in D$ occurs as $n_{K_d}=d$ by Step 5. Identify $G$ with the root limit over $k$ by
   Step 1. A compatible family $(z_d)_d$ maps to $(z_{n_L})_L\in C$. Conversely, from $(c_L)_L\in
   C$, define $z_d=c_L^{n_L/d}$ using any $L$ with $d\mid n_L$, for instance $K_d$. Two choices
   have a common finite Galois overfield $M$, and their displayed expressions both equal
   $c_M^{n_M/d}$. The same calculation proves $z_e^{e/d}=z_d$. These maps are inverse: to recover
   $c_L$, use that very $L$ at order $n_L$. Each coordinate of either map depends on one input
   coordinate through a power map between finite groups, so both maps are continuous. This
   explicitly gives the topological isomorphism $G\cong C$.
12. At $L=K_d$, Step 5 makes $\alpha_d$ a uniformizer and $q_{K_d}=1$. Hence
   $\theta_{K_d}(h)=\overline{h(\alpha_d)/\alpha_d}=\overline{t_d(h)}$. Under the reduction
   identification of Step 1, the isomorphism in Step 11 therefore carries $t$ exactly to $\theta$,
   coordinate by coordinate at every $d$. Consequently $S=\ker t=P$, topologically, and Step 10
   proves the required finite-quotient assertion for $S$ when $p>1$.
13. Now suppose $p=1$. For each $L$ of Step 3, Step 4 gives $k_L=k$, and every automorphism acts
   trivially on it. For a uniformizer $w_L$, put $\chi_L(h)=\overline{h(w_L)/w_L}$. Writing
   $\pi=u_L w_L^{e_L}$ and applying $h$ gives $\chi_L(h)^{e_L}=1$, because
   $\overline{h(u_L)/u_L}=1$. The equality $h(h'(w_L))/w_L=h(h'(w_L)/w_L)h(w_L)/w_L$ proves
   multiplicativity after reduction. If $\chi_L(h)=1$, the automorphism of the DVR $B_L$ is
   finite-order, fixes its residue field, and satisfies $h(w_L)/w_L\equiv1$ modulo its maximal
   ideal. By [lem-per-dvr-char-zero-tangent-kernel] it is the identity on $B_L$, hence on its
   fraction field $L$. Thus $\chi_L$ is injective. Only the characteristic-zero finite-order
   congruence lemma is newly required here.
14. For $M\supseteq L$ finite Galois in this characteristic-zero case, write $w_L=v w_M^r$ in the
   DVR $B_M$, with $v$ a unit. Valuations of $\pi$ give $e_M=r e_L$. Reducing
   $h(w_L)/w_L=(h(v)/v)(h(w_M)/w_M)^r$ gives $\chi_L(h|_L)=\chi_M(h)^{e_M/e_L}$, since $h$ fixes
   the residue field. Let $h\in S$ and fix $L$. Take a finite Galois $M$ containing both $L$ and
   $K_{e_L}$. Since $e_{K_{e_L}}=e_L$ by Step 5, this formula applied to both subfields gives
   $\chi_L(h|_L)=\chi_{K_{e_L}}(h|_{K_{e_L}})$. The right side is $1$, as $h\in S$ fixes every
   $\alpha_d$, and hence fixes $K_{e_L}$. Step 13 gives $h|_L=1$. The union of finite Galois
   subfields is $K^{\mathrm{sep}}$, as in [lem-exc-galois-krull-finite-limit], so $h=1$. Thus
   $S=1$ when $p=1$. Together with Step 8 and the definition $S=\ker t$, this establishes the
   asserted exact sequence in every case.
15. It remains to produce compatible primitive roots in $\Omega$. By [lem-sc-primitive-root], the
   set $E_d$ of primitive $d$th roots is finite and nonempty. If $d\mid e$, the power map $E_e\to
   E_d$ is onto. Indeed choose primitive $\eta_e$; the prescribed target is $(\eta_e^{e/d})^a$ for
   an integer $a$ prime to $d$. Choose $b\equiv a\pmod d$ and $b\equiv1\pmod r$ for each prime
   $r\mid e$ not dividing $d$, using [lem-pc-crt-ideal-quotient-product] over $\mathbf Z$. These
   ideals are pairwise coprime, and the resulting $b$ is prime to $e$, so $\eta_e^b$ is the
   required primitive lift. The transition maps satisfy identity and composition. Apply
   [lem-galois-inverse-limit-surjective] to this inverse system of primitive-root sets to obtain
   $(\zeta_d)_d\in G$ with every $\zeta_d$ primitive. Write $\sigma=(\zeta_d)_d$.
16. A basic open subset of $G$ specifies finitely many coordinates; choose $e\in D$ divisible by
   their indices. Since $\zeta_e$ generates $\mu_e(\Omega)$, some integer power of $\sigma$
   matches any given point at coordinate $e$, hence at all those coordinates. Thus
   $\langle\sigma\rangle$ is dense. Fix $d\in D$. The coordinate projection $G\to\mu_d(\Omega)$ is
   onto because it contains all powers of $\zeta_d$, and its kernel $U_d$ is closed. Every power
   of $\sigma^d$ lies in $U_d$. Conversely, for $x\in U_d$ and any finite-coordinate neighborhood,
   choose $e$ divisible by $d$ and those indices, and write $x_e=\zeta_e^a$. Then
   $1=x_d=\zeta_d^a$ implies $d\mid a$, so $\sigma^a\in\langle\sigma^d\rangle$ lies in the
   neighborhood. Hence $\overline{\langle\sigma^d\rangle}=U_d$. Its cosets are the $d$ fibers of
   that surjective coordinate projection, giving index exactly $d$, including $d=1$. -/
theorem exists_canonical_tame_character
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ksep : Type w) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (Ω : Type z) [Field Ω] [IsAlgClosed Ω] [Algebra Ksep Ω]
    (p : ℕ) (hp : p = if ringChar (IsLocalRing.ResidueField R) = 0 then 1
      else ringChar (IsLocalRing.ResidueField R)) :
    ∃ t : Gal(Ksep/K) →* TameRoots.limitSubgroup Ω p,
      @Continuous _ _ inferInstance (TameRoots.limitTopology Ω p) t ∧
      Function.Surjective t ∧
      (∀ π : R, Irreducible π →
        ∃ α : TameRoots.Order p → Ksep,
          (∀ d : TameRoots.Order p,
            α d ^ d.1 = algebraMap K Ksep (algebraMap R K π)) ∧
          ∀ d e : TameRoots.Order p, d.1 ∣ e.1 → α e ^ (e.1 / d.1) = α d) ∧
      (∀ (π : R), Irreducible π → ∀ α : TameRoots.Order p → Ksep,
        (∀ d : TameRoots.Order p,
          α d ^ d.1 = algebraMap K Ksep (algebraMap R K π)) →
        (∀ d e : TameRoots.Order p, d.1 ∣ e.1 → α e ^ (e.1 / d.1) = α d) →
        ∀ (h : Gal(Ksep/K)) (d : TameRoots.Order p),
          (((t h).1 d : Ωˣ) : Ω) = algebraMap Ksep Ω (h (α d) / α d)) ∧
      (∀ (Q : Type q) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
        (f : t.ker →* Q), Continuous f → Function.Surjective f →
          ∃ n : ℕ, Nat.card Q = p ^ n) ∧
      (p = 1 → t.ker = ⊥) ∧
      (∃ σ : TameRoots.limitSubgroup Ω p,
        TameRoots.IsCompatiblePrimitiveFamily p σ.1) ∧
      ∀ σ : TameRoots.limitSubgroup Ω p,
        TameRoots.IsCompatiblePrimitiveFamily p σ.1 →
        @DenseRange (TameRoots.limitSubgroup Ω p) (TameRoots.limitTopology Ω p) ℤ
          (fun n : ℤ ↦ σ ^ n) ∧
        ∀ d : TameRoots.Order p,
          ∃ U : Subgroup (TameRoots.limitSubgroup Ω p),
            (U : Set (TameRoots.limitSubgroup Ω p)) =
              @closure _ (TameRoots.limitTopology Ω p)
                (Set.range (fun n : ℤ ↦ (σ ^ d.1) ^ n)) ∧
            U.index = d.1 := by
  sorry

end IsDiscreteValuationRing
