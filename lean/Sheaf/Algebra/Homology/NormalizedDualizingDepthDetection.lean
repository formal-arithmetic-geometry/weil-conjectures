/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.RingTheory.Depth
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Sheaf.Algebra.Homology.CoherentRHomFiniteInjectiveDimension
import WeilConjectures.RingTheory.DepthExt
import Sheaf.Algebra.Homology.BoundedInjectiveRHomModelSupport
import Sheaf.Algebra.Homology.BoundedInjectiveTotalHomExact
import WeilConjectures.RingTheory.SimpleFiltration
import Sheaf.RingTheory.LengthOfSupportAtMaximalIdeal
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.Algebra.Module.QuotientPrimaryComponentNoTorsion
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated
import WeilConjectures.RingTheory.DepthQuotSMulTop

import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Noetherian.Basic

/-! # Degree bounds and depth detection for normalized algebraic duality

Source: Stacks Project, dualizing.tex, Tags 0A7B and 0A7U(1),(3), and
section-dualizing-local (normalization).
(blueprint: lem-sfb-normalized-dualizing-depth-detection).

The ordinary-module presentation of the recorded derived internal Hom is used.
Scalar action is the canonical enriched identity, the transpose of the right unitor.
The tensor unit represents A[0]. No dualizing complex is chosen by this module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

/-- The module E^i = H^i(RHom_A(M[0],K)), using the existing RHom bifunctor.
This abbreviation only names the expression E^i in the statement below.
Source: Stacks Project, Tag 0A7U
(blueprint: lem-sfb-normalized-dualizing-depth-detection). -/
abbrev moduleDualCohomology (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    ModuleCat.{u} A :=
  (homologyFunctor (ModuleCat.{u} A) i).obj
    ((ordinaryModuleDerivedInternalHom A).obj
      (op ((singleFunctor (ModuleCat.{u} A) 0).obj M), K))

/-- Normalized algebraic duality has degrees [-dim Supp(M),0] and detects depth
as the least nonnegative t with nonzero cohomology in degree -t.

Source: Stacks Project, dualizing.tex, Tag 0A7U(1),(3), Tag 0A7B, and
section-dualizing-local (normalization).
(blueprint: lem-sfb-normalized-dualizing-depth-detection).

Proof (the accepted DAG split, steps 1--14):

1. Write $D^i(T)=H^iR\operatorname{Hom}_A(T[0],K)$ for any finite $T$. The hypotheses on $K$ are
used as written inline, without a separate dualizing-definition node. By
[lem-trf-coherent-rhom-finite-injective-dimension], applied with source $T[0]$ and target $K$,
every $D^i(T)$ is finite. For nonzero finite $T$, [lem-weil-pbc-depth-ext] gives finite depth.
Also $\operatorname{Ann}_A(T)$ is proper and contained in $\mathfrak m$, so
[lem-weil-pbc-finite-module-support-annihilator] puts $\mathfrak m$ in its support. Every prime
chain of its support is a prime chain of $A$;
[lem-weil-pbc-noetherian-local-finite-krull-dimension] therefore gives $0\le d_T\le\dim A<\infty$.
We have $D^i(0)=0$, directly from the zero Hom complex. Uses:
lem-trf-coherent-rhom-finite-injective-dimension, lem-weil-pbc-depth-ext,
lem-weil-pbc-finite-module-support-annihilator,
lem-weil-pbc-noetherian-local-finite-krull-dimension.

2. Fix a bounded injective representative $J$ of $K$. The natural derived isomorphism of
[lem-trf-bounded-injective-rhom-model-support], applied to $T[0]$, computes $D^i(T)$ as
$H^i\operatorname{Hom}_A^\bullet(T[0],J)$. For $0\to U\to V\to W\to0$, apply
[lem-trf-bounded-injective-total-hom-exact] to the complexes in degree zero, then
[lem-weil-pbc-complex-ses-homology-long-exact]. This gives $\cdots\to D^i(W)\to D^i(V)\to
D^i(U)\to D^{i+1}(W)\to\cdots$. The naturality clause of the model node identifies these arrows
with the maps induced by the given module maps. If $U\to V$ is multiplication by $f$ on $T$, its
Hom-complex map is multiplication by $f$, since $\varphi(ft)=f\varphi(t)$ termwise; its cohomology
map is consequently multiplication by $f$ as well. Uses:
lem-trf-bounded-injective-rhom-model-support, lem-trf-bounded-injective-total-hom-exact,
lem-weil-pbc-complex-ses-homology-long-exact.

3. For a finite-length $A$-module $L$, [lem-weil-pbc-finite-length-module-simple-filtration] gives
$0=L_0\subsetneq\cdots\subsetneq L_r=L$ with simple factors. Each simple factor $S$ is $\kappa$:
if $0\ne z\in S$, simplicity makes $a\mapsto az$ a surjection $A\to S$ with proper kernel $I$; a
strict intermediate ideal $I\subsetneq J\subsetneq A$ would give a proper nonzero submodule of
$S$. Thus $I$ is maximal, hence $I=\mathfrak m$. These maps identify all factors with $\kappa$. In
particular $\mathfrak m L_j\subseteq L_{j-1}$, so $\mathfrak m^r L=0$; if $L\ne0$ then $r\ge1$ and
$L_1\cong\kappa$ embeds in $L$. Uses: lem-weil-pbc-finite-length-module-simple-filtration.

4. The normalization in the statement gives $D^i(\kappa)=0$ for $i\ne0$ and
$D^0(\kappa)\cong\kappa\ne0$. Induct on $j$ in Step 3, starting with $L_0=0$. Applying Step 2 to
$0\to L_{j-1}\to L_j\to\kappa\to0$ shows $D^i(L_j)=0$ for $i\ne0$ and gives $0\to\kappa\to
D^0(L_j)\to D^0(L_{j-1})\to0$: the outer groups needed here are $D^{-1}(L_{j-1})$ and
$D^1(\kappa)$, already zero. Thus every finite-length $L$ has dual cohomology concentrated in
degree zero, and $D^0(L)\ne0$ if $L\ne0$. This is the elementary filtration argument, not the full
Matlis-duality identification.

5. We now prove by strong induction on $d\ge0$ that every nonzero finite $T$ with $d_T=d$
satisfies $D^i(T)=0$ for $i<-d$ or $i>0$. When $d=0$, any prime of its support distinct from
$\mathfrak m$ would give a strict length-one chain ending in $\mathfrak m$, which belongs to the
support by Step 1. Hence its support is $\{\mathfrak m\}$. By
[lem-sc-generic-stalk-finite-length], $T$ has finite length. Step 4 gives exactly the desired
vanishing. For $d>0$ assume the bounds for every nonzero finite module of support dimension
strictly below $d$; first prove the positive-depth case at dimension $d$, then the depth-zero
case. Uses: lem-sc-generic-stalk-finite-length.

6. Suppose $d_T=d>0$ and $\operatorname{depth}(T)>0$. The supremum definition of depth gives a
regular sequence of positive length; its first element $f\in\mathfrak m$ acts injectively on $T$.
Put $Q=T/fT$. Its finite generating set is given by the images of generators of $T$, and $Q\ne0$
by Nakayama. The nonzerodivisor clause of
[lem-weil-pbc-support-dimension-quotient-element-equality] gives $d_Q+1=d_T$, so $d_Q=d-1$. The
dimension induction in Step 5 applies to $Q$ and gives $D^j(Q)=0$ for $j<-(d-1)$ or $j>0$. Step 2
applies to $0\to T\xrightarrow{f}T\to Q\to0$. Uses: def-weil-pbc-depth,
def-weil-pbc-regular-sequence, lem-weil-pbc-nakayama-jacobson,
lem-weil-pbc-support-dimension-quotient-element-equality.

7. For $i<-d$ we have $i+1<-(d-1)$, and for $i>0$ we have $i+1>0$. Thus $D^{i+1}(Q)=0$ in either
case by Step 6. The exact segment $D^i(T)\xrightarrow f D^i(T)\to D^{i+1}(Q)$ gives
$fD^i(T)=D^i(T)$. The module $D^i(T)$ is finite by Step 1; the ideal $(f)$ is contained in the
Jacobson radical $\mathfrak m$. By [lem-weil-pbc-nakayama-jacobson], $D^i(T)=0$. This establishes
the bounds for all positive-depth modules of dimension $d$ before any depth-zero module of
dimension $d$ is considered. Uses: lem-weil-pbc-nakayama-jacobson.

8. For $d_T=d>0$ with depth zero, set $N=T[\mathfrak m^\infty]=\{z\in T:\mathfrak m^e z=0\text{
for some }e\ge1\}$ and $T'=T/N$. The set $N$ is a submodule: a maximum of two annihilating
exponents works for a sum, and scalar multiplication preserves the condition. By
[lem-weil-pbc-noetherian-submodule-finite], $N$ is finite. Choose finitely many generators and
take the maximum $e$ of their annihilating exponents, obtaining $\mathfrak m^e N=0$ (take $e=1$ if
$N=0$). At any prime $\mathfrak q\ne\mathfrak m$, choose $a\in\mathfrak m\setminus\mathfrak q$;
then $a^eN=0$, and $a$ acts invertibly after localization, so $N_{\mathfrak q}=0$. Hence, if
$N\ne0$, [lem-sc-generic-stalk-finite-length] gives it finite length, and Step 4 applies. If $N=0$
its dual vanishes by Step 1. Uses: lem-weil-pbc-noetherian-submodule-finite,
def-weil-pbc-module-localization, lem-sc-generic-stalk-finite-length.

9. For $\mathfrak q\ne\mathfrak m$, the quotient map gives an isomorphism $T_{\mathfrak q}\to
T'_{\mathfrak q}$, directly on fractions: it is surjective by lifting numerators, and if $z/s$
maps to zero, some $u\notin\mathfrak q$ has $uz\in N$, whence $a^euz=0$ for the $a$ of Step 8, so
$z/s=0$. Since $d>0$, the support of $T$ contains a prime other than $\mathfrak m$; thus $T'\ne0$.
It is finite as a quotient. Step 1 puts $\mathfrak m$ in both supports. The fraction isomorphisms
identify their remaining support points, so $\operatorname{Supp}(T')=\operatorname{Supp}(T)$ and
$d_{T'}=d$. This argument uses only the fraction equality and zero criterion in
[def-weil-pbc-module-localization]. Uses: def-weil-pbc-module-localization.

10. The ideal $\mathfrak m$ is finitely generated since $A$ is Noetherian. By
[lem-weil-pbc-quotient-by-power-torsion-no-torsion], $T'[\mathfrak m]=0$. In particular no element
of $T'$ has annihilator exactly $\mathfrak m$. By
[lem-weil-pbc-nonzerodivisor-if-maximal-not-associated] there is an $f\in\mathfrak m$ acting
injectively on $T'$. Nakayama makes $T'/fT'$ nonzero, so the depth and regular-sequence
definitions give $\operatorname{depth}(T')>0$. Steps 6--7, already proved for positive depth at
dimension $d$, give the bounds for $T'$. Step 2 applied to $0\to N\to T\to T'\to0$ has segment
$D^i(T')\to D^i(T)\to D^i(N)$. For $i<-d$ or $i>0$, the first term is zero by those bounds and the
last is zero by Step 4, since $i\ne0$. Thus $D^i(T)=0$. This finishes the dimension induction and
proves clause (1), without a pre-existing dualizing-bounds theorem. Uses:
lem-weil-pbc-quotient-by-power-torsion-no-torsion,
lem-weil-pbc-nonzerodivisor-if-maximal-not-associated, lem-weil-pbc-nakayama-jacobson,
def-weil-pbc-depth, def-weil-pbc-regular-sequence.

11. We prove by induction on $n\ge0$ that for every nonzero finite $T$ of depth $n$,
$D^{-n}(T)\ne0$ and $D^i(T)=0$ for $i>-n$. For $n=0$, no $f\in\mathfrak m$ can be injective on
$T$: Nakayama applied to $(f)$ makes $T/fT$ nonzero, so such an $f$ would be a regular sequence of
length one, contradicting the definition of depth. The contrapositive of
[lem-weil-pbc-nonzerodivisor-if-maximal-not-associated] supplies $z\in T$ with annihilator exactly
$\mathfrak m$. (Such $z$ is nonzero because the annihilator of zero is $A$.) Thus $a\bmod\mathfrak
m\mapsto az$ embeds $\kappa$ into $T$. Set $W=T/Az$, a finite quotient. Step 2 gives $D^0(T)\to
D^0(\kappa)\to D^1(W)$. Step 10 gives $D^1(W)=0$ when $W\ne0$, and Step 1 covers $W=0$, and
normalization gives $D^0(\kappa)\cong\kappa\ne0$. The surjection onto this nonzero module proves
$D^0(T)\ne0$. Step 10 supplies the required vanishing for $i>0$. Uses:
lem-weil-pbc-nakayama-jacobson, def-weil-pbc-depth, def-weil-pbc-regular-sequence,
lem-weil-pbc-nonzerodivisor-if-maximal-not-associated.

12. Let $n>0$ and assume the induction claim for all nonzero finite modules of depth $n-1$. If $T$
has depth $n$, the supremum defining depth contains a regular sequence of positive length;
otherwise its only possible length would be zero. Its first element $f\in\mathfrak m$ is injective
on $T$. Put $Q=T/fT$. By [lem-weil-pbc-depth-drops-by-one], $Q\ne0$ and has depth $n-1$; it is
finite since the images of any finite generating set of $T$ generate $Q$. The induction hypothesis
therefore gives $D^{-(n-1)}(Q)\ne0$ and $D^j(Q)=0$ for every $j>-(n-1)$. The short exact sequence
$0\to T\xrightarrow{f}T\to Q\to0$ satisfies the hypotheses of Step 2. Uses: def-weil-pbc-depth,
def-weil-pbc-regular-sequence, lem-weil-pbc-depth-drops-by-one.

13. For any integer $i>-n$, we have $i+1>-(n-1)$, so $D^{i+1}(Q)=0$ by Step 12. Exactness of
$D^i(T)\xrightarrow{f}D^i(T)\to D^{i+1}(Q)$ from Step 2 gives $fD^i(T)=D^i(T)$. The module
$D^i(T)$ is finite by Step 1, and $(f)$ lies in the Jacobson radical since $A$ is local and
$f\in\mathfrak m$. Nakayama therefore gives $D^i(T)=0$. This proves the vanishing half of the
induction claim in all degrees $i>-n$. Uses: lem-weil-pbc-nakayama-jacobson.

14. The same exact sequence contains $D^{-n}(T)\to D^{-n+1}(Q)\to D^{-n+1}(T)$. Its middle term is
nonzero by Step 12, while the last is zero by Step 13. Thus the first arrow is surjective onto a
nonzero module, and $D^{-n}(T)\ne0$. This completes the induction. Apply it with $T=M$ and its
finite depth from Step 1. For $0\le t<\operatorname{depth}(M)=n$, the inequality $-t>-n$ gives
$E^{-t}=0$, and $E^{-n}\ne0$. Hence $n$ is precisely the smallest nonnegative integer $t$ with
$E^{-t}\ne0$, which proves clause (2).
-/
theorem normalizedDualizing_degreeBounds_depthDetection
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hKinjective : ∃ J : CochainComplex (ModuleCat.{u} A) ℤ,
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (J.X i)) ∧
      (∀ i : ℤ, Injective (J.X i)) ∧ Nonempty (Q.obj J ≅ K))
    (hKfinite : ∀ i : ℤ, Module.Finite A
      ((homologyFunctor (ModuleCat.{u} A) i).obj K))
    (hKscalar : IsIso (MonoidalClosed.id K))
    (hKnormalized : Nonempty
      ((ordinaryModuleDerivedInternalHom A).obj
        (op ((singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A))), K) ≅
        (singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A))))
    (M : ModuleCat.{u} A) [Module.Finite A M] [Nontrivial M] :
    (∀ d : ℕ, Module.supportDim A M = (d : WithBot ℕ∞) →
      ∀ i : ℤ, i < -(d : ℤ) ∨ 0 < i → IsZero (moduleDualCohomology A M K i)) ∧
    (∃ n : ℕ, IsLocalRing.depth (R := A) M = (n : ℕ∞) ∧
      ¬ IsZero (moduleDualCohomology A M K (-(n : ℤ))) ∧
      ∀ t : ℕ, t < n → IsZero (moduleDualCohomology A M K (-(t : ℤ)))) := by
  sorry

end DerivedCategory
