/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.Mathlib.RingTheory.Henselian

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Sheaf.NumberTheory.DvrGaloisDegreeData
import Sheaf.FieldTheory.FiniteDVRTameInertia
import WeilConjectures.RingTheory.HenselianLocalRootLifting
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.DeligneLaumon.TraitLogSmoothUniformizerChart

/-!
# Tame quotients of complete strictly henselian traits

Source: ILO, Exposé XVI 3.7, printed p.254; Exposé VI 2.1--2.2, pp.71--72
(blueprint: lem-per-tame-trait-quotient-log-etale).

The invariant algebra is Mathlib's actual fixed subalgebra. Canonical log structures
are identified with the existing divisorial presheaves along the fraction-field maps,
compatibly with their structural maps. Thus their data are prescribed up to the
unique structural isomorphism, rather than selected from an uncharacterized existence.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A finite invertible-order group acting over the base on a finite dominant
extension of complete strictly henselian mixed-characteristic traits has the claimed
canonical log-étale quotient, and log smoothness transfers to that quotient.
Source: ILO XVI 3.7, p.254; VI 2.1--2.2, pp.71--72
(blueprint: lem-per-tame-trait-quotient-log-etale).

Proof plan from the DAG:
1. Write $B=R^{\prime}$, $L=\operatorname{Frac}B$ and $A=B^H$. By
[def-sc-discrete-valuation-ring], the rings of both given traits are DVRs; use the normalized
additive valuation $v:L^\times\to\mathbf Z$ of $B$, so $B=\{0\}\cup\{x:v(x)\geq0\}$. By
[lem-weil-pbc-finite-algebra-is-integral], $B$ is integral over $R$; the maximal-preimage clause
of [lem-weil-pbc-integral-algebra-ideal-in-radical] (with $I=0$) shows that its maximal ideal
contracts to the unique maximal ideal of $R$. Thus a uniformizer of $R$ has positive value in $B$.
Each $h$ extends to $L$ by $h(a/b)=h(a)/h(b)$. Let $G$ be the image of $H$ in
$\operatorname{Aut}(L)$ and put $F=L^G$. The action of $G$ is faithful. Apply
[lem-wf-finite-field-action-fixed-degree]: $L/F$ is finite Galois of degree $d=|G|$. The fibres of
$H\twoheadrightarrow G$ are cosets of its kernel, all of the same size, so $d\mid\#H$. If $p>0$ is
the residue characteristic of $R$, the unit hypothesis on $\#H$ implies $p\nmid d$.

2. The equality $A=B\cap F$ follows directly from being fixed by $H$. Also
$\operatorname{Frac}A=F$: for $x=a/b\in F$, $a,b\in B$, $b\neq0$, put $c=\prod_{h\in H}h(b)$. Then
$0\neq c\in A$ and $xc=a\prod_{h\neq1}h(b)\in B\cap F=A$. Restrict $v$ to $F^\times$. Its image is
a nonzero subgroup of $\mathbf Z$, since a uniformizer of $R$ has positive value in $B$ (as
checked in Step 1). Write this subgroup as $r\mathbf Z$, $r>0$, and choose $\pi\in F$ with
$v(\pi)=r$. Then $\pi\in A$. Elements of value zero are precisely the units of $A$; for every
nonzero ideal $J$ of $A$, choose an element $a\in J$ of least value. Every $b\in J$ has
$v(b/a)\geq0$, so $b/a\in A$ and $J=aA$. Thus $A$ is local, every ideal is principal, and $\pi$
generates its nonzero maximal ideal. It is a DVR, hence a trait, by
[def-sc-discrete-valuation-ring]. This is a direct valuation argument, not a new invariant-ring
lemma.

3. Since $R$ is Noetherian and $B$ is finite over $R$, the $R$-submodule $A\subset B$ is finite by
[lem-weil-pbc-noetherian-submodule-finite]. The same finite list of $R$-module generators of $B$
generates it over $A$, since $R\subset A$. Apply [lem-weil-pbc-finite-over-complete-local-product]
to $R\to A$: as $A$ is a domain it is complete for its maximal ideal. By
[lem-weil-pbc-henselian-local-root-lifting] ((ii)$\Rightarrow$(i)), the root-lifting henselianity
of $R$ in the statement is henselianity in the idempotent sense of
[lem-weil-pbc-finite-over-henselian-local-product]; apply that node to the same map. A nonzero
domain has no nontrivial idempotent, so only one factor occurs; $A$ is henselian and its residue
field $k_A$ is finite over $k_R$; by (i)$\Rightarrow$(ii) of
[lem-weil-pbc-henselian-local-root-lifting], simple roots of monic polynomials over $k_A$ lift to
$A$, as the statement's definition requires. By [lem-kun-sep-closed-finite-extension-sep-closed],
$k_A$ is separably closed. Thus $T=\operatorname{Spec}A$ is complete strictly henselian. Both
$R\hookrightarrow A$ and $A\hookrightarrow B$ are module-finite and injective, so the two scheme
maps are finite by [def-weil-finite-integral-morphism] and dominant: the zero prime maps to the
zero prime, whose closure in either domain spectrum is the whole spectrum. The embeddings also
preserve characteristic zero and the positive residue characteristic.

4. The DVRs $A$ and $B$ are normal by [lem-weil-pbc-pid-noetherian-normal]. Since $B$ is finite
over $A$, [lem-weil-pbc-finite-algebra-is-integral] says its elements are integral over $A$.
Conversely, an element of $L$ integral over $A$ is integral over $B$ by the same monic equation,
and belongs to $B$ by its normality. Thus $B$ is exactly the integral closure of $A$ in $L$. By
[lem-weil-pbc-finite-galois-fixed-field], $\operatorname{Gal}(L/F)$ has order $[L:F]=d$. The image
$G$ is a subgroup of this automorphism group of the same order, so it is the whole group. Every
such automorphism preserves $B$ (apply it to monic equations over $A$), hence its unique maximal
ideal. By [lem-weil-pbc-finite-over-henselian-local-product], $k_B/k_A$ is finite; by
[lem-kun-sep-closed-finite-extension-purely-inseparable] it is purely inseparable. Every
$k_A$-automorphism of $k_B$ is therefore the identity: if $x^{p^m}\in k_A$, the equation
$X^{p^m}=x^{p^m}$ has at most one root. Consequently both decomposition and inertia groups are the
whole $G$.

5. Choose uniformizers $\pi\in A$ and $w\in B$, and write $\pi=uw^e$ with $u\in B^\times$. By
[lem-exc-dvr-galois-degree-data], $d=e f$, where $f=[k_B:k_A]$; the number of maximal ideals is
one since $B$ is local. Thus $e$ is prime to $p$. Apply [lem-exc-finite-dvr-tame-inertia] to the
now verified integral closure $B/A$ and finite Galois extension $L/F$. Its wild kernel $P\subset
I=G$ is a finite $p$-group, while $|G|=d$ is prime to $p$, so $P=1$ (coset counting makes $|P|$
divide $d$). Its tame quotient has order the prime-to-$p$ part of $e$, which here is $e$ itself.
Hence $d=|G|=|I/P|=e$ and $f=1$. In particular the residue map $k_A\to k_B$ is an isomorphism and
$e$ is invertible in both local rings. This establishes total tame ramification without assuming
the separably closed residue fields perfect.

6. The polynomial $X^e-\bar u$ over the separably closed residue field $k_B$ has a root $\bar b$,
since $e$ is prime to $p$ and $\bar u\neq0$, so it is separable. Its derivative at that root is
$e\bar b^{e-1}\neq0$. By [lem-weil-pbc-henselian-local-root-lifting], applied in the henselian
ring $B$, this root lifts to $b\in B$ with $b^e=u$. Its residue is nonzero, hence $b$ is a unit.
Set $t=bw$. It is a uniformizer of $B$ and $t^e=\pi$. The argument includes $e=1$.

7. Let $D=A[Z]/(Z^e-\pi)$ and map $Z$ to $t$. By [lem-sbc-dvr-uniformizer-root-algebra], $D$ is a
DVR. To check this map injective, reduce a polynomial modulo the monic equation to $\sum_{0\leq
i<e}a_iZ^i$. If its image is nonzero termwise, the term values $v(a_it^i)=e v_A(a_i)+i$ are
distinct modulo $e$. A term of strictly least value cannot cancel: divide by it; its residue is
nonzero and every other summand has residue zero. Thus the kernel is zero. The same calculation
with $a_i\in F$ proves the $e$ elements $1,t,\ldots,t^{e-1}$ linearly independent over $F$. Since
$[L:F]=e$, they form a basis, so the fraction field of the embedded $D$ is $L$. The DVR $D$ is
integrally closed by [lem-weil-pbc-pid-noetherian-normal]. Every element of $B$ satisfies a monic
equation over $A\subset D$ from Step 4, so lies in $D$. The reverse inclusion holds by
construction. We have proved the actual $A$-algebra identification $B=A[t]=A[Z]/(Z^e-\pi)$.

8. The canonical log structures have the uniformizer charts $\mathbf N\to A$, $1\mapsto\pi$, and
$\mathbf N\to B$, $1\mapsto t$, as stated in [lem-per-trait-log-smooth-uniformizer-chart]. The map
of charts is $1\mapsto e$. Its group map $\mathbf Z\to\mathbf Z$ has zero kernel and cokernel
$\mathbf Z/e\mathbf Z$, of unit order. The underlying comparison $\operatorname{Spec}B\to
T\times_{\operatorname{Spec}\mathbf Z[\mathbf N]}\operatorname{Spec}\mathbf Z[\mathbf N]$ is the
identity under the presentation of Step 7. It is etale (an identity is flat, finitely presented
and unramified). Therefore [def-per-fs-log-smooth-etale] gives log etaleness of $S^{\prime}\to T$.
These are fs charts since $\mathbf N$ is finitely generated, integral and saturated. Step 1 gives
its generic-field degree $e=d\mid\#H$.

9. Now let $(V,M_V)\to S^{\prime}$ be the stated log-smooth morphism. At each geometric point
apply [lem-per-trait-log-smooth-uniformizer-chart], with the specific uniformizer $t$ constructed
above. It supplies an etale neighborhood $U\to V$, an fs monoid $Q$ with torsion-free group
completion $Q^{\rm gp}$, an injective $u:\mathbf N\to Q$, and a chart compatible with $1\mapsto
t$, for which $C=Q^{\rm gp}/\mathbf Z u(1)$ has finite torsion subgroup of order $n$ invertible on
$U$. The comparison $U\to S^{\prime}\times_{\operatorname{Spec}\mathbf Z[\mathbf
N]}\operatorname{Spec}\mathbf Z[Q]$ is etale. The hypotheses of that node are exactly the given
locally Noetherian fs condition and log smoothness over a trait; it imposes no regularity or
finite-type assumption on $V$. Use for $V\to T$ the same chart on $U$ and the map $\mathbf N\to
Q$, $1\mapsto e u(1)$.

10. Put $q=u(1)$. The group map for the composite chart is injective because $u^{\rm gp}$ is
injective and $e>0$. Write $C'=Q^{\rm gp}/\mathbf Z(e q)$. The natural surjection $C'\to C$ has
kernel $\mathbf Zq/\mathbf Z(e q)\cong\mathbf Z/e\mathbf Z$. Its inverse image of $C_{\rm tors}$
is exactly $C'_{\rm tors}$: if $m x=a q$ modulo the representatives in $Q^{\rm gp}$, then $emx=0$
in $C'$, and the converse follows by projection. Thus $0\to\mathbf Z/e\mathbf Z\to C'_{\rm
tors}\to C_{\rm tors}\to0$ is exact. Each fibre has $e$ elements, so $C'_{\rm tors}$ is finite of
order $en$, which is invertible on $U$ since both $e$ and $n$ are. This is an explicit computation
of the chart cokernel, not an appeal to logarithmic composition.

11. The two comparison targets are the same scheme with the same induced map from $U$. Indeed
their coordinate algebras are respectively $$B\otimes_{\mathbf Z[\mathbf N]}\mathbf Z[Q] \cong
A[Z]\otimes_{\mathbf Z[\mathbf N]}\mathbf Z[Q]/(Z^e-\pi) \cong A[Q]/(z^{e q}-\pi) \cong
A\otimes_{\mathbf Z[\mathbf N]}\mathbf Z[Q],$$ where the first tensor uses $1\mapsto t$ and
$1\mapsto q$, and the last uses $1\mapsto\pi$ and $1\mapsto e q$. In the middle, $Z$ is identified
with $z^q$. The comparison maps agree since they have the same $Q$-chart and $A$-structure map;
this calculation takes place on affine opens of the targets and does not require $U$ affine. The
comparison for $V\to T$ is therefore the etale comparison of Step 9, hence smooth by
[lem-weil-pbc-etale-smooth-zero-dimensional-fibres]. The charts cover every geometric point of
$V$; with the group conditions of Step 10, [def-per-fs-log-smooth-etale] gives log smoothness of
the composite. This proves the last clause and completes the item.
-/
theorem tame_trait_quotient_log_etale
    (R B : Type u) [CommRing R] [CommRing B] [IsDomain R] [IsDomain B]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing B]
    [IsStrictlyHenselianLocalRing R] [IsStrictlyHenselianLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [CharZero R] [CharZero B]
    (hR : ringChar (IsLocalRing.ResidueField R) ≠ 0)
    (hB : ringChar (IsLocalRing.ResidueField B) ≠ 0)
    [Algebra R B] [Module.Finite R B]
    (hdom : Function.Injective (algebraMap R B))
    (H : Type v) [Group H] [Finite H] [MulSemiringAction H B]
    [SMulCommClass H R B] (htame : IsUnit (Nat.card H : R)) :
    ∃ (hD : IsDiscreteValuationRing (FixedPoints.subalgebra R B H))
      (_ : IsStrictlyHenselianLocalRing (FixedPoints.subalgebra R B H)),
      IsAdicComplete (IsLocalRing.maximalIdeal (FixedPoints.subalgebra R B H))
        (FixedPoints.subalgebra R B H) ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        (algebraMap R (FixedPoints.subalgebra R B H)))) ∧
      DenseRange (Spec.map (CommRingCat.ofHom
        (algebraMap R (FixedPoints.subalgebra R B H)))) ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        (FixedPoints.subalgebra R B H).val.toRingHom)) ∧
      DenseRange (Spec.map (CommRingCat.ofHom
        (FixedPoints.subalgebra R B H).val.toRingHom)) ∧
      (∃ (K : Type u) (_ : Field K) (_ : Algebra (FixedPoints.subalgebra R B H) K)
        (_ : IsFractionRing (FixedPoints.subalgebra R B H) K)
        (L : Type u) (_ : Field L) (_ : Algebra B L) (_ : IsFractionRing B L)
        (_ : Algebra K L) (_ : Algebra (FixedPoints.subalgebra R B H) L)
        (_ : IsScalarTower (FixedPoints.subalgebra R B H) B L)
        (_ : IsScalarTower (FixedPoints.subalgebra R B H) K L),
        FiniteDimensional K L ∧ Module.finrank K L ∣ Nat.card H) ∧
      ∃ (MB : EtaleLogStructure (Spec (.of B)))
        (MA : EtaleLogStructure (Spec (.of (FixedPoints.subalgebra R B H))))
        (fsB : MB.IsFineSaturated) (fsA : MA.IsFineSaturated)
        (eB : MB.monoidSheaf.obj ≅ divisorialLogPresheaf
          (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))))
        (eA : MA.monoidSheaf.obj ≅ divisorialLogPresheaf
          (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R B H)
            (FractionRing (FixedPoints.subalgebra R B H))))))
        (q : EtaleLogHom
          ⟨Spec (.of B), inferInstance, MB, fsB⟩
          ⟨Spec (.of (FixedPoints.subalgebra R B H)), inferInstance, MA, fsA⟩),
        eB.hom ≫ divisorialStructuralMap
          (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))) = MB.alpha ∧
        eA.hom ≫ divisorialStructuralMap
          (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R B H)
            (FractionRing (FixedPoints.subalgebra R B H))))) = MA.alpha ∧
        q.base = Spec.map (CommRingCat.ofHom
          (FixedPoints.subalgebra R B H).val.toRingHom) ∧
        q.IsLogEtale ∧
        ∀ (V : FineSaturatedLogScheme.{u})
          (f : EtaleLogHom V ⟨Spec (.of B), inferInstance, MB, fsB⟩),
          f.IsLogSmooth → ∃ g : EtaleLogHom V
            ⟨Spec (.of (FixedPoints.subalgebra R B H)), inferInstance, MA, fsA⟩,
            f.CompEq q g ∧ g.IsLogSmooth := by
  sorry

end AlgebraicGeometry
