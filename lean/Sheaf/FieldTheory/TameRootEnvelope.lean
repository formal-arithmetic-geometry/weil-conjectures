module

public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Etale.Basic
public import Sheaf.RingTheory.ValuationComapResidue

import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.PrimitiveElement
import Sheaf.RingTheory.HenselianFiniteEtaleFieldLift
import WeilConjectures.RingTheory.HenselianLocalRootLifting
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Sheaf.RingTheory.HenselianFiniteEtaleMapBijective
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Sheaf.FieldTheory.MultiradicalGaloisDegree
import Mathlib.FieldTheory.Galois.Basic

/-!
# Finite tame radical envelopes

Source: Temkin, Stable modification of relative curves, §2.1, Lemma 2.1.5(iii), and
Gabber--Ramero, Almost Ring Theory, Corollary 6.2.14 and §§6.2.16--6.2.18
(blueprint: lem-trf-tame-root-envelope).

Finite extensions are realized in a fixed normed algebraic closure. The valuation
rings are restrictions of its norm valuation. The value quotient is written as
field units modulo valuation-ring units, then modulo the image of base-field units.
The residue algebra is the existing canonical restricted-valuation residue map.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace IntermediateField

/-- Numerical tameness is equivalent to an isometric embedding in a finite radical
extension of a finite unramified extension. The list may be empty; the value group
need not be discrete and the residue field need not be perfect.

Source: Temkin, §2.1, Lemma 2.1.5(iii); Gabber--Ramero, Corollary 6.2.14 and
§§6.2.16--6.2.18 (blueprint: lem-trf-tame-root-envelope).

Proof plan (the accepted DAG split):
1. Fix a common algebraic closure with the spectral extending absolute value. Its restriction to
every finite subextension agrees with the given absolute value by uniqueness. Each finite
subextension is a finite-dimensional normed space over $K$, hence complete. The completion-factors
lemma, applied with $F=K$ (and the identity finite separable extension), says that $K^\circ$ is
henselian, since $\widehat K=K$. The same application to every finite extension gives henselianity
of its valuation ring. These facts apply in particular to $L$, to the unramified fields
constructed below and to their composita. Dependencies: lem-pc-algebraic-closure-exists-unique,
lem-weil-pbc-algebraic-extension-embeds-algebraically-closed,
lem-trf-spectral-norm-algebraic-extension, lem-sfb-algebraic-absolute-value-unique,
lem-per-finite-normed-space-complete, lem-trf-separable-valued-completion-factors.

2. We will use elementary tower bookkeeping without the parent ramification-calculus lemma. For
finite $A\subset B\subset C$, products of representatives for $\Gamma_C/\Gamma_B$ and
$\Gamma_B/\Gamma_A$ represent $\Gamma_C/\Gamma_A$ exactly once; products of successive field bases
give bases both for $C/A$ and for $\widetilde C/\widetilde A$. Thus $e$, $f$ and field degrees
multiply. Put $d(B/A)=[B:A]/(e(B/A)f(B/A))$. The fundamental inequality gives $d\ge1$, and the
three multiplicativities give $d(C/A)=d(C/B)d(B/A)$. Consequently defectlessness descends to
intermediate fields, since a product of two real numbers at least one is one only if both are one.
Indices in the lower extension divide the composite index. Restricting the separability condition
to elements proves that a subextension of a separable residue extension is separable; separability
in successive residue extensions is transitive by the cited permanence lemma. Dependencies:
lem-trf-valued-extension-degree-bound, lem-zl-separable-permanence.

3. Assume (a), and put $k=\widetilde K$, $l=\widetilde L$, $e=e(L/K)$, $f=[l:k]$. Choose $\bar b$
with $l=k(\bar b)$ by the primitive-element lemma. Lift $l/k$ to a finite etale $K^\circ$-algebra
$D$ using the field-lifting lemma. A prime over the maximal ideal is obtained from $D/\mathfrak
m_KD\cong l$. The valuation-etale-factor lemma gives its localization $S$, finite etale over
$K^\circ$, a valuation domain with residue $l$ and fraction field $V_0$ of degree $f$. Choose
$y\in S$ reducing to $\bar b$. That same lemma says $S=K^\circ[y]$, $V_0=K(y)$, and the monic
minimal polynomial $g$ of $y$ reduces to the minimal polynomial of $\bar b$, with simple root
$\bar b$. Hensel lifting in $L^\circ$ produces $b$ with $g(b)=0$ and residue $\bar b$. Sending $y$
to $b$ embeds $V_0$ into $L$; write its image $V$. Uniqueness of the extending absolute value
identifies $S$ with $V^\circ$. Thus $V^\circ/K^\circ$ is finite etale, $\widetilde V=l$, and
$[V:K]=f$. The fundamental inequality gives $e(V/K)=1$, so $\Gamma_V=\Gamma_K$ and $[L:V]=e$.
Dependencies: lem-weil-pbc-finite-separable-extension-primitive-element,
lem-weil-pbc-henselian-finite-etale-field-lift, lem-trf-henselian-valuation-etale-local-factors,
lem-weil-pbc-henselian-local-root-lifting, lem-sfb-algebraic-absolute-value-unique,
lem-trf-valued-extension-degree-bound.

4. Choose nonidentity coset generators $\gamma_i$ of the finite group $\Gamma_L/\Gamma_V$ (one may
take all nonidentity cosets). Choose $t_i\in L^\times$ with value representing $\gamma_i$, let
$n_i$ be the order of that coset, and choose $a_i\in V^\times$ with $|a_i|=|t_i|^{n_i}$. Each
$n_i$ divides $e$, so is prime to $p$ when $p>0$. Put $u_i=t_i^{n_i}/a_i\in(L^\circ)^\times$.
Their residues $\bar u_i$ belong to $l=\widetilde V$. If the quotient is trivial, take the empty
list. For every integer prime to $p$ (every positive integer if $p=0$), its image in the residue
field is nonzero, hence it is a unit in each valuation ring used here. Dependencies: .

5. In an algebraic closure of $l$, adjoin all roots of the finitely many polynomials $X^{n_i}-\bar
u_i$ and $X^{n_i}-1$, and call the resulting field $k'$. These monic polynomials have no common
root with their derivatives: a root is nonzero and $n_i$ is invertible in $l$. Their roots are
separable algebraic over $l$. The algebraic-generators lemma gives $[k':l]<\infty$; adjoining the
roots one at a time gives separability by the simple-separable-extension lemma and transitivity.
At each adjunction the minimal polynomial divides the same separable polynomial over the
intermediate field. Transitivity also gives $k'/k$ finite separable, since $l/k$ is so. When the
list is empty set $k'=l$. Dependencies: lem-pc-algebraic-closure-exists-unique,
lem-weil-pbc-algebraic-generators-finite-extension, lem-trf-simple-separable-field-extension,
lem-zl-separable-permanence.

6. Lift $k'/k$ to a finite etale $K^\circ$-algebra, then take its valuation local factor as in
step 3. Denote that factor by $B$ and its fraction field by $U$. The factor lemma gives
$B=U^\circ$, residue $k'$, and $[U:K]=[k':k]$; the fundamental inequality gives
$\Gamma_U=\Gamma_K$. Both $V^\circ$ and $B$ are finite etale over $K^\circ$. The residue inclusion
$l\hookrightarrow k'$ lifts to a $K^\circ$-algebra map $V^\circ\to B$ by the finite-etale
map-bijection lemma. This map is injective: after tensoring with $K$ it is a unital map from the
field $V$ to the field $U$. Thus regard $U$ as an extension of $V$ and form $H=LU$ in an algebraic
closure containing both over $V$. The norm uniqueness lemma makes all these embeddings isometric,
including their restrictions to $K$ and $L$. In particular $\widetilde U$ contains $\widetilde
L=l$ inside $\widetilde H$. Dependencies: lem-weil-pbc-henselian-finite-etale-field-lift,
lem-trf-henselian-valuation-etale-local-factors, lem-trf-valued-extension-degree-bound,
lem-weil-pbc-henselian-finite-etale-map-bijective, lem-sfb-algebraic-absolute-value-unique,
lem-weil-pbc-algebraic-extension-embeds-algebraically-closed.

7. For each $i$, the residue $\bar u_i\in l^\times$ has an $n_i$-th root $\bar z_i$ in
$k'\subseteq\widetilde H$. Hensel lifting for $X^{n_i}-u_i$ in $H^\circ$ produces a unit $z_i$
with $z_i^{n_i}=u_i$, because $n_i\bar z_i^{n_i-1}\ne0$. Set $\alpha_i=t_i/z_i\in H$. Then
$\alpha_i^{n_i}=a_i\in V^\times\subseteq U^\times$ and $|\alpha_i|=|t_i|$. Also $U$ contains all
$n_i$-th roots of unity: the residue polynomial $X^{n_i}-1$ splits into $n_i$ distinct roots in
$k'$, and Hensel lifting in $U^\circ$ gives $n_i$ distinct roots upstairs. A polynomial of degree
$n_i$ has at most that many roots, so these are all the roots in the common algebraic closure.
Dependencies: lem-weil-pbc-henselian-local-root-lifting,
lem-pc-separable-polynomial-distinct-roots-alg-closed.

8. Put $R=U(\alpha_i)\subseteq H$. Since $\Gamma_U=\Gamma_V$ and $|\alpha_i|=|t_i|$, the group
$\Gamma_R/\Gamma_U$ contains the $e$ distinct cosets generated by the original $\gamma_i$. The
fundamental inequality gives $[R:U]\ge e$. On the other hand, the $U$-span in $H$ of a $V$-basis
of $L$ is a subalgebra: multiplication has structure constants in $V$. It is a domain of dimension
at most $[L:V]=e$, hence a field by the finite-dimensional-domain lemma. It contains $L$ and $U$,
so equals $H$. Thus $[H:U]\le e$. As $R\subseteq H$, both inequalities force $R=H$. Hence
$L\subseteq R$, with all required equations, roots of unity and the isometric embedding. For $e=1$
the same comparison gives $LU=U$ and the empty list works. Dependencies:
lem-trf-valued-extension-degree-bound, lem-weil-pbc-finite-dimensional-domain-is-field.

9. Conversely assume (b). Apply the valuation-etale-factor lemma to $D=U^\circ$ over $K^\circ$ and
its maximal ideal. Since $U^\circ$ is already local, the factor is itself; its fraction field is
$U$. The lemma gives separable residue extension and $[U:K]=f(U/K)$; the fundamental inequality
gives $e(U/K)=1$. Thus $U/K$ satisfies (a). Write $R_0=U$ and $R_i=U(\alpha_1,\ldots,\alpha_i)$.
For each $i$, $R_{i-1}$ contains all $n_i$-th roots of unity, $n_i$ is invertible there, and
$a_i\in U^\times\subseteq R_{i-1}^\times$. The multiradical Galois-degree lemma with one radical
and exponent $n_i$ gives $R_i/R_{i-1}$ finite Galois and $[R_i:R_{i-1}]\mid n_i$. This application
makes no irreducibility assumption on the binomial and includes $n_i=1$. Dependencies:
lem-trf-henselian-valuation-etale-local-factors, lem-trf-valued-extension-degree-bound,
lem-sfb-multiradical-galois-degree.

10. Apply the Galois graded-wild-kernel lemma to each $R_i/R_{i-1}$. If $p>0$, its wild subgroup
has $p$-power order, whereas the Galois group has order prime to $p$: the fixed-field lemma
identifies its order with the degree in step 9. Hence that subgroup is trivial, its fixed field is
$R_i$, and the lemma gives $[R_i:R_{i-1}]=e(R_i/R_{i-1})f(R_i/R_{i-1})$, separable residue
extension and prime-to-$p$ index. If $p=0$, the same lemma states directly that the wild subgroup
is trivial, with the same conclusions and no index restriction. All bases are complete by step 1;
their residue characteristic remains $p$. Dependencies: lem-trf-galois-graded-wild-kernel,
lem-weil-pbc-finite-galois-fixed-field.

11. Starting with $U/K$ and the successive radical extensions, multiply the tower invariants from
step 2. Transitivity of residue separability gives separable $\widetilde R/\widetilde K$, the
product of the indices is prime to $p$ if $p>0$, and $d(R/K)=1$. Identify $L$ with its image in
$R$ under the embedding in (b); it is a valued embedding by hypothesis. In $K\subseteq L\subseteq
R$, multiplicativity gives $d(R/K)=d(R/L)d(L/K)$ with both factors at least one. Thus $d(L/K)=1$.
Also $e(L/K)$ divides $e(R/K)$, and $\widetilde L/\widetilde K$ is separable because every element
lies in the separable extension $\widetilde R/\widetilde K$. These are exactly the three
assertions in (a). When the list is empty the argument simply starts with $R=U$. Dependencies:
lem-trf-valued-extension-degree-bound, lem-zl-separable-permanence. -/
theorem tame_root_envelope_iff
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type v) [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
    [FiniteDimensional K L] (A : ValuationSubring L)
    (_hA : A = (NormedField.valuation (K := L)).valuationSubring)
    (Ω : Type w) [NormedField Ω] [NormedAlgebra K Ω] [IsUltrametricDist Ω]
    [IsAlgClosure K Ω] (B : ValuationSubring Ω)
    (_hB : B = (NormedField.valuation (K := Ω)).valuationSubring) :
    (Module.finrank K L =
        ((QuotientGroup.mk' A.unitGroup).comp
          (Units.map (algebraMap K L).toMonoidHom)).range.index *
        @Module.finrank
          (IsLocalRing.ResidueField (A.comap (algebraMap K L)))
          (IsLocalRing.ResidueField A) inferInstance inferInstance
          (@Algebra.toModule
            (IsLocalRing.ResidueField (A.comap (algebraMap K L)))
            (IsLocalRing.ResidueField A) inferInstance inferInstance
            (A.comapResidueAlgebra (algebraMap K L))) ∧
      @Algebra.IsSeparable
        (IsLocalRing.ResidueField (A.comap (algebraMap K L)))
        (IsLocalRing.ResidueField A) inferInstance inferInstance
        (A.comapResidueAlgebra (algebraMap K L)) ∧
      (0 < ringChar (IsLocalRing.ResidueField (A.comap (algebraMap K L))) →
        Nat.Coprime
          ((QuotientGroup.mk' A.unitGroup).comp
            (Units.map (algebraMap K L).toMonoidHom)).range.index
          (ringChar (IsLocalRing.ResidueField (A.comap (algebraMap K L)))))) ↔
    ∃ U : IntermediateField K Ω, FiniteDimensional K U ∧
      ∃ C : ValuationSubring U, C = B.comap U.val ∧
      @Module.Finite (C.comap (algebraMap K U))
        C inferInstance inferInstance
        (@Algebra.toModule (C.comap (algebraMap K U))
          C inferInstance inferInstance
          ((algebraMap K U).restrict (C.comap (algebraMap K U)) C
            (fun _ h ↦ h)).toAlgebra) ∧
      @Algebra.Etale (C.comap (algebraMap K U))
        C inferInstance inferInstance
        ((algebraMap K U).restrict (C.comap (algebraMap K U)) C
            (fun _ h ↦ h)).toAlgebra ∧
      ∃ (s : ℕ) (n : Fin s → ℕ) (a : Fin s → Uˣ) (α : Fin s → Ω),
        (∀ i : Fin s, 0 < n i) ∧
        (∀ i : Fin s,
          0 < ringChar (IsLocalRing.ResidueField (A.comap (algebraMap K L))) →
            Nat.Coprime (n i)
              (ringChar (IsLocalRing.ResidueField (A.comap (algebraMap K L))))) ∧
        (∀ i : Fin s, α i ^ n i = algebraMap U Ω (a i : U)) ∧
        (∀ (i : Fin s) (ζ : Ω), ζ ^ n i = 1 → ζ ∈ U) ∧
        ∃ j : L →ₐ[K] IntermediateField.adjoin U (Set.range α),
          ∀ x : L, ‖(j x : Ω)‖ = ‖x‖ := by
  sorry

end IntermediateField
