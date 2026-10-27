module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.TraceOneInvariantFiniteness
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Lasker
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.RingTheory.CompletionFiniteExtension
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.ExcellentRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Nakayama
import WeilConjectures.RingTheory.FiniteModuleComplete
import WeilConjectures.RingTheory.LocalCompletionQuotient
import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
import Sheaf.RingTheory.FilteredColimitFiniteData
import WeilConjectures.RingTheory.FiniteMapColimitDescent
import Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct

/-!
# Marked invariant algebras descend to a polynomial cylinder

Source: ILO, Travaux de Gabber, Expose V, 2.2.1--2.2.8 and 3.2.2--3.2.4,
printed pp. 65--68 (blueprint: lem-per-equivariant-marked-cylinder-algebraization).
-/

@[expose] public section

universe u v

namespace RingTheory

/-- Marked invariant algebras descend after an equivariant change of formal coordinates.
Source: ILO, Expose V, 2.2.1--2.2.8 and 3.2.2--3.2.4, pp. 65--68
(blueprint: lem-per-equivariant-marked-cylinder-algebraization).

The `n + 1` variables encode every positive number of variables. The images under `c`
of the standard variables are the new coordinates. The equality defining `d` specifies
its value on all formal series. The completion equivalence is linear for that precise
coefficient inclusion, and transports all the marked ideals simultaneously.

Proof plan:

1. The element $1/|H|$ has trace one. Apply [lem-per-trace-one-noetherian-invariant-finiteness] to
$V$ and to $B$: $V$ is finite over $\Lambda$, and $A_0=B^H$ is Noetherian. The ring $A_0$ is
local: an invariant element outside $\mathfrak m_B$ has invariant inverse. It is a normal domain:
an element of $\operatorname{Frac}(A_0)$ integral over $A_0$ lies in $B$ by normality of $B$, and
is fixed by $H$, hence lies in $A_0$. Set $R_\Lambda=\Lambda[[t_1,\ldots,t_r]]$. The formal-ring
finiteness clause of [lem-per-finite-coefficient-henselian-cylinder], applied with $e=r-1$ and
$T=t_r$, makes $V[[t]]$ finite over $R_\Lambda$. Thus $B$ is finite over $R_\Lambda$. This ring is
Noetherian by [lem-weil-pbc-power-series-noetherian], so its submodule $A_0\subset B$ is finite by
[lem-weil-pbc-noetherian-submodule-finite].

2. By [lem-per-noetherian-primary-decomposition], write each marking as a finite intersection of
primary ideals $Q$. For $I_i=A_0$ use the empty intersection. Keep $Q=0$ separately; it already
descends as the zero ideal of every model. For every remaining $Q$,
[lem-per-normal-finite-primary-dichotomy] gives either $g_Q\in Q\cap R_\Lambda$ with nonzero
reduction modulo $\mathfrak m_\Lambda$, or, in the DVR case, $Q=P^{(n)}$ with $P$ a height-one
prime containing a fixed uniformizer $\pi\in\Lambda$. All its hypotheses were established in step
1. Call the first list the scalar-annihilated components and the second the vertical components.

3. Replace the ramification denominator $f$ by its norm $F_0=\prod_{h\in H}h(f)$. It lies in
$R_\Lambda$: fixed power series have fixed coefficients, and $H$ fixes all variables. Its
reduction modulo $\mathfrak m_V$ is a product of nonzero series, hence nonzero; since $\mathfrak
m_V\cap\Lambda=\mathfrak m_\Lambda$, its reduction over $\Lambda$ is nonzero. Inverting $F_0$ also
inverts $f$. Multiply $F_0$, all the finitely many $g_Q$, and $t_r$ to form $F\in\mathfrak
m_{R_\Lambda}$, still nonzero modulo $\mathfrak m_\Lambda$. Apply
[lem-per-weierstrass-henselian-cylinder] to $F$. The shear substitutions $t_i\mapsto
t_i+t_r^{N_i}$ have coefficients in $\Lambda$ and commute with $H$. Equivalently use their inverse
to choose formal coordinates $u_i$, with $T=u_r$, in which $F$ is a unit times a distinguished
polynomial $g\in D[T]$ of positive degree, where $D=\Lambda[[u_1,\ldots,u_{r-1}]]$. Set $R=D[[T]]$
and $S=(D[T]_{(\mathfrak m_D,T)})^h$. The cited node identifies $R$ with both completions of $S$.

4. Put $E=V[[u_1,\ldots,u_{r-1}]]$, $S_V=(E[T]_{(\mathfrak m_E,T)})^h$, and $R_V=E[[T]]$. Apply
[lem-per-finite-coefficient-henselian-cylinder]: $S_V$ is finite local over $S$, $S$ is excellent,
$(S_V,gS_V)$ is henselian, its $g$-adic completion is $R_V$, and $R\otimes_S S_V\cong R_V$. Each
coefficient automorphism of $V$ extends to $S_V$ by the unique local henselian extension; this
gives its $H$-action and fixes $S$ and $g$. The finite $R_V$-algebra $B$ is etale away from $g$,
since $F$ is a multiple of $f$ and a unit times $g$. Apply
[lem-per-elkik-finite-etale-away-completion] to the Noetherian henselian pair $(S_V,gS_V)$. Obtain
a finite $S_V$-algebra $\widetilde B$, etale away from $g$, with $R_V\otimes_{S_V}\widetilde
B\cong B$.

5. For $h\in H$, twist the $S_V$-algebra structure on $\widetilde B$ by $h^{-1}$. Its completed
twist is the corresponding twist of $B$, and the given action map $h$ identifies this with $B$ as
an algebra. Full faithfulness in [lem-per-elkik-finite-etale-away-completion] lifts this
isomorphism uniquely to the twisted model. Its inverse lifts too, so it is an isomorphism. For
$h,k$, the two lifts representing $hk$ and the composite of the lifts for $h$ and $k$ agree after
completion; faithfulness makes them equal. The identity lifts to the identity. This constructs the
required semilinear action on $\widetilde B$ and makes the displayed completion isomorphism
equivariant.

6. Set $A=\widetilde B^H$. Since $\widetilde B$ is finite over $S_V$ and $S_V$ is finite over the
Noetherian ring $S$, [lem-weil-pbc-noetherian-submodule-finite] makes $A$ finite over $S$. Compute
invariants as the kernel of $x\mapsto(hx-x)_{h\in H}$ from $\widetilde B$ to the finite product of
its copies, viewed as $S$-modules. The map $S\to R$ is flat by step 3, so
[lem-weil-pbc-flat-tensor-exact] identifies $$R\otimes_S A=(R\otimes_S\widetilde B)^H=B^H=A_0,$$
using step 4. By [lem-weil-pbc-completion-finite-module-tensor] this tensor product is the
maximal-ideal-of-$S$ completion of $A$. By [lem-weil-pbc-finite-over-henselian-local-product], $A$
is a finite product of henselian local rings. The completed product is the nonzero local ring
$A_0$, so it has exactly one factor: every other factor would have a nonzero residue field and
hence nonzero completion. Thus $A$ is local henselian, and the completion in question is also its
maximal-ideal completion by [lem-weil-pbc-completion-finite-extension].

7. The ring $A$ is excellent by [lem-exc-finite-type-localization-excellent], since it is finite
over the excellent ring $S$. It is Noetherian by the same excellent-ring convention
[def-exc-excellent-ring]. By [lem-weil-pbc-local-completion-faithfully-flat] and
[lem-weil-pbc-faithfully-flat-ideal-contraction], $A\hookrightarrow\widehat A=A_0$ and $bA_0\cap
A=bA$ for $b\in A$. In particular $A$ is a domain. To check normality, write an element of its
fraction field integral over $A$ as $x=a/b$. It lies in $A_0$ by normality of $A_0$; thus $a\in
bA_0\cap A=bA$, and $x\in A$. We may therefore apply the excellent henselian normal-domain
completion input to $A$.

8. For a scalar-annihilated component $Q$, $g_Q$ divides $F$ in $R$, so $g$ annihilates $A_0/Q$.
By [lem-per-distinguished-polynomial-quotient], $R/(g)=D[T]/(g)$ is finite over $D$ (the classes
of $1,T,\ldots,T^{\deg g-1}$ generate it). Since $A_0$ is finite over $R$, $M=A_0/Q$ is finite
over $D$, hence over $A$. Let $N$ be the image of $A$ in $M$. Maximal-ideal completion gives
$M=N+\mathfrak m_A M$, because $A\to A_0$ is surjective modulo $\mathfrak m_AA_0$. Therefore
$\mathfrak m_A(M/N)=M/N$. Apply [lem-weil-pbc-nakayama-jacobson] to the finite $A$-module $M/N$:
it is zero. Thus $A\to M$ is surjective. Put $K=\ker(A\to M)$.

9. Here $M$ is $\mathfrak m_D$-adically complete by
[lem-weil-pbc-finite-module-complete-over-complete-noetherian]. Since $g$ annihilates $M$ and is
distinguished, $T$ is nilpotent on $M/\mathfrak m_D M$. Hence $M/\mathfrak m_D M$ has finite
length over $S$, and a power of $\mathfrak m_S$ annihilates it. It follows that the $\mathfrak
m_D$-adic and $\mathfrak m_S$-adic filtrations on $M$ are cofinal: for some $c$, $\mathfrak
m_S^{cn}M\subseteq\mathfrak m_D^nM\subseteq\mathfrak m_S^nM$. The maximal-ideal topology from the
finite local extension $S\to A$ is cofinal with the latter, as in
[lem-weil-pbc-completion-finite-extension]. Thus $M$ is already its $\mathfrak m_A$-adic
completion. Apply [lem-weil-pbc-local-completion-quotient] to the surjection $A\to M$: its
completed kernel is $KA_0$, and its completed map is the original quotient $A_0\to A_0/Q$.
Consequently $KA_0=Q$.

10. In the DVR case the vertical components have the form $Q=P^{(n)}$ with $P$ height one and
$\pi\in P$. Such a $P$ is minimal over $\pi A_0$: a prime strictly below it must be zero, which
does not contain the nonzero element $\pi$. Apply [lem-per-vertical-symbolic-powers-completion] to
$A$, $a=\pi$, and $\widehat A=A_0$. Step 7 checked excellence, henselianity and normality, and
step 1 checked normality of $A_0$; $\pi$ is nonzero and lies in $\mathfrak m_A$. We obtain
$P=\mathfrak p A_0$ and $\mathfrak p^{(n)}A_0=P^{(n)}=Q$. Thus this component descends as
$K=\mathfrak p^{(n)}$.

11. For each original $I_i=\bigcap_jQ_{ij}$, let $K_i=\bigcap_jK_{ij}\subset A$, using $K=0$ for
the zero component and the empty intersection $A$ for the unit ideal. Extension commutes with
these finite intersections: $\bigcap_jK_{ij}$ is the kernel of $A\to\bigoplus_j A/K_{ij}$, and
flat tensor exactness [lem-weil-pbc-flat-tensor-exact] identifies its extension to $A_0$ with the
kernel of $A_0\to\bigoplus_j A_0/Q_{ij}$. Therefore $K_iA_0=I_i$. This is equality of ideals,
including their nonreduced structures.

12. Use [lem-per-ordinary-henselian-pointed-neighbourhood-limit] for $D[T]$ at $\mathfrak
q=(\mathfrak m_D,T)$, obtaining a henselian local colimit $H=\varinjlim S_a$ with maximal ideal
$\mathfrak qH$. By [lem-per-pointed-etale-limit-henselization](1), $H$ is a henselization of
$D[T]_{\mathfrak q}$, so the uniqueness in [def-weil-pbc-henselization-at-prime] gives a unique
local $D[T]_{\mathfrak q}$-algebra isomorphism $H\cong S$; we regard each $S_a$ as mapping to $S$
through it. Thus $S=\varinjlim S_a$ with each $S_a$ etale of finite presentation over $D[T]$ and
with a point $\mathfrak q_a$ over $\mathfrak q$ having the same residue field. Present the finite
$S$-algebra $A$ by finitely many generators and relations, and each $K_i$ by finitely many
elements; finiteness of these data follows from Noetherianity of $S,A$. Lift their coefficients to
one stage using [lemma-nagata-filtered-colimit-finite-data]. This produces a finitely presented
$S_a$-algebra $C_a$ and ideals $J_{i,a}$ with $C_a\otimes_{S_a}S\cong A$ carrying the ideals to
$K_i$. Apply [lem-weil-pbc-colimit-finite-ring-map] to make $C_a$ finite over a later $S_a$.

13. Fix this stage and write $C=C_a$, $J_i=J_{i,a}$. The map $C\to A$ takes $\mathfrak m_A$ back
to a maximal ideal $\mathfrak n$ above $\mathfrak q_a$: $C/\mathfrak n$ is an integral domain
finite over the field $S_a/\mathfrak q_a=D/\mathfrak m_D$, hence is a field. In the limit,
$S\otimes_{S_a}C=A$ is local. Base changing its completion gives $$R\otimes_{S_a}C=R\otimes_S
A=A_0.$$ The maximal-ideal completion of $(S_a)_{\mathfrak q_a}$ is $R$: by
[lem-per-pointed-etale-limit-henselization](3), applied to the system of step 12 at the stage $a$
(which still has colimit $S$ by step 12), $(S_a)_{\mathfrak q_a}/\mathfrak q_a^n\to S/\mathfrak
m_S^n$ is an isomorphism for every $n$, compatibly with the maps from $S_a$; and
[lem-per-weierstrass-henselian-cylinder] identifies the maximal-ideal completion of $S$ with $R$.
By [lem-weil-pbc-completion-finite-extension], $R\otimes_{S_a}C$ is the product of the completions
at all primes over $\mathfrak q_a$. It is nonzero local, so there is exactly one such prime and
$$\widehat{C_{\mathfrak n}}\cong A_0.$$ The isomorphism is induced by the specified structural
maps, hence is a $D$-algebra isomorphism, and carries $J_i\widehat{C_{\mathfrak n}}$ onto
$K_iA_0=I_i$.

14. Finally $D[T]\to S_a$ is etale of finite presentation and $S_a\to C$ is finite. Thus $C$ is
finite type over $D[T]$. For every prime $\mathfrak p$ of $D[T]$, the fibre
$S_a\otimes_{D[T]}\kappa(\mathfrak p)$ is etale over $\kappa(\mathfrak p)$ by
[lem-weil-pbc-etale-scheme-base-change], hence unramified by [def-weil-etale-morphism], so
[lem-weil-pbc-unramified-algebra-over-field-product] makes it a finite product of finite separable
field extensions of $\kappa(\mathfrak p)$; tensoring the finite $S_a$-module $C$ with this fibre
gives a finite-dimensional algebra over that residue field. Its spectrum is finite, with finite
residue-field extensions. This proves quasi-finiteness in the stated sense. The previous step
already gives finiteness of $C/\mathfrak n$ over $D/\mathfrak m_D$. All maps restrict on $D$ to
the chosen invariant formal-coordinate inclusion. The construction also applies when $s=0$, and
when $r=1$ the smaller coefficient ring is simply $D=\Lambda$.
-/
theorem exists_equivariant_marked_cylinder_algebraization
    (V B : Type u) [CommRing V] [IsDomain V] [IsLocalRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B]
    [IsNoetherianRing B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (n : ℕ) [Algebra (MvPowerSeries (Fin (n + 1)) V) B]
    [Module.Finite (MvPowerSeries (Fin (n + 1)) V) B]
    [IsLocalHom (algebraMap (MvPowerSeries (Fin (n + 1)) V) B)]
    (hinj : Function.Injective (algebraMap (MvPowerSeries (Fin (n + 1)) V) B))
    (hres : ∃ e : (V ⧸ IsLocalRing.maximalIdeal V) ≃+*
        (B ⧸ IsLocalRing.maximalIdeal B),
      e.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V)) =
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)).comp
          ((algebraMap (MvPowerSeries (Fin (n + 1)) V) B).comp MvPowerSeries.C))
    (H : Type v) [Group H] [Finite H] [MulSemiringAction H V] [MulSemiringAction H B]
    (horder : IsUnit (Nat.card H : V))
    (hequiv : ∀ (h : H) (x : MvPowerSeries (Fin (n + 1)) V),
      algebraMap (MvPowerSeries (Fin (n + 1)) V) B
          (MvPowerSeries.map (MulSemiringAction.toRingHom H V h) x) =
        h • algebraMap (MvPowerSeries (Fin (n + 1)) V) B x)
    (Λ : Subring V) (hΛ : Λ = FixedPoints.subring V H)
    [IsLocalRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ]
    (hkind : (IsField V ∧ Subsingleton H ∧ IsField Λ) ∨
      (IsDiscreteValuationRing V ∧ IsDiscreteValuationRing Λ))
    (f : MvPowerSeries (Fin (n + 1)) V)
    (hred : MvPowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V)) f ≠ 0)
    (hetale : (IsLocalization.Away.map (Localization.Away f)
      (Localization.Away (algebraMap (MvPowerSeries (Fin (n + 1)) V) B f))
      (algebraMap (MvPowerSeries (Fin (n + 1)) V) B) f).Etale)
    (A₀ : Subring B) (hA₀ : A₀ = FixedPoints.subring B H)
    (s : ℕ) (I : Fin s → Ideal A₀) :
    ∃ (c : MvPowerSeries (Fin (n + 1)) V ≃ₐ[V] MvPowerSeries (Fin (n + 1)) V)
      (d : MvPowerSeries (Fin n) Λ →+* A₀),
      (∀ (h : H) (x : MvPowerSeries (Fin (n + 1)) V),
        c (MvPowerSeries.map (MulSemiringAction.toRingHom H V h) x) =
          MvPowerSeries.map (MulSemiringAction.toRingHom H V h) (c x)) ∧
      A₀.subtype.comp d =
        (algebraMap (MvPowerSeries (Fin (n + 1)) V) B).comp
          (c.toRingHom.comp
            ((MvPowerSeries.rename (R := V) Fin.castSucc).toRingHom.comp
              (MvPowerSeries.map Λ.subtype))) ∧
      ∃ (C : Type u) (_ : CommRing C) (a : Polynomial (MvPowerSeries (Fin n) Λ) →+* C)
        (hft : a.FiniteType) (p : PrimeSpectrum C),
        p.asIdeal.IsMaximal ∧
        p.asIdeal.comap a = Ideal.comap Polynomial.constantCoeff
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) Λ)) ∧
        (∀ q : PrimeSpectrum C,
          @Algebra.IsQuasiFiniteAtPrime (Polynomial (MvPowerSeries (Fin n) Λ)) C
            _ _ a.toAlgebra hft q) ∧
        (∃ k : (MvPowerSeries (Fin n) Λ ⧸
              IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) Λ)) →+* (C ⧸ p.asIdeal),
          k.Finite ∧
          k.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) Λ))) =
            (Ideal.Quotient.mk p.asIdeal).comp (a.comp Polynomial.C)) ∧
        ∃ (J : Fin s → Ideal C)
          (e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
            (Localization.AtPrime p.asIdeal) ≃+* A₀),
          (∀ x : MvPowerSeries (Fin n) Λ,
            e (algebraMap (Localization.AtPrime p.asIdeal) _
              (algebraMap C (Localization.AtPrime p.asIdeal) (a (Polynomial.C x)))) = d x) ∧
          ∀ i : Fin s,
            (J i).map (e.toRingHom.comp
              ((algebraMap (Localization.AtPrime p.asIdeal) _).comp
                (algebraMap C (Localization.AtPrime p.asIdeal)))) = I i :=
  sorry

end RingTheory
