/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.RingTheory.SerreConditions
import Sheaf.RingTheory.UniversallyCatenaryDimensionFormula
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.GoingDown
import Sheaf.RingTheory.FaithfullyFlatNormalRingDescent
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.Exactness
import WeilConjectures.RingTheory.CompletionFiniteExtension
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import WeilConjectures.RingTheory.FlatUnderRegular
import WeilConjectures.RingTheory.FormalFibreQuotientIso
import WeilConjectures.RingTheory.GRingCompletionRegular
import WeilConjectures.RingTheory.GRingMaximalIdealCriterion
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import WeilConjectures.RingTheory.SerreCriterionNormal
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The least generic formal singular height

Source: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Theorem 5.1, Step 2, (5.1)–(5.6), Claim 5.2, pp.9–11, and the consequence on p.13
(blueprint: lem-per-gabber-minimal-formal-defect).

The helper definitions are the constructions explicitly introduced in this node: its
principal-adic local completion, canonical map, singular locus and set of generic
minimal singular heights. Normalization itself is Mathlib's `integralClosure`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace GabberFormalDefect

/-- The `x`-adic completion of `B` localized at `n`, not its maximal-adic completion.
Source: Kurano–Shimomoto, Theorem 5.1, Step 2, preceding (5.1), p.9
(blueprint: lem-per-gabber-minimal-formal-defect). -/
abbrev completion (B : Type u) [CommRing B] (x : B) (n : PrimeSpectrum B) : Type u :=
  AdicCompletion (Ideal.span {algebraMap B (Localization.AtPrime n.asIdeal) x})
    (Localization.AtPrime n.asIdeal)

/-- The canonical composite from `B` to its localized principal-adic completion.
Source: Kurano–Shimomoto, Theorem 5.1, Step 2, the cofiber squares on pp.9–10
(blueprint: lem-per-gabber-minimal-formal-defect). -/
noncomputable def toCompletion (B : Type u) [CommRing B] (x : B)
    (n : PrimeSpectrum B) : B →+* completion B x n :=
  (algebraMap (Localization.AtPrime n.asIdeal) (completion B x n)).comp
    (algebraMap B (Localization.AtPrime n.asIdeal))

/-- The singular locus consists of primes whose local rings are not regular local.
Source: Kurano–Shimomoto, Section 4, notation preceding Lemma 4.2, and Step 2, p.9
(blueprint: lem-per-gabber-minimal-formal-defect). -/
def singularLocus (T : Type u) [CommRing T] : Set (PrimeSpectrum T) :=
  {p | ¬ IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

/-- The minimal singular primes of the completed local ring contracting to zero in `B`.
Source: Kurano–Shimomoto, Theorem 5.1, Step 2, definition of `S_L` before (5.2), p.9
(blueprint: lem-per-gabber-minimal-formal-defect). -/
def genericMinimalSingularPrimes (B : Type u) [CommRing B] (x : B)
    (n : PrimeSpectrum B) : Set (PrimeSpectrum (completion B x n)) :=
  {s | Minimal (fun p => p ∈ singularLocus (completion B x n)) s ∧
    s.asIdeal.comap (toCompletion B x n) = ⊥}

/-- The heights of all triples in `S`, retaining the extended dimension values.
The two algebra structures and their scalar-tower condition specify the canonical
restriction of the fraction-field action. Finite field extensions admit representatives
in the base universe; the identity extension is included.
Source: Kurano–Shimomoto, Theorem 5.1, Step 2, (5.2), p.9
(blueprint: lem-per-gabber-minimal-formal-defect). -/
def genericSingularHeights (R : Type u) [CommRing R] [IsDomain R] (x : R) :
    Set (WithBot ℕ∞) :=
  {d | ∃ (L : Type u) (_ : Field L) (_ : Algebra R L)
    (_ : Algebra (FractionRing R) L) (_ : IsScalarTower R (FractionRing R) L)
    (_ : Module.Finite (FractionRing R) L) (n : PrimeSpectrum (integralClosure R L)),
    n.asIdeal.IsMaximal ∧
      ∃ s ∈ genericMinimalSingularPrimes (integralClosure R L)
        (algebraMap R (integralClosure R L) x) n,
        ringKrullDim (Localization.AtPrime s.asIdeal) = d}

/-- The least generic formal singular height is at least two, and controls excellence
of all localizations of the base and its finite normalizations up to that height.
Source: Kurano–Shimomoto, Theorem 5.1, Step 2, (5.1)–(5.6), Claim 5.2, pp.9–11,
and the low-height normalization consequence on p.13
(blueprint: lem-per-gabber-minimal-formal-defect).

Proof plan, with the DAG inputs named at their use:

1. Fix $L,\mathfrak n$, and abbreviate $B=B_L$, $A=B_{\mathfrak n}$, $\mathfrak m=\mathfrak nA$,
$C=C_{L,\mathfrak n}$. A finite module algebra is finite type (its module generators also
generate it as an algebra). Hence $B$ is Noetherian by
[lem-weil-pbc-finite-type-algebra-noetherian], $A$ is Noetherian by
[lem-weil-pbc-localization-noetherian], and $C$ is Noetherian by
[lem-weil-pbc-adic-completion-noetherian]. By [lem-weil-pbc-adic-complete-jacobson-radical], $x$
belongs to every maximal ideal of $B$, so $x\in\mathfrak m$. By
[lem-weil-pbc-adic-completion-mod-ideal], $C$ is $xC$-adically complete and $C/xC=A/xA$.

2. The quotient $C/xC=A/xA$ is local and $xC$ is in the Jacobson radical by
[lem-weil-pbc-adic-complete-jacobson-radical]. Thus $C$ is local, with maximal ideal $\mathfrak
mC$, and $A\to C$ is local. For each $j\geq1$, exact completion of $0\to\mathfrak m^j\to A\to
A/\mathfrak m^j\to0$, together with its finite-module tensor description, gives $C/\mathfrak
m^jC\cong(A/\mathfrak m^j)^{\wedge(x)}=A/\mathfrak m^j$: the last completion stabilizes because
$x^j\in\mathfrak m^j$. These isomorphisms are induced by $A\to C$, hence commute with all
quotient transitions. Taking inverse limits identifies $\widehat C=\widehat A$, compatibly with
the maps from $A$ and $C$. This is a short quotient calculation, not an extra completion
theorem.

3. By [lem-per-quasi-excellent-localization], $A/xA$ is quasi-excellent, since it is a
localization of the assumed quasi-excellent ring $B/xB$. In particular it is a G-ring. Apply
[lem-per-local-g-ring-adic-lifting] to the local complete pair $(C,xC)$ from steps 1–2: $C$ is a
G-ring. Apply [lem-per-semilocal-g-ring-j2] to this local ring: it is quasi-excellent and
therefore has closed singular locus. The map $C\to\widehat C=\widehat A$ is regular by
[lem-weil-pbc-g-ring-completion-regular] and faithfully flat by
[lem-weil-pbc-local-completion-faithfully-flat]. The target is a normal local domain by the
assumption on the maximal-adic completion of $(B_L)_{\mathfrak n}$. Hence
[lem-sfb-faithfully-flat-normal-ring-descent] makes $C$ normal; as a local normal ring it is a
domain. This proves every assertion about each individual $C_{L,\mathfrak n}$.

4. We record why only generic formal fibres can fail. For primes $0\ne\mathfrak
t\subseteq\mathfrak p$ of $R$, $R/\mathfrak t$ is quasi-excellent by hypothesis; its
localization at $\mathfrak p/\mathfrak t$ is quasi-excellent by
[lem-per-quasi-excellent-localization]. Its completion map is regular by
[lem-weil-pbc-g-ring-completion-regular]. The generic fibre of that map is geometrically
regular, and [lem-weil-pbc-formal-fibre-quotient-iso] identifies it with the fibre over
$\mathfrak t$ of $R_{\mathfrak p}\to\widehat{R_{\mathfrak p}}$. Thus all nonzero-prime fibres of
every such completion map are geometrically regular.

5. The quotient $R/xR$ is quasi-excellent since $xR\ne0$, and $xR$ is in the Jacobson radical by
[lem-weil-pbc-adic-complete-jacobson-radical]. If $R$ were a G-ring,
[lem-per-g-ring-quasi-excellent-closed-fibre] would make it quasi-excellent, contrary to
hypothesis. By [lem-weil-pbc-g-ring-maximal-ideal-criterion], choose a maximal ideal $\mathfrak
m$ whose local completion map is not regular. It is flat by
[lem-weil-pbc-local-completion-faithfully-flat], so step 4 shows that its generic fibre
$F=K\otimes_R\widehat{R_{\mathfrak m}}$, $K=\operatorname{Frac}R$, is not geometrically regular.
This ring is Noetherian: it is a localization of a Noetherian completion. By
[def-weil-pbc-g-ring], there is a finite purely inseparable extension $L/K$ such that
$L\otimes_K F$ is not regular. This includes the degree-one extension; no characteristic
assumption is used.

6. For any finite extension $L/K$ put $B=B_L$. Then $(R\setminus\{0\})^{-1}B=L$: given $z\in L$,
choose a monic equation $z^r+\sum_{i<r}a_i z^i=0$ over $K$ and a common nonzero denominator
$d\in R$ for the $a_i$. The equation for $dz$ has coefficients $d^{r-i}a_i\in R$, so $dz\in B$
and $z=(dz)/d$. For any prime $\mathfrak p$ of $R$, apply
[lem-weil-pbc-completion-finite-extension] to the finite $R$-algebra $B$, then invert all
nonzero elements of $B$, using [lem-weil-pbc-localization-base-change] and
[lem-weil-pbc-tensor-cancel-base-change]. It gives $$L\otimes_K(K\otimes_R\widehat{R_{\mathfrak
p}})\cong\prod_{\mathfrak q\cap R=\mathfrak p}\bigl(L\otimes_B\widehat{B_{\mathfrak q}}\bigr).$$
The product is finite. A finite product is regular exactly when each factor is regular: a prime
selects one factor (the coordinate idempotents are orthogonal and sum to one), its local ring is
that factor's local ring, and a finite product is Noetherian exactly when its factors are. These
are componentwise ideal and localization calculations. This is the scalar identity used in the
source's two cofiber squares.

7. Apply step 6 to the $L$ and $\mathfrak m$ chosen in step 5. Since its left side is not
regular, some factor $L\otimes_B\widehat{B_{\mathfrak n}}$, for a prime $\mathfrak n$ of $B$
over $\mathfrak m$, is not regular; $\mathfrak n$ is a maximal ideal by
[lem-weil-pbc-integral-prime-over-maximal-maximal], since $B$ is integral over $R$ and
$\mathfrak m$ is maximal. Put $C=C_{L,\mathfrak n}$. If $L\otimes_B C$ were regular, every local
ring of $\widehat{B_{\mathfrak n}}$ at a prime over $(0)\subset B$ would be regular: the
corresponding local ring of $C$ is regular, and the local map is flat with regular closed fibre
because $C\to\widehat C=\widehat{B_{\mathfrak n}}$ is regular (step 3). Apply
[lem-weil-pbc-flat-over-regular-with-regular-fibre]. This contradicts the chosen factor. Thus
$L\otimes_B C$ is not regular, and has a singular prime, corresponding to a singular prime of
$C$ contracting to zero in $B$. Since $\operatorname{Sing}C$ is closed, write it as $V(J)$;
[lem-weil-pbc-prime-contains-minimal-prime] supplies a prime minimal over $J$ below that
singular prime. Its contraction to $B$ is still zero. It therefore gives a member of $\mathcal
S$.

8. Every prime in each Noetherian $C$ has finite natural height by
[lem-trf-noetherian-prime-finite-height]. The nonempty set of these natural heights therefore
has a least element $h$, realized by a triple. Each $C$ is normal by step 3, hence satisfies
$(R_1)$ by [lem-weil-pbc-serre-criterion-normal]. By the definition of $(R_1)$ in
[def-weil-pbc-serre-conditions-rk-sk], a singular prime cannot have height zero or one. Hence
$h\geq2$.

9. Fix $0\ne\mathfrak p\subset R$ with $\operatorname{ht}\mathfrak p\leq h$, and let $L/K$ be
any finite extension. Put $B=B_L$ and take any prime $\mathfrak q$ of $B$ over $\mathfrak p$. By
[lem-exc-dimension-formula-universally-catenary-finite-type-domain],
$0<\operatorname{ht}\mathfrak q=\operatorname{ht}\mathfrak p\leq h$: both the fraction-field and
residue-field extensions are algebraic. Choose a maximal $\mathfrak n\supseteq\mathfrak q$ and
put $C=C_{L,\mathfrak n}$, $A=B_{\mathfrak q}$. The map $B_{\mathfrak n}\to C$ is flat by
[lem-weil-pbc-noetherian-completion-flat] and local by step 2, hence faithfully flat by
[lem-pc-local-flat-faithful-flat-reflects-surjective]. Thus $\mathfrak qC$ is proper:
[lem-weil-pbc-faithfully-flat-surjective-spectrum] gives a prime over $\mathfrak qB_{\mathfrak
n}$. Choose $Q$ minimal over $\mathfrak qC$ using
[lem-weil-pbc-minimal-prime-over-proper-ideal]. Its contraction to $B$ equals $\mathfrak q$,
since otherwise [lem-sc-flat-going-down] would produce a smaller prime over $\mathfrak q$ still
containing $\mathfrak qC$. The flat local map $\alpha:A\to C_Q$ has zero-dimensional closed
fibre, since $Q$ is minimal over $\mathfrak qC$. Thus [lem-weil-pbc-flat-height-formula] gives
$\operatorname{ht}Q=\operatorname{ht}\mathfrak q\leq h$.

10. Put $T=\widehat{C_Q}$. By [lem-weil-pbc-localization-noetherian] and
[lem-weil-pbc-adic-completion-noetherian], these local rings are Noetherian. The map
$\widehat\alpha:\widehat A\to T$ is flat by [lem-weil-pbc-flat-completion], and it is local
since the compatible completion map carries the extended maximal ideal of $A$ into that of
$C_Q$; the description of these maximal ideals is [lem-weil-pbc-local-completion-local-ring]. It
is faithfully flat by [lem-pc-local-flat-faithful-flat-reflects-surjective]. Since $C$ is a
G-ring, the map $C_Q\to T$ is regular by [def-weil-pbc-g-ring].

11. Write $\operatorname{Sing}C=V(J)$, and let $s_1,\ldots,s_r$ be its minimal singular primes
contained in $Q$; there are finitely many by [lem-sc-finite-minimal-primes-over-ideal]. If
$s_i\subsetneq Q$, appending this strict inclusion to a chain realizing its finite height shows
$\operatorname{ht}s_i<\operatorname{ht}Q\leq h$. Hence $s_i\cap B\ne0$, since otherwise
$(L,\mathfrak n,s_i)\in\mathcal S$ would contradict the minimality of $h$. If $s_i=Q$, its
contraction is the nonzero ideal $\mathfrak q$. Choose $0\ne b_i\in s_i\cap B$ and put
$b=\prod_i b_i$, with $b=1$ if $r=0$. Then $b\ne0$ since $B$ is a domain. This is a common
element in all surviving singular components.

12. We claim $T[1/b]$ is regular. For a prime $P\subset T$ avoiding $b$, contract it to
$s\subseteq Q$ in $C$. If $C_s$ were singular, [lem-weil-pbc-prime-contains-minimal-prime] would
give a minimal singular prime $s_i\subseteq s$, one of those in step 11, forcing $b\in P$, a
contradiction. Thus $C_s$ is regular. The map $C_s\to T_P$ is flat local with regular closed
fibre: the fibre is a localization of a geometrically regular fibre of $C_Q\to T$ (step 10), so
it is regular by [lem-weil-pbc-localization-of-regular-ring]. Apply
[lem-weil-pbc-flat-over-regular-with-regular-fibre] to get regularity of $T_P$. Localization
preserves Noetherianity by [lem-weil-pbc-localization-noetherian], proving the claim. This
pointwise argument avoids an unstated comparison of singular ideals under completion.

13. The map $\widehat\alpha:\widehat A\to T$ is faithfully flat (step 10). By
[lem-weil-pbc-faithfully-flat-surjective-spectrum], every prime $P$ of $\widehat A$ avoiding $b$
lifts to a prime of $T$, also avoiding $b$. The resulting local map is flat, and its target is
regular by step 12. Thus [lem-weil-pbc-flat-under-regular] gives regularity of $\widehat A_P$.
Every prime of $L\otimes_B\widehat A$ avoids the nonzero $b$, and localization preserves
regularity by [lem-weil-pbc-localization-of-regular-ring]. Hence
$L\otimes_B\widehat{B_{\mathfrak q}}$ is regular. We have proved this for every finite $L/K$ and
every $\mathfrak q$ over $\mathfrak p$. Step 6 now makes
$L\otimes_K(K\otimes_R\widehat{R_{\mathfrak p}})$ regular for every finite $L/K$, in particular
for every finite purely inseparable extension. By [def-weil-pbc-g-ring], the generic fibre of
$R_{\mathfrak p}\to\widehat{R_{\mathfrak p}}$ is geometrically regular. Step 4 treats every
nongeneric fibre; the completion map is flat by [lem-weil-pbc-local-completion-faithfully-flat].
It is therefore regular.

14. By [lem-weil-pbc-g-ring-maximal-ideal-criterion], the local ring $R_{\mathfrak p}$ is a
G-ring, since its only maximal-local completion map is the regular map of step 13. Then
[lem-per-semilocal-g-ring-j2] makes $R_{\mathfrak p}$ quasi-excellent. It is universally
catenary by the definition in [def-exc-excellent-ring]: if $D$ is generated by $d_1,\ldots,d_t$
over $R_{\mathfrak p}$, let $D_0$ be the $R$-subalgebra generated by these elements. The
canonical map $(R\setminus\mathfrak p)^{-1}D_0\to D$ is surjective by the generators and
injective since the denominators are already units in $D$. Between two primes surviving a
localization every intermediate prime also survives, so the saturated chains and their lengths
agree. Universal catenarity of $R$ therefore supplies it for $R_{\mathfrak p}$. Thus
$R_{\mathfrak p}$ is excellent. At $\mathfrak p=0$, the local ring is the field $K$, excellent
by [lem-exc-fields-excellent].

15. Finally fix $L$ and $\mathfrak q\subset B_L$ of height at most $h$, and put $\mathfrak
p=\mathfrak q\cap R$. Apply [lem-exc-dimension-formula-universally-catenary-finite-type-domain]
to the finite extension of domains $R\subset B_L$: its fraction field extension and its residue
field extension at $\mathfrak q$ are algebraic, so both transcendence degrees are zero and
$\operatorname{ht}\mathfrak p=\operatorname{ht}\mathfrak q\leq h$. Hence $R_{\mathfrak p}$ is
excellent by step 14. The algebra $B_L\otimes_R R_{\mathfrak p}$ is finite, hence finite type
over this ring, and $(B_L)_{\mathfrak q}$ is its localization. Apply
[lem-exc-finite-type-localization-excellent] to obtain excellence of $(B_L)_{\mathfrak q}$. This
includes height zero, where the localizations are fields.
-/
theorem minimal_formal_defect
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (hNagata : IsNagataRing R) (x : R)
    (hx : x ≠ 0) (hxunit : ¬ IsUnit x)
    (hcomplete : IsAdicComplete (Ideal.span {x}) R)
    (hcatenary : IsUniversallyCatenary R) (hnotqe : ¬ IsQuasiExcellent R)
    (hquot : ∀ K : Ideal R, K ≠ ⊥ → IsQuasiExcellent (R ⧸ K))
    (hB : ∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
      [IsScalarTower R (FractionRing R) L] [Module.Finite (FractionRing R) L],
      Module.Finite R (integralClosure R L) ∧
      (∀ q : PrimeSpectrum (integralClosure R L),
        IsDomain (Localization.AtPrime q.asIdeal) ∧
          IsIntegrallyClosed (Localization.AtPrime q.asIdeal)) ∧
      IsNagataRing (integralClosure R L) ∧
      IsUniversallyCatenary (integralClosure R L) ∧
      IsAdicComplete (Ideal.span {algebraMap R (integralClosure R L) x})
        (integralClosure R L) ∧
      IsQuasiExcellent ((integralClosure R L) ⧸
        Ideal.span {algebraMap R (integralClosure R L) x}) ∧
      ∀ n : PrimeSpectrum (integralClosure R L), n.asIdeal.IsMaximal →
        IsLocalRing (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal))
          (Localization.AtPrime n.asIdeal)) ∧
        IsDomain (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal))
          (Localization.AtPrime n.asIdeal)) ∧
        IsIntegrallyClosed (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal))
          (Localization.AtPrime n.asIdeal))) :
    (∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
      [IsScalarTower R (FractionRing R) L] [Module.Finite (FractionRing R) L]
      (n : PrimeSpectrum (integralClosure R L)), n.asIdeal.IsMaximal →
      IsNoetherianRing (completion (integralClosure R L)
        (algebraMap R (integralClosure R L) x) n) ∧
      IsLocalRing (completion (integralClosure R L)
        (algebraMap R (integralClosure R L) x) n) ∧
      (∀ p : PrimeSpectrum (completion (integralClosure R L)
          (algebraMap R (integralClosure R L) x) n),
        IsDomain (Localization.AtPrime p.asIdeal) ∧
          IsIntegrallyClosed (Localization.AtPrime p.asIdeal)) ∧
      IsGRing (completion (integralClosure R L)
        (algebraMap R (integralClosure R L) x) n) ∧
      IsClosed (singularLocus (completion (integralClosure R L)
        (algebraMap R (integralClosure R L) x) n))) ∧
    ∃ h : ℕ, 2 ≤ h ∧ IsLeast (genericSingularHeights R x) (h : WithBot ℕ∞) ∧
      (∀ p : PrimeSpectrum R,
        ringKrullDim (Localization.AtPrime p.asIdeal) ≤ (h : WithBot ℕ∞) →
          IsExcellent (Localization.AtPrime p.asIdeal)) ∧
      (∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
        [IsScalarTower R (FractionRing R) L] [Module.Finite (FractionRing R) L]
        (q : PrimeSpectrum (integralClosure R L)),
        ringKrullDim (Localization.AtPrime q.asIdeal) ≤ (h : WithBot ℕ∞) →
          IsExcellent (Localization.AtPrime q.asIdeal)) :=
  sorry

end GabberFormalDefect
