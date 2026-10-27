/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.FieldTheory.Finiteness
public import WeilConjectures.RingTheory.GRing
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
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import WeilConjectures.RingTheory.FlatUnderRegular
import WeilConjectures.RingTheory.FormalFibreQuotientIso
import WeilConjectures.RingTheory.GRingCompletionRegular
import WeilConjectures.RingTheory.GRingMaximalIdealCriterion
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.SerreCriterionNormal

/-!
# The least generic formal singular height

Source: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Theorem 5.1, Step 2, (5.1)–(5.6) and Claim 5.2, pp. 9–11, and p. 13
(blueprint: lem-per-qe-minimal-formal-defect).

The two helpers spell out the completion and the indexed pieces of the set S
introduced in the statement. All completion and integral closure data come from Mathlib.
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- The principal-adic completion of a prime localization. Source: Kurano–Shimomoto,
Theorem 5.1, Step 2, before (5.1) (blueprint: lem-per-qe-minimal-formal-defect). -/
abbrev qeFormalCompletion (B : Type u) [CommRing B] (x : B)
    (n : Ideal B) [n.IsPrime] :=
  AdicCompletion (Ideal.span {algebraMap B (Localization.AtPrime n) x})
    (Localization.AtPrime n)

/-- The piece of S indexed by B and n: minimal singular primes contracting to zero in B.
Source: Kurano–Shimomoto, Theorem 5.1, Step 2, definition of S_L preceding (5.2)
(blueprint: lem-per-qe-minimal-formal-defect). -/
def qeGenericMinimalSingularPrimes (B : Type u) [CommRing B] (x : B)
    (n : Ideal B) [n.IsPrime] : Set (PrimeSpectrum (qeFormalCompletion B x n)) :=
  {s | Minimal (fun p : PrimeSpectrum (qeFormalCompletion B x n) ↦
      ¬ IsRegularLocalRing (Localization.AtPrime p.asIdeal)) s ∧
    s.asIdeal.comap
      ((algebraMap (Localization.AtPrime n) (qeFormalCompletion B x n)).comp
        (algebraMap B (Localization.AtPrime n))) = ⊥}

/-- The least generic formal singular height controls excellence in low height.
Source: Kurano–Shimomoto, Theorem 5.1, Step 2, (5.1)–(5.6), Claim 5.2, pp. 9–11,
and the finite-extension consequence on p. 13
(blueprint: lem-per-qe-minimal-formal-defect).

Proof plan (the accepted DAG split):

1. Fix $L,\mathfrak n$, and abbreviate $B=B_L$, $A=B_{\mathfrak n}$, $\mathfrak m=\mathfrak nA$,
$C=C_{L,\mathfrak n}$. A finite module algebra is finite type (its module generators also
generate it as an algebra). Hence $B$ is Noetherian by
[lem-weil-pbc-finite-type-algebra-noetherian], $A$ is Noetherian by
[lem-weil-pbc-localization-noetherian], and $C$ is Noetherian by
[lem-weil-pbc-adic-completion-noetherian]. By [lem-weil-pbc-adic-complete-jacobson-radical], $x$
belongs to every maximal ideal of $B$, so $x\in\mathfrak m$. By
[lem-weil-pbc-adic-completion-mod-ideal], $C$ is $xC$-adically complete and $C/xC=A/xA$.
Uses: lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian,
lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-adic-complete-jacobson-radical,
lem-weil-pbc-adic-completion-mod-ideal.

2. The quotient $C/xC=A/xA$ is local and $xC$ is in the Jacobson radical by
[lem-weil-pbc-adic-complete-jacobson-radical]. Thus $C$ is local, with maximal ideal $\mathfrak
mC$, and $A\to C$ is local. For each $j\geq1$, exact completion of $0\to\mathfrak m^j\to A\to
A/\mathfrak m^j\to0$, together with its finite-module tensor description, gives $C/\mathfrak
m^jC\cong(A/\mathfrak m^j)^{\wedge(x)}=A/\mathfrak m^j$: the last completion stabilizes because
$x^j\in\mathfrak m^j$. These isomorphisms are induced by $A\to C$, hence commute with all
quotient transitions. Taking inverse limits identifies $\widehat C=\widehat A$, compatibly with
the maps from $A$ and $C$. This is a short quotient calculation, not an extra completion
theorem.
Uses: lem-weil-pbc-adic-complete-jacobson-radical, lem-weil-pbc-completion-exact-finite-modules,
lem-weil-pbc-completion-finite-module-tensor.

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
Uses: lem-per-quasi-excellent-localization, lem-per-local-g-ring-adic-lifting,
lem-per-semilocal-g-ring-j2, lem-weil-pbc-g-ring-completion-regular,
lem-weil-pbc-local-completion-faithfully-flat, lem-sfb-faithfully-flat-normal-ring-descent.

4. We record why only generic formal fibres can fail. For primes $0\ne\mathfrak
t\subseteq\mathfrak p$ of $R$, $R/\mathfrak t$ is quasi-excellent by hypothesis; its
localization at $\mathfrak p/\mathfrak t$ is quasi-excellent by
[lem-per-quasi-excellent-localization]. Its completion map is regular by
[lem-weil-pbc-g-ring-completion-regular]. The generic fibre of that map is geometrically
regular, and [lem-weil-pbc-formal-fibre-quotient-iso] identifies it with the fibre over
$\mathfrak t$ of $R_{\mathfrak p}\to\widehat{R_{\mathfrak p}}$. Thus all nonzero-prime fibres of
every such completion map are geometrically regular.
Uses: lem-per-quasi-excellent-localization, lem-weil-pbc-g-ring-completion-regular,
lem-weil-pbc-formal-fibre-quotient-iso.

5. The quotient $R/xR$ is quasi-excellent since $xR\ne0$, and $xR$ is in the Jacobson radical by
[lem-weil-pbc-adic-complete-jacobson-radical]. If $R$ were a G-ring,
[lem-per-g-ring-quasi-excellent-closed-fibre] would make it quasi-excellent, contrary to
hypothesis. By [lem-weil-pbc-g-ring-maximal-ideal-criterion], choose a maximal ideal $\mathfrak
n$ whose local completion map is not regular. It is flat by
[lem-weil-pbc-local-completion-faithfully-flat], so step 4 shows its generic fibre is not
geometrically regular. Put $K=\operatorname{Frac}R$. Since $K$ has characteristic zero, a finite
purely inseparable extension has degree one (an element with a $p$-power in the base can occur
nontrivially only in characteristic $p>0$). Thus geometric regularity over $K$ is ordinary
regularity by [def-weil-pbc-g-ring]. Consequently $K\otimes_R\widehat{R_{\mathfrak n}}$ is not
regular.
Uses: lem-weil-pbc-adic-complete-jacobson-radical, lem-per-g-ring-quasi-excellent-closed-fibre,
lem-weil-pbc-g-ring-maximal-ideal-criterion, lem-weil-pbc-local-completion-faithfully-flat,
def-weil-pbc-g-ring.

6. Use $L=K$, so normality of $R$ gives $B_K=R$, and put $C=C_{K,\mathfrak n}$. If $K\otimes_R
C$ were regular, every local ring of $\widehat{R_{\mathfrak n}}$ at a prime over $(0)$ would be
regular: the corresponding local ring of $C$ is regular, the local map is flat with regular
closed fibre because $C\to\widehat C$ is regular (step 3), and
[lem-weil-pbc-flat-over-regular-with-regular-fibre] applies. This contradicts step 5. Choose a
singular prime of $C$ contracting to zero. Since $\operatorname{Sing}C$ is closed, write it as
$V(J)$; [lem-weil-pbc-prime-contains-minimal-prime] supplies a prime minimal over $J$ below the
chosen prime. Its contraction to $R$ is still zero, so it gives a member of $\mathcal S$.
Uses: lem-weil-pbc-flat-over-regular-with-regular-fibre,
lem-weil-pbc-prime-contains-minimal-prime.

7. Every prime in each Noetherian $C$ has finite natural height by
[lem-trf-noetherian-prime-finite-height]. The nonempty set of these natural heights therefore
has a least element $h$, realized by a triple. Each $C$ is normal by step 3, hence satisfies
$(R_1)$ by [lem-weil-pbc-serre-criterion-normal]. By the definition of $(R_1)$ in
[def-weil-pbc-serre-conditions-rk-sk], a singular prime cannot have height zero or one. Hence
$h\geq2$.
Uses: lem-trf-noetherian-prime-finite-height, lem-weil-pbc-serre-criterion-normal,
def-weil-pbc-serre-conditions-rk-sk.

8. Let $0\ne\mathfrak p\subset R$ have height at most $h$, choose a maximal $\mathfrak
n\supseteq\mathfrak p$, and put $C=C_{K,\mathfrak n}$, $A=R_{\mathfrak p}$. The map
$R_{\mathfrak n}\to C$ is flat by [lem-weil-pbc-noetherian-completion-flat] and local by step 2,
hence faithfully flat by [lem-pc-local-flat-faithful-flat-reflects-surjective]. Thus $\mathfrak
pC$ is proper: by [lem-weil-pbc-faithfully-flat-surjective-spectrum] some prime of $C$ contracts
to $\mathfrak pR_{\mathfrak n}$, and it contains $\mathfrak pC$. Choose $Q$ minimal over
$\mathfrak pC$ using [lem-weil-pbc-minimal-prime-over-proper-ideal]. Its contraction to $R$ is
exactly $\mathfrak p$: otherwise [lem-sc-flat-going-down] would produce a strictly smaller prime
over $\mathfrak p$ containing $\mathfrak pC$. The induced map $\alpha:A\to C_Q$ is flat and
local, and its closed fibre has dimension zero because $Q$ is minimal over $\mathfrak pC$. Thus
[lem-weil-pbc-flat-height-formula] gives $\operatorname{ht}Q=\operatorname{ht}\mathfrak p\leq
h$. No finite-type assumption on this completion map is used.
Uses: lem-weil-pbc-noetherian-completion-flat,
lem-pc-local-flat-faithful-flat-reflects-surjective,
lem-weil-pbc-minimal-prime-over-proper-ideal, lem-sc-flat-going-down,
lem-weil-pbc-flat-height-formula, lem-weil-pbc-faithfully-flat-surjective-spectrum.

9. Put $T=\widehat{C_Q}$. By [lem-weil-pbc-localization-noetherian] and
[lem-weil-pbc-adic-completion-noetherian], these local rings are Noetherian. The map
$\widehat\alpha:\widehat A\to T$ is flat by [lem-weil-pbc-flat-completion], and it is local
since the compatible completion map carries the extended maximal ideal of $A$ into that of
$C_Q$; the description of these maximal ideals is [lem-weil-pbc-local-completion-local-ring]. It
is faithfully flat by [lem-pc-local-flat-faithful-flat-reflects-surjective]. Since $C$ is a
G-ring, the map $C_Q\to T$ is regular by [def-weil-pbc-g-ring].
Uses: lem-weil-pbc-localization-noetherian, lem-weil-pbc-adic-completion-noetherian,
lem-weil-pbc-flat-completion, lem-weil-pbc-local-completion-local-ring,
lem-pc-local-flat-faithful-flat-reflects-surjective, def-weil-pbc-g-ring.

10. Write $\operatorname{Sing}C=V(J)$, and let $s_1,\ldots,s_r$ be the primes minimal over $J$
which are contained in $Q$; there are finitely many by
[lem-sc-finite-minimal-primes-over-ideal]. For each $s_i\subsetneq Q$, strict inclusion and
finite heights give $\operatorname{ht}s_i<\operatorname{ht}Q\leq h$. Its contraction to $R$ must
be nonzero: otherwise $(K,\mathfrak n,s_i)\in\mathcal S$ contradicts minimality of $h$. If
$s_i=Q$, its contraction is the nonzero ideal $\mathfrak p$. Choose $0\ne b_i\in s_i\cap R$ and
put $b=\prod_i b_i$, with $b=1$ if $r=0$. This is nonzero since $R$ is a domain. This product is
the explicit common element in all the surviving singular components.
Uses: lem-sc-finite-minimal-primes-over-ideal.

11. We claim $T[1/b]$ is regular. For a prime $P\subset T$ not containing $b$, contract it to a
prime $s\subseteq Q$ of $C$. If $C_s$ were singular, [lem-weil-pbc-prime-contains-minimal-prime]
would give a minimal singular prime $s_i\subseteq s$; it appears in step 10, forcing $b\in P$, a
contradiction. Thus $C_s$ is regular. The map $C_s\to T_P$ is flat local with regular closed
fibre: it is obtained by localization from the regular map $C_Q\to T$ of step 9. Apply
[lem-weil-pbc-flat-over-regular-with-regular-fibre] to obtain that $T_P$ is regular. Since
localization preserves Noetherianity by [lem-weil-pbc-localization-noetherian], this proves the
claim. This pointwise argument supplies explicitly the source's assertion that the singular
ideal extends to a defining ideal of $\operatorname{Sing}T$.
Uses: lem-weil-pbc-prime-contains-minimal-prime,
lem-weil-pbc-flat-over-regular-with-regular-fibre, lem-weil-pbc-localization-noetherian.

12. Faithful flatness of $\widehat\alpha$ gives, by
[lem-weil-pbc-faithfully-flat-surjective-spectrum], for every prime $P$ of $\widehat A$ avoiding
$b$ a prime of $T$ over it, also avoiding $b$. The local map of the corresponding prime
localizations is flat, and its target is regular by step 11. By
[lem-weil-pbc-flat-under-regular], $\widehat A_P$ is regular. Localizing once more preserves
regular local rings by [lem-weil-pbc-regular-local-localization]. Every prime of
$K\otimes_R\widehat A$ avoids the nonzero $b$, so this generic fibre is regular. As in step 5,
characteristic zero makes it geometrically regular. Together with step 4 and flatness of the
completion map [lem-weil-pbc-local-completion-faithfully-flat], every fibre of $A\to\widehat A$
is geometrically regular; this map is regular.
Uses: lem-weil-pbc-flat-under-regular, lem-weil-pbc-regular-local-localization,
lem-weil-pbc-local-completion-faithfully-flat, lem-weil-pbc-faithfully-flat-surjective-spectrum.

13. By [lem-weil-pbc-g-ring-maximal-ideal-criterion], the local ring $A=R_{\mathfrak p}$ is a
G-ring, since its only maximal-local completion map is the regular map of step 12. Then
[lem-per-semilocal-g-ring-j2] makes $A$ quasi-excellent. It is universally catenary by the
definition in [def-exc-excellent-ring]: a finite type $R_{\mathfrak p}$-algebra is the
localization, at $R\setminus\mathfrak p$, of a finite type $R$-algebra (choose finitely many
algebra generators and clear denominators in finitely many defining equations, possible since
$R$ is Noetherian). Between two primes surviving a localization every intermediate prime also
survives, so the saturated chains and their lengths agree. Universal catenarity of $R$ therefore
supplies it for $A$. Thus $A$ is excellent. At $\mathfrak p=0$, the local ring is the field $K$,
excellent by [lem-exc-fields-excellent].
Uses: lem-weil-pbc-g-ring-maximal-ideal-criterion, lem-per-semilocal-g-ring-j2,
def-exc-excellent-ring, lem-exc-fields-excellent.

14. Finally fix $L$ and $\mathfrak q\subset B_L$ of height at most $h$, and put $\mathfrak
p=\mathfrak q\cap R$. Apply [lem-exc-dimension-formula-universally-catenary-finite-type-domain]
to the finite extension of domains $R\subset B_L$: its fraction field extension and its residue
field extension at $\mathfrak q$ are algebraic, so both transcendence degrees are zero and
$\operatorname{ht}\mathfrak p=\operatorname{ht}\mathfrak q\leq h$. Hence $R_{\mathfrak p}$ is
excellent by step 13. The algebra $B_L\otimes_R R_{\mathfrak p}$ is finite, hence finite type
over this ring, and $(B_L)_{\mathfrak q}$ is its localization. Apply
[lem-exc-finite-type-localization-excellent] to obtain excellence of $(B_L)_{\mathfrak q}$. This
includes height zero, where the localizations are fields.
Uses: lem-exc-dimension-formula-universally-catenary-finite-type-domain,
lem-exc-finite-type-localization-excellent.
-/
theorem exists_qe_minimal_formal_defect
    (R : Type u) [CommRing R] [IsDomain R] [Algebra ℚ R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (hNagata : IsNagataRing R) (x : R)
    (hx : x ≠ 0) (hxunit : ¬ IsUnit x)
    (hcomplete : IsAdicComplete (Ideal.span {x}) R)
    (hcatenary : IsUniversallyCatenary R) (hnotqe : ¬ IsQuasiExcellent R)
    (hquot : ∀ K : Ideal R, K ≠ ⊥ → IsQuasiExcellent (R ⧸ K))
    (hB : ∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
      [IsScalarTower R (FractionRing R) L] [Module.Finite (FractionRing R) L],
      Module.Finite R (integralClosure R L) ∧
      (∀ (p : Ideal (integralClosure R L)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
      IsNagataRing (integralClosure R L) ∧
      IsUniversallyCatenary (integralClosure R L) ∧
      IsAdicComplete (Ideal.span {algebraMap R (integralClosure R L) x})
        (integralClosure R L) ∧
      IsQuasiExcellent ((integralClosure R L) ⧸
        Ideal.span {algebraMap R (integralClosure R L) x}) ∧
      ∀ (n : Ideal (integralClosure R L)) [n.IsMaximal],
        IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime n))
          (Localization.AtPrime n)) ∧
        IsDomain (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime n))
          (Localization.AtPrime n)) ∧
        IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime n))
          (Localization.AtPrime n))) :
    (∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
      [IsScalarTower R (FractionRing R) L] [Module.Finite (FractionRing R) L]
      (n : Ideal (integralClosure R L)) [n.IsMaximal],
      IsNoetherianRing (qeFormalCompletion (integralClosure R L)
        (algebraMap R (integralClosure R L) x) n) ∧
      IsLocalRing (qeFormalCompletion (integralClosure R L)
        (algebraMap R (integralClosure R L) x) n) ∧
      (∀ (p : Ideal (qeFormalCompletion (integralClosure R L)
          (algebraMap R (integralClosure R L) x) n)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
      IsGRing (qeFormalCompletion (integralClosure R L)
        (algebraMap R (integralClosure R L) x) n) ∧
      IsClosed {s : PrimeSpectrum (qeFormalCompletion (integralClosure R L)
          (algebraMap R (integralClosure R L) x) n) |
        ¬ IsRegularLocalRing (Localization.AtPrime s.asIdeal)}) ∧
    ∃ h : ℕ, 2 ≤ h ∧
      (∃ (L : Type u) (_ : Field L) (_ : Algebra R L) (_ : Algebra (FractionRing R) L)
        (_ : IsScalarTower R (FractionRing R) L) (_ : Module.Finite (FractionRing R) L)
        (n : Ideal (integralClosure R L)) (_ : n.IsMaximal)
        (s : PrimeSpectrum (qeFormalCompletion (integralClosure R L)
          (algebraMap R (integralClosure R L) x) n)),
        s ∈ qeGenericMinimalSingularPrimes (integralClosure R L)
          (algebraMap R (integralClosure R L) x) n ∧
        ringKrullDim (Localization.AtPrime s.asIdeal) = (h : WithBot ℕ∞)) ∧
      (∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
        [IsScalarTower R (FractionRing R) L] [Module.Finite (FractionRing R) L]
        (n : Ideal (integralClosure R L)) [n.IsMaximal]
        (s : PrimeSpectrum (qeFormalCompletion (integralClosure R L)
          (algebraMap R (integralClosure R L) x) n)),
        s ∈ qeGenericMinimalSingularPrimes (integralClosure R L)
          (algebraMap R (integralClosure R L) x) n →
        (h : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime s.asIdeal)) ∧
      (∀ p : PrimeSpectrum R,
        ringKrullDim (Localization.AtPrime p.asIdeal) ≤ (h : WithBot ℕ∞) →
        IsExcellent (Localization.AtPrime p.asIdeal)) ∧
      (∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
        [IsScalarTower R (FractionRing R) L] [Module.Finite (FractionRing R) L]
        (q : PrimeSpectrum (integralClosure R L)),
        ringKrullDim (Localization.AtPrime q.asIdeal) ≤ (h : WithBot ℕ∞) →
        IsExcellent (Localization.AtPrime q.asIdeal)) := by
  sorry
