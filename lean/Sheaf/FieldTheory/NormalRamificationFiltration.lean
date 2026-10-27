/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q99
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import WeilConjectures.RingTheory.NagataOfCompleteLocal
import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.JapaneseDomain
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import WeilConjectures.FieldTheory.NormalExtensionFixedField
import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower
import Sheaf.FieldTheory.FiniteDVRTameInertia
import Sheaf.AlgebraicGeometry.FiniteGroupInertiaInvariantsEtale
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTraitStalk
import Sheaf.NumberTheory.DvrGaloisDegreeData
import Sheaf.FieldTheory.FiniteDVRResidueNormalAction

/-!
# Normal ramification filtration

Source: Stacks Project, More on Algebra, Tag 09F8 (`lemma-special-case`),
normal closure and branchwise base change paragraphs
(blueprint: lem-sfb-epp-normal-ramification-filtration).

## Main declarations

* `IsDiscreteValuationRing.normal_ramification_filtration`: existence of a normal tower.
* `IsDiscreteValuationRing.normal_ramification_filtration_baseChange`: branchwise stability.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y z t

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- The four step conditions in the filtration of Tag 09F8, using the induced map of
integral closures and its induced residue-field map. The existential local structures
only allow the residue fields to be typed; they do not choose new rings or maps.
Source: Stacks Project, More on Algebra, Tag 09F8
(blueprint: lem-sfb-epp-normal-ramification-filtration). -/
def IsNormalRamificationStep (B : Type u) (E : Type v) (F : Type w) (p : ℕ)
    [CommRing B] [Field E] [Field F] [Algebra B E] [Algebra B F]
    (f : E →ₐ[B] F) : Prop :=
  ∃ dE : IsDiscreteValuationRing (integralClosure B E),
    ∃ dF : IsDiscreteValuationRing (integralClosure B F),
      letI := dE
      letI := dF
      letI := f.toRingHom.toAlgebra
      ∃ hf : IsLocalHom f.mapIntegralClosure.toRingHom,
        letI := hf
        letI := (IsLocalRing.ResidueField.map f.mapIntegralClosure.toRingHom).toAlgebra
        (CharP E p ∧ Module.finrank E F = p ∧
          ∀ x : F, ∃ a : E, f a = x ^ p) ∨
        (IsGalois E F ∧ Module.finrank E F = p) ∨
        (IsGalois E F ∧ IsCyclic (F ≃ₐ[E] F) ∧
          Nat.Coprime (Module.finrank E F) p ∧
          (∃ e : ℕ, Nat.Coprime e p ∧
            Ideal.map f.mapIntegralClosure.toRingHom
                (IsLocalRing.maximalIdeal (integralClosure B E)) =
              IsLocalRing.maximalIdeal (integralClosure B F) ^ e) ∧
          Algebra.IsSeparable (IsLocalRing.ResidueField (integralClosure B E))
            (IsLocalRing.ResidueField (integralClosure B F))) ∨
        (Ideal.map f.mapIntegralClosure.toRingHom
              (IsLocalRing.maximalIdeal (integralClosure B E)) =
            IsLocalRing.maximalIdeal (integralClosure B F) ∧
          Module.Finite (IsLocalRing.ResidueField (integralClosure B E))
            (IsLocalRing.ResidueField (integralClosure B F)) ∧
          Algebra.IsSeparable (IsLocalRing.ResidueField (integralClosure B E))
            (IsLocalRing.ResidueField (integralClosure B F)))

/-- A chain with the four permitted nonidentity steps.
Source: Stacks Project, More on Algebra, Tag 09F8, the displayed tower and its normalization
(blueprint: lem-sfb-epp-normal-ramification-filtration). -/
def IsNormalRamificationChain (B : Type u) (K : Type v) (N : Type w) (p n : ℕ)
    [CommRing B] [Field K] [Field N] [Algebra B K] [Algebra K N] [Algebra B N]
    [IsScalarTower B K N] (F : Fin (n + 1) → IntermediateField K N) : Prop :=
  ∃ h : Monotone F, ∀ i : Fin n, F i.castSucc ≠ F i.succ →
    IsNormalRamificationStep B (F i.castSucc) (F i.succ) p
      ((IntermediateField.inclusion (h (Fin.castSucc_le_succ i))).restrictScalars B)

/-- Completeness and the DVR property for every normalization along the filtration.
Source: Stacks Project, More on Algebra, Tag 09F8, first proof paragraph
(blueprint: lem-sfb-epp-normal-ramification-filtration). -/
def HasCompleteRamificationClosures (B : Type u) (K : Type v) (N : Type w) (n : ℕ)
    [CommRing B] [Field K] [Field N] [Algebra B K] [Algebra K N] [Algebra B N]
    [IsScalarTower B K N] (F : Fin (n + 1) → IntermediateField K N) : Prop :=
  ∀ i, ∃ d : IsDiscreteValuationRing (integralClosure B (F i)),
    letI := d
    IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure B (F i)))
      (integralClosure B (F i))

/-- The composita with the chosen finite base extension inside a field factor. A surjective
map from the tensor product to a field selects precisely a field factor of its reduction:
nilpotents map to zero, and the reduced finite-dimensional algebra is a product of fields.
Source: Stacks Project, More on Algebra, Tags 09EM and 09F8
(blueprint: lem-sfb-epp-normal-ramification-filtration). -/
def normalRamificationBaseChangeFields
    (K : Type u) (E : Type v) (T : Type w) (K' : Type x) (W : Type y)
    [Field K] [Field E] [Field T] [Field K'] [Field W]
    [Algebra K E] [Algebra E T] [Algebra K T] [IsScalarTower K E T]
    [Algebra K K'] [Algebra T W] [Algebra E W] [Algebra K W]
    [IsScalarTower E T W] [IsScalarTower K T W]
    (q : T ⊗[K] K' →ₐ[T] W) (n : ℕ)
    (F : Fin (n + 1) → IntermediateField E T) :
    Fin (n + 1) → IntermediateField E W :=
  fun i ↦ (F i).map (IsScalarTower.toAlgHom E T W) ⊔
    IntermediateField.adjoin E
      (Set.range ((q.restrictScalars K).comp Algebra.TensorProduct.includeRight))

/-- Every finite extension of the fraction field of a complete DVR embeds into a finite
normal extension with the four-step filtration of Tag 09F8.

Source: Stacks Project, More on Algebra, Tag 09F8 (`lemma-special-case`).
Proof: finite normalizations of the complete DVR are finite by Nagata, local and complete
by the finite-algebra decomposition, and DVRs by the local normalization theorem. Pass to
a finite normal closure and first refine its purely inseparable part into degree-p steps.
For its Galois part, the decomposition group is the full automorphism group. The fixed
field of inertia is unramified (09EH, or 0BST plus the etale trait criterion). Wild inertia
is a normal p-group and the tame quotient is cyclic of order prime to p (09EE). Its fixed
field gives the cyclic tame step: the degree formula ef = n and normality of the residue
extension rule out an inseparable residue part. Refine the wild p-group by normal subgroups
of index p. The Galois correspondence and automorphism-order/degree equality give the
Galois degree-p steps. Concatenate the chains and remove identities.

Proof plan from the DAG:

1. For each complete DVR $D$ encountered below and finite extension $T/\operatorname{Frac}(D)$,
let $S=\operatorname{IntCl}_T(D)$. The DVR definition makes $D$ a nonfield local PID. Thus $D$ is
Noetherian and normal by [lem-weil-pbc-pid-noetherian-normal] and has dimension one by
[lem-sc-dvr-dimension-one]. By [lem-weil-pbc-complete-local-nagata], $D$ is Nagata. Its zero ideal
is prime, so the definitions [def-weil-pbc-nagata-ring, def-weil-pbc-japanese-domain] give that
$S$ is a finite $D$-module, without a separability assumption. It is a domain, being a subring of
$T$. Consequently [lem-weil-pbc-finite-over-complete-local-product] makes $S$ local and complete.
By [lem-sfb-finite-normalization-local-dvr] there is a maximal ideal $q$ of $S$ over $\mathfrak
m_D$, and $S_q$ is a DVR with fraction field $T$ and maximal ideal contracting to $\mathfrak m_D$.
Since $S$ is local, this $q$ is its unique maximal ideal and every denominator outside $q$ is a
unit, so $S=S_q$. Therefore $S$ is a finite complete DVR, and $D\to S$ is local. This argument
applies separately to every finite field extension used below. Uses:
def-sc-discrete-valuation-ring, lem-weil-pbc-pid-noetherian-normal, lem-sc-dvr-dimension-one,
lem-weil-pbc-complete-local-nagata, def-weil-pbc-nagata-ring, def-weil-pbc-japanese-domain,
lem-weil-pbc-finite-over-complete-local-product, lem-sfb-finite-normalization-local-dvr.

2. Choose a finite normal extension $N/L$ containing $M$ by
[lem-weil-pbc-finite-extension-in-finite-normal-extension]. By
[lem-weil-pbc-normal-extension-purely-inseparable-then-galois] there is $L\subseteq F\subseteq N$
with $F/L$ purely inseparable and $N/F$ Galois. Both subextensions are finite, since an
intermediate field is a vector subspace of $N$ over $L$. In characteristic zero $F=L$ by the
definition of pure inseparability. In positive characteristic, the embedding $B\subseteq L$ shows
$\operatorname{char}(L)=p$: a field of positive characteristic has that same characteristic in any
nonzero residue field of a subring. Apply [lem-weil-pbc-purely-inseparable-pth-root-tower] to
$F/L$ to obtain its degree-$p$ steps. For a step $H(\alpha)/H$ with $\alpha^p\in H$, every
rational expression in $\alpha$ has its $p$th power in $H$, so it is type (a). Step 1, with $D=B$,
makes the closures in all these intermediate fields finite complete DVRs with local inclusions.
Uses: lem-weil-pbc-finite-extension-in-finite-normal-extension,
lem-weil-pbc-normal-extension-purely-inseparable-then-galois,
def-weil-pbc-finite-purely-inseparable-extension, lem-weil-pbc-purely-inseparable-pth-root-tower.

3. Put $R=\operatorname{IntCl}_F(B)$ and $C=\operatorname{IntCl}_N(B)$. Transitivity of integral
elements [lem-sfb-integral-element-tower-descent] shows that $C$ is also the closure of $R$ in
$N$: integrality over $B$ implies integrality over $R$, and the reverse implication uses $R/B$
integral. These rings are complete DVRs by step 1. Let $G=\operatorname{Aut}_F(N)$. Every element
of $G$ preserves $C$, because it preserves monic equations over $R$, and hence preserves its
unique maximal ideal. Thus the decomposition group is all of $G$. Apply
[lem-exc-finite-dvr-tame-inertia] to $R,N/F,C$ and its maximal ideal: the inertia group $I$ has a
normal subgroup $P$, of $p$-power order, and $I/P$ is cyclic of order prime to $p$. Put $U=N^I$,
$V=N^P$. Their integral closures are complete DVRs by step 1. Uses:
lem-sfb-integral-element-tower-descent, lem-exc-finite-dvr-tame-inertia.

4. The fixed ring $C^G$ is $R$: [lem-weil-pbc-finite-galois-fixed-field] identifies the fixed
fraction field with $F$, and the elements of $C\cap F$ and of $R$ are, by their definitions,
exactly the elements of $F$ integral over $B$. Likewise $C^I=C\cap U$ is the integral closure of
$B$ in $U$, by the defining monic-equation condition. Apply
[lem-dl-a1-finite-group-inertia-invariants-etale] to $G$ acting on $C$ at its maximal ideal. It
makes $\operatorname{Spec}(C^I)\to\operatorname{Spec}R$ etale on a neighbourhood of the closed
point. Since $C^I$ is local, any open containing its closed point is the entire spectrum. Apply
[lem-sbc-etale-trait-stalk] at that point: a uniformizer of $R$ generates the maximal ideal of
$C^I$, and hence the index is one. Apply [lem-weil-pbc-etale-algebra-residue-field-separable] to
this etale map: its residue extension is finite separable. Therefore $U/F$ is type (d), unless it
is the identity. Uses: lem-weil-pbc-finite-galois-fixed-field,
lem-dl-a1-finite-group-inertia-invariants-etale, lem-sbc-etale-trait-stalk,
lem-weil-pbc-etale-algebra-residue-field-separable.

5. By [lem-wf-finite-field-action-fixed-degree], $N/U$ is Galois of degree $|I|$ and $N/V$ is
Galois of degree $|P|$. By [lem-weil-pbc-finite-galois-fixed-field], the full automorphism groups
of these finite Galois extensions have exactly these degrees as their orders. Since they contain
$I$ and $P$, respectively, they equal those subgroups. Apply
[lem-per-finite-galois-normal-fixed-quotient] to $N/U$ and $P\triangleleft I$. It identifies
$\operatorname{Aut}_U(V)$ with $I/P$, so $V/U$ is cyclic Galois. The same finite-Galois
cardinality theorem gives its degree $n=|I/P|$, prime to $p$. By [lem-exc-dvr-galois-degree-data],
its unique normalized DVR branch has $ef=n$. Thus both $e$ and $f$ are prime to $p$. Its residue
extension is normal by [lem-exc-dvr-residue-normal-action]. For that characteristic-$p$ residue
extension [lem-exc-normal-field-degree-factors] writes $f=s p^b$, where $p^b$ is the degree over
the subfield of separable elements. Coprimality forces $b=0$, so every residue element is
separable. This is type (c) if $V\ne U$. Uses: lem-wf-finite-field-action-fixed-degree,
lem-per-finite-galois-normal-fixed-quotient, lem-exc-dvr-galois-degree-data,
lem-exc-dvr-residue-normal-action, lem-exc-normal-field-degree-factors,
lem-weil-pbc-finite-galois-fixed-field.

6. If $P=1$, then $V=N$. Otherwise apply [lem-sfb-finite-p-group-normal-index-p] repeatedly, first
to $P$ and then to each subgroup obtained, obtaining $P=P_0\supset P_1\supset\cdots\supset P_a=1$,
with $P_{i+1}$ normal in $P_i$ of index $p$. The order falls by a factor $p$ at each step, so the
iteration terminates. Set $H_i=N^{P_i}$. By [lem-wf-finite-field-action-fixed-degree], $N/H_i$ is
Galois of degree $|P_i|$. By [lem-weil-pbc-finite-galois-fixed-field], its full automorphism group
has that same order, and hence equals its subgroup $P_i$; applying
[lem-per-finite-galois-normal-fixed-quotient] to $P_{i+1}\triangleleft P_i$ gives $H_{i+1}/H_i$
Galois with group $P_i/P_{i+1}$, hence degree $p$ by [lem-weil-pbc-finite-galois-fixed-field]
again. These are type (b); no assertion that their residue extension is trivial is used.
Concatenate $L\subseteq F$, $F\subseteq U$, $U\subseteq V=H_0$, and this last tower. Delete
identities to get the first assertion. Uses: lem-sfb-finite-p-group-normal-index-p,
lem-wf-finite-field-action-fixed-degree, lem-per-finite-galois-normal-fixed-quotient,
lem-weil-pbc-finite-galois-fixed-field.
(blueprint: lem-sfb-epp-normal-ramification-filtration). -/
theorem normal_ramification_filtration
    (B : Type u) (L : Type v) (M : Type w) (p : ℕ)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Field L] [Field M] [Algebra B L] [IsFractionRing B L]
    [Algebra L M] [Module.Finite L M]
    [Fact p.Prime] [CharP (IsLocalRing.ResidueField B) p] :
    ∃ (N : Type (max v w)) (_ : Field N) (_ : Algebra L N) (_ : Algebra B N)
      (_ : IsScalarTower B L N) (_ : Module.Finite L N) (_ : Normal L N),
      Nonempty (M →ₐ[L] N) ∧
      ∃ (n : ℕ) (F : Fin (n + 1) → IntermediateField L N),
        F 0 = ⊥ ∧ F (Fin.last n) = ⊤ ∧ IsNormalRamificationChain B L N p n F ∧
          HasCompleteRamificationClosures B L N n F := by
  sorry

/-- The four types persist in every normalized branch after finite base change, and deleting
identity steps gives a chain no longer than the original one.

Source: Stacks Project, More on Algebra, Tag 09F8, branchwise induction paragraph.
Proof: in the chosen field factor put F_j = E_j K'. The image of each tensor algebra is a
finite-dimensional domain over E_j, hence a field, so F_j/E_j is finite. The normalizations
are complete DVRs as in the first assertion, and transitivity of integral elements
identifies successive normalizations. For (a), exponent one and degree at most p persist;
the degree is a p-power, hence 1 or p. For (b), Galois compositum restriction embeds the
new group in a group of order p; its order and the new degree are 1 or p. For (c), the same
restriction gives a subgroup of the cyclic prime-to-p group, and tame compositum permanence
(0EXY) gives the ramification and residue conditions. For (d), the reduced tensor product
splits into fields (09EM). Its normalization splits into their integral closures, and
localizing at the maximal ideal for the chosen factor recovers its complete DVR. Apply
09EQ to this branch: the index-one and separable-residue conditions persist, without any
fraction-field separability assumption. Residue finiteness follows from finite
normalization. The composita are nested and exhaust the chosen top factor. Deleting equal
adjacent fields leaves at most the original number of steps.

Proof plan from the DAG:

7. Now take the arbitrary tower and finite base change in the second assertion. Work inside the
chosen top field factor $W=E^s_1$. All maps from the fields $E^j$ and $K\prime$ into $W$ are
injective. Set $F_j=E^jK\prime\subseteq W$ and $C_j=\operatorname{IntCl}_{E^j}(B\prime)$,
$D_j=\operatorname{IntCl}_{F_j}(B\prime)$. The image of $E^j\otimes_K K\prime$ in $W$ is a
finite-dimensional $E^j$-algebra and a domain. A nonzero element acts injectively on this
finite-dimensional vector space and therefore surjectively, so has an inverse in the image. Thus
the image is already the field $F_j$; in particular $F_j/E^j$ is finite. Since $E^j/E^0$ and
$F_j/E^j$ are finite, so is $F_j/E^0$ (products of finite spanning sets span). Step 1 with
$D=B\prime$ makes all $C_j,D_j$ finite complete DVRs. By [lem-sfb-integral-element-tower-descent],
$D_j$ is also the integral closure of $C_j$ in $F_j$, and $D_{j+1}$ is the closure of $D_j$ in
$F_{j+1}$. The inclusions are therefore local by step 1 applied with those complete base DVRs and
finite fraction-field extensions. Their residue characteristic is $p$, by the corrected
hypothesis. Uses: lem-sfb-integral-element-tower-descent.

8. For a type (a) step $E^{j+1}/E^j$, every $p$th power of a rational expression in elements of
$E^{j+1}$ and $F_j$ lies in $F_j$, so $F_{j+1}/F_j$ is purely inseparable of exponent at most one.
Also its degree is at most $p$: the $p$ elements of an $E^j$-basis of $E^{j+1}$ span the image
algebra over $F_j$, which is a field by the finite-dimensional-domain argument in the preceding
step, and is exactly $F_{j+1}$. Apply [lem-weil-pbc-purely-inseparable-pth-root-tower] to this
finite purely inseparable extension, and multiply the degrees of its steps using
[lem-weil-pbc-field-degree-multiplicativity]. Its degree is a power of $p$ between $1$ and $p$,
hence either $1$ or $p$. In the latter case it is type (a); in the former case it is deleted.
Uses: lem-weil-pbc-purely-inseparable-pth-root-tower, lem-weil-pbc-field-degree-multiplicativity.

9. For a type (b) step apply [lem-sfb-galois-compositum-restriction] with $k=E^j$, $K=E^{j+1}$,
$F=F_j$ and ambient field $F_{j+1}$. The new step is Galois and its group injects into the group
of order $p$. By [lem-exc-finite-group-cauchy] the old group has an element of order $p$, whose
$p$ distinct powers exhaust its $p$ elements. Every nonidentity power is again a generator, since
its exponent is invertible modulo $p$. Thus its subgroups are trivial or the entire group. By
[lem-weil-pbc-finite-galois-fixed-field] the new degree is the order of its group, hence $1$ or
$p$, so the surviving step is type (b). For a type (c) step the same restriction theorem gives a
cyclic Galois group of order dividing the original prime-to-$p$ cyclic order (if the original
generator has order $n$, the least positive exponent $d$ whose power belongs to the subgroup
divides $n$ by Euclidean division; dividing any other such exponent by $d$ shows the subgroup
consists of these powers and has order $n/d$). Thus its degree is prime to $p$. Uses:
lem-sfb-galois-compositum-restriction, lem-weil-pbc-finite-galois-fixed-field,
lem-exc-finite-group-cauchy.

10. For a type (c) step apply [lem-sfb-dvr-tame-unramified-compositum-permanence] to the local DVR
inclusion $C_j\hookrightarrow D_j$ and the finite separable extension $E^{j+1}/E^j$. The original
normalized extension is tame by the definition in the item. The compositum $F_{j+1}$ is a field
factor of $E^{j+1}\otimes_{E^j}F_j$: the multiplication map is onto, by the
finite-dimensional-domain argument of step 7. The theorem gives prime-to-$p$ ramification index
and finite separable residue extension for its normalization over $D_j$, which is $D_{j+1}$ by
step 7. With the cyclic Galois conclusion of step 9 this is type (c), unless the step is an
identity. Uses: lem-sfb-dvr-tame-unramified-compositum-permanence.

11. For a type (d) step put $Q=(E^{j+1}\otimes_{E^j}F_j)_{\mathrm{red}}$. Apply
[lem-sfb-dvr-algebraic-normalization-structure] with $A=C_j$, $B=C_{j+1}$, $P=F_j$: the map is
injective local by step 7, and $F_j/E^j$ is finite. It gives $Q=\prod_\alpha Q_\alpha$ with field
factors. Multiplication is onto $F_{j+1}$ by step 7 and kills nilpotents. A surjection from a
finite product of fields to a field sends exactly one of the orthogonal coordinate idempotents to
$1$ and the others to $0$; its restriction on that factor is an isomorphism. Thus one $Q_\alpha$
is the chosen compositum $F_{j+1}$. Write $S_\alpha=\operatorname{IntCl}_{Q_\alpha}(C_{j+1})$.
Then $H=\operatorname{IntCl}_Q(C_{j+1})=\prod_\alpha S_\alpha$: projection of a monic equation
proves one inclusion, and the product of monic annihilators for all coordinates annihilates their
tuple, proving the other. Each $Q_\alpha/E^{j+1}$ is finite, as a quotient of the
finite-dimensional tensor algebra; step 1 makes $S_\alpha$ a complete DVR. For the selected
factor, $S_\alpha=D_{j+1}$ by the closure identification in step 7. Let $q$ be the inverse image
of $\mathfrak m_{D_{j+1}}$ under $H\twoheadrightarrow D_{j+1}$. This is maximal. In $H_q$ the
selected idempotent is a unit and kills the other factors; the surviving denominators are units of
$D_{j+1}$. Consequently $H_q=D_{j+1}$. Uses: lem-sfb-dvr-algebraic-normalization-structure.

12. For this type (d) step apply [lem-sfb-dvr-index-one-separable-base-change] with $A=C_j$,
$B=C_{j+1}$, $K=E^j$, $L=E^{j+1}$, $N=F_j$. Its hypotheses on $A\to B$ are exactly the old step:
index one and separable residue extension; its finite-field hypothesis is $F_j/E^j$, proved in
step 7. No separability of $E^{j+1}/E^j$ is required. In the notation of that lemma, $R=D_j$ by
step 7, and $C=H$, $C_q=D_{j+1}$ by step 11. The lemma says $n=q\cap D_j$ is maximal, hence
$n=\mathfrak m_{D_j}$ since $D_j$ is local, and $R_n=D_j$. Its equality $nC_q=qC_q$ is therefore
$\mathfrak m_{D_j}D_{j+1}=\mathfrak m_{D_{j+1}}$, and its residue conclusion gives separability.
This residue extension is finite as well: step 1 makes $D_{j+1}$ finite over $D_j$, and images of
module generators span the residue field over $D_j/\mathfrak m_{D_j}$. Thus the surviving step is
type (d), including when the old fraction-field extension is inseparable. Uses:
lem-sfb-dvr-index-one-separable-base-change.

13. The subfields $F_0\subseteq\cdots\subseteq F_s$ are nested because their two sets of
generators are nested, and their endpoint is $W$: the image of $E^s\otimes_K K\prime$ in its
chosen field factor generates all of $W$. Remove a repeated field whenever $F_j=F_{j+1}$. Removing
repetitions changes neither the maps nor the normalized rings for any remaining adjacent
nonidentity step; the surviving steps are exactly the nonidentity steps already treated. There are
at most $s$ of them. Step 7 has already proved completeness and the DVR property for every
normalization. Uses: .
(blueprint: lem-sfb-epp-normal-ramification-filtration). -/
theorem normal_ramification_filtration_baseChange
    (A : Type u) (B : Type v) (K : Type w) (E : Type x) (T : Type y)
    (K' : Type z) (W : Type t) (p n : ℕ)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Field K] [Field E] [Field T] [Field K'] [Field W]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hinj : Function.Injective (algebraMap A B))
    [Algebra A K] [IsFractionRing A K] [Algebra B E] [IsFractionRing B E]
    [Algebra K E] [Algebra A E] [IsScalarTower A B E] [IsScalarTower A K E]
    [Algebra E T] [Module.Finite E T] [Algebra K T] [IsScalarTower K E T]
    [Algebra B T] [IsScalarTower B E T]
    [Algebra K K'] [Module.Finite K K']
    [Algebra T W] [Algebra K W] [Algebra E W] [Algebra B W]
    [IsScalarTower E T W] [IsScalarTower K T W] [IsScalarTower B E W]
    [Fact p.Prime] [CharP (IsLocalRing.ResidueField B) p]
    (F : Fin (n + 1) → IntermediateField E T)
    (hbase : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    (hchain : IsNormalRamificationChain B E T p n F)
    (q : T ⊗[K] K' →ₐ[T] W) (hq : Function.Surjective q) :
    IsNormalRamificationChain B E W p n
        (normalRamificationBaseChangeFields K E T K' W q n F) ∧
      HasCompleteRamificationClosures B E W n
        (normalRamificationBaseChangeFields K E T K' W q n F) ∧
      ∃ (r : ℕ) (_ : r ≤ n) (H : Fin (r + 1) → IntermediateField E W),
        StrictMono H ∧
        Set.range H = Set.range (normalRamificationBaseChangeFields K E T K' W q n F) ∧
        IsNormalRamificationChain B E W p r H := by
  sorry

end IsDiscreteValuationRing
