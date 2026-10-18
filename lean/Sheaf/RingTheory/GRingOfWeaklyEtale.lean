/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.RingTheory.GRing
public import Sheaf.RingTheory.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.Flat.LocalizationPreservesFlatness
import Sheaf.RingTheory.FibreRingNoetherian
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.WeaklyEtaleField
import Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit
import Sheaf.RingTheory.FormallySmoothAdic
import Sheaf.RingTheory.FormallySmoothAdicOfFlatClosedFiber
import Sheaf.RingTheory.FormallySmoothAdicCompleteSourceTarget
import Sheaf.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.Algebra
import Sheaf.RingTheory.FormallySmoothCompleteLocalRegular
import Sheaf.RingTheory.RegularComposition
import Sheaf.RingTheory.LocalizationOfRegularRing
import Sheaf.RingTheory.GeometricRegularitySeparableExtension
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# G-rings ascend along weakly etale homomorphisms

Source: Silvio Greco, Two theorems on excellent rings, Nagoya Mathematical Journal 60
(1976), 139–149, Theorem 5.3(i), Section 1.1 and Remark 5.2, pp. 139–140 and 146–147;
Stacks Project, More on Algebra, Definition 07GH (blueprint: lem-exc-weakly-etale-g-ring).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom

/-- The target of a weakly etale homomorphism of Noetherian rings is a G-ring if its
source is a G-ring. Source: Greco, Two theorems on excellent rings, Theorem 5.3(i),
with P = geometrically regular in Section 1.1 and the equivalence in Remark 5.2;
Stacks Project, Definition 07GH (blueprint: lem-exc-weakly-etale-g-ring).

Proof:
1. Fix an arbitrary prime $\mathfrak q\subset B$, put $\mathfrak p=f^{-1}(\mathfrak q)$,
   $R=A_{\mathfrak p}$ and $S=B_{\mathfrak q}$, and let $g:R\to S$ be the induced map. Weak
   etaleness supplies flatness of $f$ by [def-weil-pbc-ind-etale-algebra]. By
   [lem-weil-pbc-flat-local-ring-maps], $R$ and $S$ are Noetherian local rings and $g$ is flat and
   local. Write $u:R\to\widehat R$ and $v:S\to\widehat S$ for their completion maps. The G-ring
   hypothesis on $A$, unfolded by [def-weil-pbc-g-ring], says exactly that $u$ is regular. It
   remains to show that $v$ is regular for every such $\mathfrak q$. If $B$ has no primes, this
   universal condition is vacuous.

2. The localized map $g$ is weakly etale, as follows directly from the flat multiplication
   criterion. Put $T=B\otimes_A B$ and $U=B\setminus\mathfrak q$. The $T$-module $B$, via
   multiplication, is flat; [lem-pc-affine-flat-module-localization-preserves-flatness] with this
   $B$-module and $U$ shows that $S=U^{-1}B$ is flat over $T$. The ring $S\otimes_R S$ is the
   localization of $T$ obtained by inverting $b\otimes1$ and $1\otimes b$ for $b\in U$: the forward
   map sends $(b/u)\otimes(c/w)$ to $(b\otimes c)/((u\otimes1)(1\otimes w))$, and the inverse sends
   $b\otimes c$ to $(b/1)\otimes(c/1)$ and inverts the displayed denominator factors. The balancing
   relations hold over $A$, and elements of $A\setminus\mathfrak p$ are already units in both
   factors. Its action on $S$ is multiplication. By [lem-weil-pbc-flat-over-localization], $S$ is
   flat over $S\otimes_R S$. Together with step 1 this is the two-flatness definition
   [def-weil-pbc-ind-etale-algebra].

3. For each prime $\mathfrak t\subset R$ put $k_{\mathfrak t}=\kappa(\mathfrak t)$ and $F_{\mathfrak
   t}=S\otimes_R k_{\mathfrak t}$. This fibre is Noetherian by [lem-weil-pbc-fibre-ring-noetherian]
   and weakly etale over the field $k_{\mathfrak t}$ by the base-change clause of
   [lem-weil-pbc-ind-etale-stability]. The ind-etale conclusion of [lem-weil-pbc-weak-etale-field]
   gives a filtered presentation by etale algebras over this field. Apply
   [lem-weil-pbc-henselization-finite-separable-fibres] to $k_{\mathfrak t}\to F_{\mathfrak t}$ at
   the zero prime of the base field. It gives a finite product $F_{\mathfrak t}\cong\prod_{i=1}^r
   L_i$ with every $L_i/k_{\mathfrak t}$ separable algebraic. The factors are the residue fields
   $\kappa(\mathfrak s_i)$ of the primes of $S$ contracting to $\mathfrak t$: prime ideals and
   residue fields on both sides agree by taking first the quotient by $\mathfrak t$ and then
   inverting the elements of $R\setminus\mathfrak t$. The empty product is allowed if the fibre is
   empty.

4. At $\mathfrak t=\mathfrak m_R$ the closed fibre $S/\mathfrak m_RS$ is nonzero and local, since
   $\mathfrak m_RS\subseteq\mathfrak m_S$ and it is a quotient of $S$. A nonzero finite product of
   fields is local only when there is one factor: for two nonzero coordinate idempotents $e$ and
   $1-e$, neither is a unit, contradicting locality. Thus this fibre is $L=\kappa(\mathfrak m_S)$
   and $L/k_{\mathfrak m_R}$ is separable algebraic by step 3. By
   [lem-exc-separable-algebraic-square-zero-lifting], every $k_{\mathfrak m_R}$-algebra map from $L$
   to a square-zero quotient lifts. The maximal ideal of $L$ is zero, so every such map kills its
   first power. This is exactly formal smoothness of the closed fibre for its maximal-ideal-adic
   topology by [def-weil-pbc-formally-smooth-adic].

5. Apply [lem-weil-pbc-flat-formally-smooth-closed-fibre-adic] to the flat local map $g:R\to S$ of
   step 1 and the formally smooth closed fibre of step 4. It gives formal smoothness of $S/R$ for
   the $\mathfrak m_S$-adic topology. Now [lem-weil-pbc-fs-adic-complete-source-target] gives the
   coordinate homomorphism $\widehat g:\widehat R\to\widehat S$ and formal smoothness of $\widehat
   S/\widehat R$ for the $\mathfrak m_S\widehat S$-adic topology. The map sends a compatible
   sequence represented by $r_n\bmod\mathfrak m_R^n$ to $g(r_n)\bmod\mathfrak m_S^n$; locality of
   $g$ makes these maps well-defined and compatible. Both $\widehat g\circ u$ and $v\circ g$ send
   $r$ to $g(r)\bmod\mathfrak m_S^n$ at every level, hence they agree.

6. For $T=R,S$, the completion $\widehat T$ is Noetherian by
   [lem-weil-pbc-adic-completion-noetherian]. Its maximal ideal $\mathfrak m_T$ is finitely
   generated since $T$ is Noetherian. By [lem-weil-pbc-adic-completion-mod-ideal], $\widehat T$ is
   complete for $I_T=\mathfrak m_T\widehat T$ and $\widehat T/I_T\cong T/\mathfrak m_T$, a field. By
   [lem-weil-pbc-adic-complete-jacobson-radical], every maximal ideal contains $I_T$; the field
   quotient then forces $I_T$ to be the unique maximal ideal. The first-coordinate formula in step 5
   sends the kernel of $\widehat R\to R/\mathfrak m_R$ into that of $\widehat S\to S/\mathfrak m_S$,
   so $\widehat g$ is local. Thus step 5 supplies exactly the formal-smoothness hypothesis for this
   local map of complete Noetherian local rings, and
   [lem-weil-pbc-formally-smooth-complete-local-regular] proves $\widehat g$ regular.

7. The ring $\widehat S$ is Noetherian by [lem-weil-pbc-adic-completion-noetherian]. For every prime
   $\mathfrak t\subset R$, its fibre $\widehat S\otimes_R\kappa(\mathfrak t)$ is therefore
   Noetherian by [lem-weil-pbc-fibre-ring-noetherian]. The regular maps $u$ from step 1 and
   $\widehat g$ from step 6 consequently satisfy every hypothesis of
   [lem-weil-pbc-regular-composition]. Their composite $h=v\circ g:R\to\widehat S$ is regular. In
   particular $D_{\mathfrak t}=\widehat S\otimes_R k_{\mathfrak t}$ is geometrically regular over
   $k_{\mathfrak t}$.

8. Fix $\mathfrak t$ and the finite product $F_{\mathfrak t}=\prod_iL_i$ of step 3. By
   [lem-weil-pbc-tensor-cancel-base-change], $D_{\mathfrak t}\cong\widehat S\otimes_SF_{\mathfrak
   t}$. The maps $c\otimes(x_i)_i\mapsto(c\otimes x_i)_i$ and $(c_i\otimes x_i)_i\mapsto\sum_i
   c_i\otimes e_ix_i$, extended additively, are mutually inverse: $e_ix_i$ denotes $x_i$ inserted in
   the $i$th coordinate and zero elsewhere; the $e_i$ are the finitely many orthogonal coordinate
   idempotents and sum to one. They give $D_{\mathfrak t}\cong\prod_i C_i$, where $C_i=\widehat
   S\otimes_S L_i=\widehat S\otimes_S\kappa(\mathfrak s_i)$, compatibly with the $k_{\mathfrak
   t}$-actions. Each $C_i$ is the localization of $D_{\mathfrak t}$ at $e_i$; explicitly all other
   coordinate idempotents become zero and the $i$th becomes one.

9. Each $C_i$ is geometrically regular over $k_{\mathfrak t}$. Indeed it is Noetherian by
   [lem-weil-pbc-fibre-ring-noetherian], applied to $S\to\widehat S$ at $\mathfrak s_i$. For any
   finite purely inseparable field extension $K/k_{\mathfrak t}$, $K\otimes_{k_{\mathfrak t}}C_i$ is
   the localization of $K\otimes_{k_{\mathfrak t}}D_{\mathfrak t}$ at $1\otimes e_i$, via $(a\otimes
   d)/(1\otimes e_i)^n\mapsto a\otimes(d/e_i^n)$, with inverse $a\otimes(d/e_i^n)\mapsto(a\otimes
   d)/(1\otimes e_i)^n$. The balancing and localization relations make these maps well-defined and
   their composites fix every displayed generator. The latter ring is regular by step 7 and
   [def-weil-pbc-g-ring]; [lem-weil-pbc-localization-of-regular-ring] makes its localization
   regular. This is exactly the definition of geometric regularity of $C_i$.

10. For every prime $\mathfrak s\subset S$, choose its contraction $\mathfrak t$ and its factor
   $L_i=\kappa(\mathfrak s)$ in step 3. Step 9 gives $\widehat S\otimes_S\kappa(\mathfrak s)$
   geometrically regular over $k_{\mathfrak t}$. The extension $\kappa(\mathfrak s)/k_{\mathfrak t}$
   is separable algebraic, and this fibre is Noetherian as already checked, so
   [lem-weil-pbc-geometric-regularity-separable-extension] gives geometric regularity over
   $\kappa(\mathfrak s)$ itself. The map $v$ is flat by
   [lem-weil-pbc-local-completion-faithfully-flat]. By [def-weil-pbc-g-ring] it is therefore
   regular. Since the original prime $\mathfrak q\subset B$ was arbitrary and $B$ is Noetherian by
   hypothesis, the same definition gives that $B$ is a G-ring. -/
theorem isGRing_of_weaklyEtale {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) (hf : f.WeaklyEtale)
    (hA : IsGRing A) : IsGRing B := by
  sorry

end RingHom
