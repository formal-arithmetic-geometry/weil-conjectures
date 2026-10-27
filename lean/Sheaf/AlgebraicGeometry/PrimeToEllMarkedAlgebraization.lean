/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank

import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.UniversallyCatenaryDimensionFormula
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.CompleteLocalExcellence
import WeilConjectures.RingTheory.CompletionDimension
import WeilConjectures.RingTheory.DimensionQuasiFiniteOverPolynomialAlgebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg
import WeilConjectures.RingTheory.GRingCompletionRegular
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.LocalizationRegular
import Sheaf.Paper.NormalLocusOpen
import WeilConjectures.RingTheory.RegularComposition
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange

/-!
# Partial algebraization preserving a marking and prime-to-ell degree

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose V 2.1.2 and
3.1.1--3.1.4, pp. 64--66, and IX 1.3, p. 132
(blueprint: lem-per-prime-to-ell-marked-algebraization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A normal complete local scheme admits a marked partial algebraization after a finite
cover of degree prime to `ell`. The generic-point triangle fixes the function-field map,
and the stalk-completion triangle fixes the canonical completion morphism.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, V 2.1.2 and 3.1.1--3.1.4,
pp. 64--66, with geometric assembly as in IX 1.3, p. 132
(blueprint: lem-per-prime-to-ell-marked-algebraization).

Proof plan, following the ten steps of the node:

1. Write $X=\operatorname{Spec}A$ and choose an ideal $I\subseteq A$ with $Z=V(I)$. Apply
[lem-per-prime-to-ell-equivariant-cohen-presentation] to $A,\ell$, obtaining $B,H,V,r$ and
$A^+=B^H$. Put $X^+=\operatorname{Spec}A^+$. The map $A\hookrightarrow A^+$ is module-finite, so
[lem-weil-pbc-finite-algebra-is-integral] and [lem-weil-pbc-integral-injective-lying-over] give
a finite surjection $p:X^+\to X$. The function-field degree is prime to $\ell$ by the
presentation. By [lem-weil-pbc-finite-over-complete-local-product], the finite domain $A^+$ is
Noetherian complete local. It is normal: an element of $\operatorname{Frac}(B^H)$ integral over
$B^H$ is integral over $B$, hence belongs to $B$ by normality; being a fraction of invariant
elements, it is fixed by $H$, hence belongs to $B^H$. In equal characteristic $A^+=A$ and $p$ is
the identity.

2. Apply [lem-per-equivariant-marked-cylinder-algebraization] to this formal presentation and
the single ideal $I^+=IA^+$. Its hypotheses hold: $H$ has invertible order in $V$, fixes the
variables, and the finite map is etale away from an element nonzero on the coefficient special
fibre. Obtain coordinates $u_i$, $D=V^H[[u_1,\ldots,u_{r-1}]]$, a quasi-finite $D[T]$-algebra
$C$, a maximal $\mathfrak n$ over $(\mathfrak m_D,T)$, and an ideal $J\subset C$, with
$\widehat{C_{\mathfrak n}}\cong A^+$ carrying $J\widehat{C_{\mathfrak n}}$ onto $I^+$. The
formal-presentation node gives that $D$ is complete regular Noetherian local of dimension $d-1$:
in equal characteristic $r=d$, and in mixed characteristic $r=d-1$ over a DVR. It also gives
that $\ell$ is a unit in $D$.

3. The ring $D$ is excellent by [lem-per-complete-local-excellence]. Finite-type and
localization permanence [lem-exc-finite-type-localization-excellent] make $C$ and
$L=C_{\mathfrak n}$ excellent and Noetherian. By [lem-weil-pbc-local-completion-faithfully-flat]
the map $L\to A^+=\widehat L$ is faithfully flat. Ideal contraction
[lem-weil-pbc-faithfully-flat-ideal-contraction], applied to the zero ideal, embeds $L$ in the
domain $A^+$. If $a/b\in\operatorname{Frac}L$ is integral over $L$, its image in
$\operatorname{Frac}(A^+)$ is integral over $A^+$, hence lies in $A^+$. Thus $a\in bA^+$.
Contraction for the principal ideal $bL$ gives $a\in bL$, so $a/b\in L$. Consequently $L$ is a
normal domain. This is the faithfully-flat normality-descent argument written out for the
particular local domains.

4. The kernel $K$ of $C\to C_{\mathfrak n}$ is finitely generated, since $C$ is Noetherian. For
each of a finite set of generators $k_j$, choose $s_j\notin\mathfrak n$ with $s_jk_j=0$, using
the definition of localization. Set $s=\prod_j s_j$ (or $1$ if the kernel is zero). Then
$s\notin\mathfrak n$ and $C_s\to C_{\mathfrak n}$ is injective: a fraction in its kernel has
numerator in $K$, annihilated by $s$. Thus $C_s$ is a domain. Replacing $C,J,\mathfrak n$ by
their localizations at $s$ leaves $L$, its completion, and the extended ideal $I^+$ unchanged.
It preserves finite type over $D$ and quasi-finiteness over $D[T]$: an open restriction just
removes points from each finite fibre.

5. The integral affine Noetherian scheme $\operatorname{Spec}C$ is excellent in the sense of
[lem-per-excellent-normalization-preparation]: for an affine open
$V\subseteq\operatorname{Spec}C$, the open immersion $V\to\operatorname{Spec}C$ is locally of
finite type between affine schemes, so $\mathcal O(V)$ is a finite type $C$-algebra, excellent
by [lem-exc-finite-type-localization-excellent]. Apply
[lem-per-excellent-normalization-preparation] to $\operatorname{Spec}C$. It has a dense open $U$
isomorphic to an open of its normal normalization. Choose a nonempty principal open
$D(h)\subseteq U$. Its coordinate ring $C_h$ is a normal domain: it is the ring of an affine
open in a normal integral scheme. Hence [lem-weil-pbc-normal-locus-open] makes the normal locus
of $C$ open. It contains $\mathfrak n$ by Step 3. Choose $t\notin\mathfrak n$ with $D(t)$ in
this locus, and replace $C$ by $R=C_t$ and $J$ by $JR$. Put $W=\operatorname{Spec}R$,
$Y_0=\operatorname{Spec}D$, $w=\mathfrak nR$ and $Z_W=V(JR)$. The scheme $W$ is normal integral
affine excellent Noetherian; its local ring at $w$ is still $L$, so
$X^+=\operatorname{Spec}\widehat{\mathcal O_{W,w}}$.

6. The composite $D\to R\to L\to A^+$ is the injective formal-coordinate inclusion of Step 2.
Therefore $D\to R$ is injective, so $f_0:W\to Y_0$ is dominant. It is finite type since $R$ was
obtained from a finite-type $D$-algebra by two principal localizations. The point $w$ remains
maximal, with finite residue field over $D/\mathfrak m_D$, and lies over the closed point of
$Y_0$. Since $\ell$ is already a unit in $D$, its image is a unit in $R$.

7. The morphism $W\to\mathbf A^1_D$ furnished by $D[T]\to R$ is locally quasi-finite. By
[lem-weil-pbc-separated-lqf-base-change], for each $y\in Y_0$ its base change $W_y\to\mathbf
A^1_{\kappa(y)}$ is locally quasi-finite. It is an affine finite-type map, so the corresponding
ring map is quasi-finite at every prime. Apply
[lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra] with the field $\kappa(y)$ and one
variable. It gives $\dim W_y\leq1$ (including empty fibres).

8. We check that the generic fibre has dimension exactly one. By
[lem-weil-pbc-completion-dimension], $\dim L=\dim A^+$. The finite integral injection $A\to A^+$
gives $\dim A^+=d$ by [lem-weil-pbc-finite-algebra-is-integral,
lem-weil-pbc-integral-injective-dimension-equal]. Apply
[lem-exc-dimension-formula-universally-catenary-finite-type-domain] to $D\subset R$ at the
maximal point $w$ over $\mathfrak m_D$. Excellence makes $D$ universally catenary;
$\operatorname{ht}(w)=d$, $\operatorname{ht}(\mathfrak m_D)=d-1$, and the residue extension is
finite, hence has transcendence degree zero. The formula therefore gives
$\operatorname{trdeg}_{\operatorname{Frac}D}\operatorname{Frac}R=1$. The generic fibre has
coordinate ring $R\otimes_D\operatorname{Frac}D$, an integral finite-type algebra over a field,
so [lem-weil-pbc-finite-type-domain-dimension-trdeg] gives dimension one.

9. Since $L$ is excellent, it is a G-ring. Thus [lem-weil-pbc-g-ring-completion-regular] gives a
regular ring map $L\to\widehat L=A^+$. The map $R\to L$ is regular by
[lem-weil-pbc-localization-regular]. The fibre of $R\to A^+$ over a prime $\mathfrak q\subset R$
is zero if $\mathfrak q\not\subseteq w$, since some element of $\mathfrak q\setminus w$ is
inverted in $L$. If $\mathfrak q\subseteq w$, it is the fibre of $L\to A^+$ at $\mathfrak qL$,
whose residue field is $\kappa(\mathfrak q)$. These fibres are Noetherian by the completion node
(and trivially for the zero ring). Hence [lem-weil-pbc-regular-composition] applies and shows
that $R\to A^+$ is regular. Its spectrum map is precisely the canonical completion morphism
$g:X^+\to W$.

10. Under $\widehat L\cong A^+$ we have $JR\cdot A^+=IA^+$, so inverse images of closed sets
give $g^{-1}Z_W=V(IA^+)=p^{-1}Z$. Moreover $Z_W$ is nowhere dense. Since $X$ is integral and
$V(I)$ is nowhere dense, $I$ contains a nonzero element (also when $I=A$, corresponding to empty
$Z$). Injectivity $A\to A^+$ makes $IA^+\ne0$, hence $JR\ne0$. A nonzero ideal in the domain $R$
does not contain the generic point in its zero set, so $V(JR)$ is nowhere dense. This proves all
clauses.
-/
theorem exists_primeToEll_marked_algebraization
    (ell : ℕ) (hEll : ell.Prime) (X : Scheme.{u})
    [IsAffine X] [IsNoetherian X] [IsIntegral X] [IsLocalRing Γ(X, ⊤)]
    [IsAdicComplete (IsLocalRing.maximalIdeal Γ(X, ⊤)) Γ(X, ⊤)]
    (hNormal : IsNormalScheme X) (d : ℕ) (hd : 2 ≤ d)
    (hDim : topologicalKrullDim X = (d : WithBot ℕ∞))
    (hInv : ∀ x : X, IsUnit (ell : X.presheaf.stalk x))
    (Z : Set X) (hZ : IsClosed Z) (hRare : IsNowhereDense Z) :
    ∃ (Xplus Y₀ W : Scheme.{u})
      (_ : IsAffine Xplus) (_ : IsNoetherian Xplus) (_ : IsIntegral Xplus)
      (_ : IsLocalRing Γ(Xplus, ⊤))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal Γ(Xplus, ⊤)) Γ(Xplus, ⊤))
      (_ : IsAffine Y₀) (_ : IsNoetherian Y₀) (_ : IsIntegral Y₀)
      (_ : IsLocalRing Γ(Y₀, ⊤))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal Γ(Y₀, ⊤)) Γ(Y₀, ⊤))
      (_ : IsAffine W) (_ : IsNoetherian W) (_ : IsIntegral W)
      (p : Xplus ⟶ X) (_ : Algebra X.functionField Xplus.functionField)
      (f₀ : W ⟶ Y₀) (w : W) (Z_W : Set W) (g : Xplus ⟶ W)
      (e : Xplus ≅ Spec (CommRingCat.of
        (AdicCompletion (IsLocalRing.maximalIdeal (W.presheaf.stalk w))
          (W.presheaf.stalk w)))),
      IsNormalScheme Xplus ∧ IsFinite p ∧ Surjective p ∧
      (Spec.map (CommRingCat.ofHom
        (algebraMap X.functionField Xplus.functionField)) ≫ X.fromSpecFunctionField =
        Xplus.fromSpecFunctionField ≫ p) ∧
      Nat.Coprime (Module.finrank X.functionField Xplus.functionField) ell ∧
      IsRegularScheme Y₀ ∧ IsExcellent Γ(Y₀, ⊤) ∧
      topologicalKrullDim Y₀ = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
      IsNormalScheme W ∧ IsExcellent Γ(W, ⊤) ∧
      IsDominant f₀ ∧ LocallyOfFiniteType f₀ ∧ QuasiCompact f₀ ∧
      (∀ y : Y₀, topologicalKrullDim (f₀.fiber y) ≤ (1 : WithBot ℕ∞)) ∧
      topologicalKrullDim (f₀.fiber (genericPoint Y₀)) = (1 : WithBot ℕ∞) ∧
      IsClosed ({w} : Set W) ∧ IsClosed ({f₀ w} : Set Y₀) ∧
      IsClosed Z_W ∧ IsNowhereDense Z_W ∧
      (g = e.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (W.presheaf.stalk w)
          (AdicCompletion (IsLocalRing.maximalIdeal (W.presheaf.stalk w))
            (W.presheaf.stalk w)))) ≫ W.fromSpecStalk w) ∧
      p ⁻¹' Z = g ⁻¹' Z_W ∧ RingHom.IsRegular (g.appTop).hom ∧
      (∀ y : Y₀, IsUnit (ell : Y₀.presheaf.stalk y)) ∧
      (∀ v : W, IsUnit (ell : W.presheaf.stalk v)) ∧
      (ringChar Γ(X, ⊤) = ringChar (IsLocalRing.ResidueField Γ(X, ⊤)) →
        ∃ h : Xplus = X, p = eqToHom h) := by
  sorry

end AlgebraicGeometry
