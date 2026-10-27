/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.ZetaSeries
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Etale.Field
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Localization.Integral
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import WeilConjectures.RingTheory.DvrGaloisNormalizationRamificationDvd
import Sheaf.FieldTheory.FiniteDVRResidueNormalAction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.LinearAlgebra.Dimension.Free
import Sheaf.AlgebraicGeometry.Curve.NormalSeparablePointSmooth
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource

/-! # Smoothness of a tame Galois normalization of a curve

Source: Stacks Project, More Algebra, Tags 09EB and 09ED, and Varieties, Tag 0B8Y;
de Jong, Families of curves and alterations, section 3.5, printed page 607
(blueprint: lem-sfb-tame-galois-curve-normalization-smooth).

The normalization and its map are the canonical constructions `C.normalizationIn L`
and `C.fromNormalizationIn L`. The chosen open `U` is specified to be exactly the
complement of the branch subscheme, and the residue degrees use the canonical residue maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite Galois normalization of a smooth integral curve, of degree invertible in the
base field and etale away from a finite etale reduced branch subscheme, is smooth. Above
that subscheme every point is closed, its relative residue degree divides the Galois degree,
and its residue field is finite separable over the base field. Normality means that the
stalks are integrally closed domains; the domain condition follows from `IsIntegralCurve`.
The base field need not be perfect, and neither curve is assumed projective.

Source: Stacks Project, More Algebra, Tag 09EB, lemma-galois-conclusion, and Tag 09ED,
lemma-galois-galois; Varieties, Tag 0B8Y, lemma-regular-point-on-curve
(blueprint: lem-sfb-tame-galois-curve-normalization-smooth).

Proof, following the seven steps of the node:
1. First locate the branch points and their residue fields. Since $D\to\operatorname{Spec}K$ is
   finite, $D=\operatorname{Spec}H$ for a finite-dimensional $K$-algebra $H$. Its etaleness and
   [lem-weil-pbc-etale-algebra-over-field-product] give $H\cong\prod_i K_i$ with each $K_i/K$
   finite separable. Every point of this finite product spectrum is closed, with residue field one
   of the $K_i$. The closed immersion $D\hookrightarrow C$ takes it to a closed point $x$ of $C$
   and induces $\kappa(x)\cong K_i$ by [lem-weil-pbc-closed-immersion-residue-field-iso]. Thus
   $\kappa(x)/K$ is finite separable. This argument also treats the empty product, when there is
   no branch point.
2. Fix $y\mapsto x\in D$ and an affine open $U=\operatorname{Spec}R\subset C$ containing $x$.
   Write $\mathfrak p\subset R$ for $x$. By [lem-sfb-curve-closed-point-affine-local-model],
   $\mathfrak p$ is maximal and $A=R_{\mathfrak p}\cong\mathcal O_{C,x}$ is a Noetherian local
   domain of dimension one, compatibly with $K$ and residue fields. By
   [lem-weil-pbc-smooth-scheme-over-field-regular], $A$ is regular, so [lem-sc-regular-dim1-dvr]
   makes $A$ a DVR. The affine function-field result gives $F=\operatorname{Frac}R$; also
   $\operatorname{Frac}A=F$, since $R\subset R_{\mathfrak p}\subset\operatorname{Frac}R$ and a
   quotient of two elements of $R$ is still a quotient of elements of $A$.
3. By the definition of normalization in $L$, $\nu^{-1}U=\operatorname{Spec}B$ with $B$ the
   integral closure of $R$ in $L$; write $\mathfrak q\subset B$ for $y$. Finiteness of $\nu$ says
   that $B$ is a finite $R$-module. The domain $B/\mathfrak q$ is therefore finite-dimensional
   over $R/\mathfrak p=\kappa(x)$, and is a field by
   [lem-weil-pbc-finite-dimensional-domain-is-field]. Hence $\mathfrak q$ is maximal and $y$ is
   closed in $\nu^{-1}U$. Any specialization of $y$ in $Y$ maps to a specialization of the closed
   point $x$, hence lies over $x$ and is in $\nu^{-1}U$. Consequently $y$ is closed in $Y$.
   Applying the affine local-model lemma to the curve $Y$ identifies $\mathcal O_{Y,y}$ with
   $B_{\mathfrak q}$, and identifies its residue field with that of $B_{\mathfrak q}$ compatibly
   with $K$.
4. Put $S=R\setminus\mathfrak p$ and $T=S^{-1}B$. By
   [lem-weil-pbc-integral-closure-commutes-localization], $T$ is the integral closure of
   $A=S^{-1}R$ in $S^{-1}L=L$; the latter equality holds since all elements of $S$ are already
   nonzero units in $L$. The prime $\mathfrak n=S^{-1}\mathfrak q$ lies over the maximal ideal of
   $A$ and is maximal: $T/\mathfrak n=S^{-1}(B/\mathfrak q)=B/\mathfrak q$, a field, since every
   element of $S$ has nonzero image in that field. By
   [lem-weil-pbc-localization-prime-residue-field-iso], $T_{\mathfrak n}\cong B_{\mathfrak q}$ and
   $\kappa(\mathfrak n)\cong\kappa(y)$, with the residue-field scalar maps induced from $R$
   unchanged; likewise $\kappa(\mathfrak m_A)=\kappa(x)$. Apply
   [lem-sbc-dvr-galois-normalization-ramification-dvd] to the DVR $A$, its fraction field $F$, the
   finite Galois extension $L/F$, and $n=d=[L:F]$. It gives $f=[\kappa(y):\kappa(x)]\mid d$. No
   unramifiedness at $y$, perfection, or projectivity is used.
5. Write $k=\kappa(x)$ and $E=\kappa(y)$. This extension is finite by the preceding step. The
   residue-normality theorem [lem-exc-dvr-residue-normal-action], applied to the same $A,L,T$ and
   $\mathfrak n$, says that $E/k$ is normal. If $\operatorname{char}K=p>0$, then
   $\operatorname{char}k=p$ and $p\nmid d$, because $K\hookrightarrow k$ is an inclusion of fields
   and $d$ is invertible in $K$. Choose an algebraic closure of $E$ using
   [lem-pc-algebraic-closure-exists-unique], and apply [lem-exc-normal-field-degree-factors] to
   $E/k$: for its relative separable closure $E_s$, $[E:k]=s[E:E_s]$ with $[E:E_s]=p^c$. Thus
   $p^c\mid f\mid d$, so $c=0$ and $[E:E_s]=1$. The nonzero element $1$ then spans the
   one-dimensional $E_s$-space $E$, giving $E=E_s$; by [def-weil-pbc-relative-separable-closure]
   $E/k$ is separable. In characteristic zero, any minimal polynomial $P$ over $k$ has positive
   degree $r$ and nonzero derivative: its leading derivative coefficient is $r$ times its nonzero
   leading coefficient. The irreducible derivative criterion
   [lem-trf-irreducible-separable-derivative] therefore makes every such $P$ separable. Thus in
   either characteristic $E/k$ is finite separable.
6. Step 1 gives $k/K$ finite separable and step 5 gives $E/k$ finite separable. By
   [lem-zl-separable-permanence], $E/K$ is separable algebraic, and by
   [lem-weil-pbc-field-degree-multiplicativity] it is finite, with $[E:K]=[E:k][k:K]$. Since $Y$
   is a normal integral $K$-curve and $y$ is closed by step 3,
   [lem-sfb-normal-curve-separable-point-smooth] applies to $Y,y$: its local ring is integrally
   closed by the assumed normality, and its residue field is finite separable over $K$.
   Consequently $Y\to\operatorname{Spec}K$ is smooth on some open neighbourhood of every point
   over $D$.
7. For $z\in Y$ outside $\nu^{-1}D$, use the assumed etaleness of $\nu$ over $C\setminus D$. Since
   $C\to\operatorname{Spec}K$ is smooth at $\nu(z)$, the pointwise assertion of
   [lem-trf-etale-source-smoothness] makes its composite with this etale restriction smooth at
   $z$. Together with step 6 this proves smoothness at every point of $Y$. The open smooth
   neighbourhoods supplied at these points cover $Y$, so the local definition of smoothness gives
   smoothness of its structure morphism. If $D$ is empty, this last argument applies everywhere;
   if $d=1$, the divisibility argument gives $f=1$ and all preceding steps remain valid.
-/
theorem tame_galois_curve_normalization_smooth
    (K : Type u) [Field K] (C : Scheme.{u})
    (q : C ⟶ Spec (.of K)) [IsIntegralCurve q] [Smooth q]
    (L : Type u) [Field L] [Algebra C.functionField L]
    [FiniteDimensional C.functionField L] [IsGalois C.functionField L]
    (d : ℕ) (hd : 1 ≤ d) (hdegree : Module.finrank C.functionField L = d)
    (hunit : IsUnit (d : K))
    [IsIntegralCurve (C.fromNormalizationIn L ≫ q)]
    [IsFinite (C.fromNormalizationIn L)]
    (hnormal : ∀ y : C.normalizationIn L,
      IsIntegrallyClosed ((C.normalizationIn L).presheaf.stalk y))
    (D : Scheme.{u}) (i : D ⟶ C) [IsClosedImmersion i] [IsReduced D]
    [IsFinite (i ≫ q)] [Etale (i ≫ q)]
    (U : C.Opens) (hU : (U : Set C) = (Set.range i)ᶜ)
    (hetale : Etale (C.fromNormalizationIn L ∣_ U)) :
    (∀ y : C.normalizationIn L, C.fromNormalizationIn L y ∈ Set.range i →
      IsClosed ({y} : Set (C.normalizationIn L)) ∧
      @Module.finrank (C.residueField (C.fromNormalizationIn L y))
        ((C.normalizationIn L).residueField y) _ _
        ((C.fromNormalizationIn L).residueFieldMap y).hom.toAlgebra.toModule ∣ d ∧
      ((C.fromNormalizationIn L ≫ q).residueFieldAlgebraMap y).Finite ∧
      @Algebra.IsSeparable K ((C.normalizationIn L).residueField y) _ _
        ((C.fromNormalizationIn L ≫ q).residueFieldAlgebraMap y).toAlgebra) ∧
    Smooth (C.fromNormalizationIn L ≫ q) := by
  sorry

end AlgebraicGeometry
