/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.FieldTheory.SeparableClosure
public import WeilConjectures.TraceFormula.LocalDimensionFormula
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.ProperBasic
import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import WeilConjectures.AlgebraicGeometry.LocalizedSeparablePolynomialModel
import WeilConjectures.AlgebraicGeometry.SpreadPurelyInseparableFactors

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.AlgebraicGeometry.StructureSheaf

/-!
# Generic radicial-etale factorization of a proper morphism

Source: Stacks Project, Tags 02NW, 030K, 030N, 00UB, 00UC and 04DF
(blueprint: lem-sfb-proper-generic-radicial-etale-factorization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper dominant generically finite morphism of integral separated finite-type
schemes over a field admits a separable-first factorization over a dense affine open.
Source: Stacks Project, Tags 02NW, 030K, 030N, 00UB, 00UC and 04DF
(blueprint: lem-sfb-proper-generic-radicial-etale-factorization).

The function-field identification is a ring equivalence with the canonical relative
separable closure, commuting with the generic stalk maps into the function field of
the actual pullback. The auxiliary integrality and generic-point witnesses only
make these canonical maps well typed.

Proof:

1. The image of $f$ is closed by [lem-weil-pbc-proper-closed-image] and dense by dominance, hence
equals $S$. Properness gives quasi-compactness, quasi-separatedness and finite type by
[pqf-lem-proper-basic]. The field $k$ is Noetherian (its only ideals are $0$ and $k$), so
[lem-weil-pbc-finite-type-over-noetherian] makes $S$ Noetherian.
Uses: lem-weil-pbc-proper-closed-image, pqf-lem-proper-basic,
lem-weil-pbc-finite-type-over-noetherian.

2. Let $\eta$ be the generic point of $S$. Choose an affine neighbourhood $\operatorname{Spec}A$
of $\eta$ and cover its inverse image by nonempty affine opens $\operatorname{Spec}B_i$. By
[lem-sc-integral-function-field-affine-fraction], $A\subset K$, $B_i\subset L$ are domains with
the indicated fraction fields, compatibly with the generic stalk map
[def-sfb-dominant-function-field-map]. Put $C_i=(A\setminus\{0\})^{-1}B_i\subset L$. It is a
$K$-linear subspace of the finite-dimensional space $L$, hence finite-dimensional. By
[lem-weil-pbc-finite-dimensional-domain-is-field] it is a field; since it contains $B_i$ it
contains every fraction of $B_i$, so $C_i=L$. The generic fibre of each chart is
$\operatorname{Spec}C_i$: maps to this affine fibre are precisely ring maps out of $B_i$ inverting
every nonzero element of $A$, by the affine-spectrum and fibre-product universal properties. Its
sole point projects to the zero prime of $B_i$, namely the generic point of $X$. Thus the whole
set-theoretic fibre over $\eta$ is that one point.
Uses: lem-sc-integral-function-field-affine-fraction, def-sfb-dominant-function-field-map,
lem-weil-pbc-finite-dimensional-domain-is-field, def-weil-affine-spectrum, def-pc-fibre-product.

3. Apply [lem-weil-pbc-generic-finite-morphism-open-neighborhood] using Step 1 and the singleton
fibre of Step 2; $S$ has only one irreducible component. Obtain a dense open on which $f$ is
finite and choose a nonempty affine open $\operatorname{Spec}A$ inside it. Its inverse image is
$\operatorname{Spec}B$, with $B$ finite over $A$, by [def-weil-finite-integral-morphism]. Both are
domains with fraction fields $K,L$ by [lem-sc-integral-function-field-affine-fraction].
Restricting further to $D(a)$ replaces $A,B$ by $A[1/a],B[1/a]$: the affine-spectrum universal
property identifies the inverse image with the spectrum of the localized ring. Module generators
localize, so finiteness persists.
Uses: lem-weil-pbc-generic-finite-morphism-open-neighborhood, def-weil-finite-integral-morphism,
lem-sc-integral-function-field-affine-fraction, def-weil-affine-spectrum,
def-weil-ring-localization-away.

4. By [lem-weil-pbc-separable-first-purely-inseparable], $K_s/K$ is separable algebraic and
$L/K_s$ purely inseparable. As a $K$-subspace of $L$, $K_s$ has finite dimension. Choose $\alpha$
generating $K_s/K$ by [lem-weil-pbc-finite-separable-extension-primitive-element]. Its monic
minimal polynomial $P$ is separable by [def-weil-pbc-separable-algebraic-extension]. The
isomorphism $K[T]/(P)\simeq K_s$ of [lem-weil-pbc-minimal-polynomial-quotient-field-iso], together
with the power basis of [lem-weil-pbc-monic-quotient-free], gives $d=\deg P=[K_s:K]\ge1$.
Uses: lem-weil-pbc-separable-first-purely-inseparable,
lem-weil-pbc-finite-separable-extension-primitive-element,
def-weil-pbc-separable-algebraic-extension, lem-weil-pbc-minimal-polynomial-quotient-field-iso,
lem-weil-pbc-monic-quotient-free.

5. Apply [lem-weil-pbc-localized-separable-polynomial-model] to $A,K,K_s,\alpha$. After inverting
a nonzero element of $A$, $P$ descends to a monic $Q\in A[T]$ with $UQ+VQ^{\prime}=1$ for some
$U,V\in A[T]$. Also $\alpha\in B[1/a]$ for some nonzero $a\in A$: the same calculation as Step 2
shows $(A\setminus\{0\})^{-1}B=L$, and an element of this localization has a single denominator in
$A$. Invert this additional $a$; polynomial identities and module generators remain valid. Set
$C=A[T]/(Q)$ and send $T$ to $\alpha\in B$. This embeds $C$ in $B$: by the power basis
[lem-weil-pbc-monic-quotient-free], every element has degree less than $d$; an element evaluating
to zero in $L$ has all coefficients zero, since $P$ is the degree-$d$ minimal polynomial and
$A\hookrightarrow K$. Thus $C=A[\alpha]$ is a domain, and its fraction field is $K(\alpha)=K_s$.
Uses: lem-weil-pbc-localized-separable-polynomial-model, lem-weil-pbc-monic-quotient-free.

6. The same power basis makes $C$ free of rank $d$ and finite over $A$. In $C$, $VQ^{\prime}=1$,
so adjoining the inverse of $Q^{\prime}$ changes nothing. Apply
[lem-weil-pbc-standard-etale-monic-derivative] to conclude that
$e:\operatorname{Spec}C\to\operatorname{Spec}A$ is etale. It is surjective by
[lem-weil-pbc-integral-injective-lying-over]: $A\to C$ is injective and each element of the finite
algebra $C$ is integral. This integrality is supplied by
[lem-weil-pbc-finite-algebra-is-integral], applied to the finite ring map $A\to C$. The map $C\to
B$ is finite: a set generating $B$ as an $A$-module also generates it as a $C$-module. Hence we
have $\operatorname{Spec}B\to\operatorname{Spec}C\to\operatorname{Spec}A$ with composite $f$ on
this open.
Uses: lem-weil-pbc-monic-quotient-free, lem-weil-pbc-standard-etale-monic-derivative,
lem-weil-pbc-integral-injective-lying-over, lem-weil-pbc-finite-algebra-is-integral,
def-weil-finite-integral-morphism.

7. Apply [lem-weil-pbc-spread-purely-inseparable-factors] with $A\prime=C$, $E=B$, $K\prime=K_s$.
Here $A$ is a Noetherian domain: $\operatorname{Spec}A$ is an affine open of the Noetherian scheme
$S$ of Step 1, so [pqf-lem-affine-open-locnoeth] applies, $C$ is a finite etale domain of fraction
field $K_s$, $B$ is finite over $C$ with fraction field $L$, and $L/K_s$ is finite purely
inseparable by Step 4. Invert the resulting nonzero $s\in A$. Take
$S_0=\operatorname{Spec}A[1/s]$, $T_0=\operatorname{Spec}C[1/s]$ and
$X_0=\operatorname{Spec}B[1/s]$. The lemma gives the universal homeomorphism $u$; the original
module generators show it is finite. The localized polynomial $Q$ and its Bezout identity give
finite etaleness of $e$ by Step 6 again, and lying over
[lem-weil-pbc-integral-injective-lying-over], with integrality from
[lem-weil-pbc-finite-algebra-is-integral], gives surjectivity. The localized power basis has $d$
elements, so $e_*\mathcal O_{T_0}$ is free of rank $d$. Localization of a domain at a nonzero
element preserves its fraction field, so [lem-weil-pbc-spec-domain-stalks-function-field] makes
$T_0$ integral with $k(T_0)=K_s$ and the required inclusions. The nonempty open $S_0$ is dense in
integral $S$.
Uses: pqf-lem-affine-open-locnoeth, lem-weil-pbc-spread-purely-inseparable-factors,
lem-weil-pbc-monic-quotient-free, lem-weil-pbc-standard-etale-monic-derivative,
lem-weil-pbc-integral-injective-lying-over, lem-weil-pbc-finite-algebra-is-integral,
lem-weil-pbc-spec-domain-stalks-function-field.
-/
theorem Scheme.Hom.exists_generic_radicial_etale_factorization
    (k : Type u) [Field k] {X S : Scheme.{u}}
    [IsIntegral X] [IsIntegral S]
    (pX : X ⟶ Spec (CommRingCat.of k)) (pS : S ⟶ Spec (CommRingCat.of k))
    [IsSeparated pX] [IsSeparated pS]
    [LocallyOfFiniteType pX] [QuasiCompact pX]
    [LocallyOfFiniteType pS] [QuasiCompact pS]
    (f : X ⟶ S) (hf : f ≫ pS = pX) [IsProper f] [IsDominant f]
    (hfinite : @FiniteDimensional S.functionField X.functionField _ _
      (Scheme.Hom.dominantFunctionFieldAlgebra f).toModule) :
    Surjective f ∧ ∃ (U : S.Opens),
      (U : Set S).Nonempty ∧ Dense (U : Set S) ∧ IsAffineOpen U ∧
      IsFinite (pullback.snd f U.ι) ∧
      ∃ (hX₀ : IsIntegral (pullback f U.ι)) (T : Scheme.{u}) (hT : IsIntegral T)
        (a : pullback f U.ι ⟶ T) (e : T ⟶ U.toScheme),
        a ≫ e = pullback.snd f U.ι ∧ IsFinite a ∧
        (topologically IsHomeomorph).universally a ∧
        IsFinite e ∧ Etale e ∧ Surjective e ∧
        ∃ (d : ℕ), 1 ≤ d ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank
            ((Scheme.Modules.pushforward e).obj (SheafOfModules.unit T.ringCatSheaf)) d ∧
          d = @Module.finrank S.functionField
            (@separableClosure S.functionField X.functionField _ _
              (Scheme.Hom.dominantFunctionFieldAlgebra f)) _ _
            (@Submodule.module S.functionField X.functionField _ _
              (Scheme.Hom.dominantFunctionFieldAlgebra f).toModule
              ((@Subalgebra.toSubmodule S.functionField X.functionField _ _
                (Scheme.Hom.dominantFunctionFieldAlgebra f))
                (@IntermediateField.toSubalgebra S.functionField X.functionField _ _
                  (Scheme.Hom.dominantFunctionFieldAlgebra f)
                  (@separableClosure S.functionField X.functionField _ _
                    (Scheme.Hom.dominantFunctionFieldAlgebra f))))) ∧
          ∃ (hj : (pullback.fst f U.ι)
              (genericPoint (pullback f U.ι : Scheme.{u})) = genericPoint X)
            (ha : a (genericPoint (pullback f U.ι : Scheme.{u})) = genericPoint T)
            (φ : T.functionField ≃+*
              (@separableClosure S.functionField X.functionField _ _
                (Scheme.Hom.dominantFunctionFieldAlgebra f))),
            ∀ t : T.functionField,
              ((pullback.fst f U.ι).functionFieldMap hj).hom (φ t : X.functionField) =
                (a.functionFieldMap ha).hom t := by
  sorry

end AlgebraicGeometry
