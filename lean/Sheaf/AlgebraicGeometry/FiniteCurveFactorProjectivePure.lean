/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Sheaf.AlgebraicGeometry.PureDimension

import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.QuasiFinite.Basic
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents

/-!
# Projectivity and pure fibres for a finite relative curve factor

Source: literature/stacks-project/morphisms.tex, Tags 01WE, 0B3I, 02FZ and 02FY
(blueprint: lem-sfb-finite-curve-factor-projective-pure).

The statement combines projectivity after finite base change with the lower and upper
local-dimension bounds for finite relative curve factors. Its proof uses the recorded
projective-composition, finite-over-projective, graph-embedding, finite-type permanence,
generic-point, fibre-dimension, finite-fibre and constant-local-dimension statements.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite relative factor of a projective pure curve family is projective and has pure
one-dimensional geometric fibres.

Source: Stacks Project, Morphisms, Tags 01WE (lemma-H-projective-composition), 0B3I
(lemma-finite-projective), 02FZ (lemma-openness-bounded-dimension-fibres), and 02FY
(lemma-dimension-fibre-after-base-change); (blueprint: lem-sfb-finite-curve-factor-projective-pure).

Proof plan:
1. Compose the H-projective maps $X\to S\to\operatorname{Spec}k$ to obtain H-projectivity of
$X/k$. Apply the affine-base clause of finite-over-projective to $Y\to X\to\operatorname{Spec}k$
and to $T\to S\to\operatorname{Spec}k$: the base is affine Noetherian and the finite-type
$k$-schemes $X,S$ are quasi-compact, so the required global projective embeddings are available.
This proves H-projectivity of $Y/k,T/k$. Projectivity makes $S/k$ and $T/k$ proper, hence
separated. Apply the finite-constant projective graph theorem with $F=k$, $R=Y$ (closed in some
$\mathbf P^N_k$), the separated $k$-scheme $T$ and $c=g$: the graph $(i,g):Y\hookrightarrow\mathbf
P^N_T$ is a closed immersion over $T$, so $g$ is H-projective, and (taking $S'=T$) $g$ is proper.
The same theorem with $R=X$, the separated $k$-scheme $S$ and $c=f$ shows that $f$ is proper.
Uses: lem-trf-h-projective-composition, lem-fin-finite-over-projective, def-pc-projective-
morphism, lem-pc-projective-proper, def-weil-proper-morphism, lem-sfb-finite-constant-projective-
graph.

2. The composite of $g$ with $T\to\operatorname{Spec}k$ is locally of finite type by hypothesis;
finite-type cancellation makes $g$ locally of finite type. Step 1 makes $g$ and $f$ proper, hence
of finite type. Base change therefore makes each ordinary or geometric fibre of $g$ and of $f$ of
finite type over its field. All these fibres are Noetherian, since a field is Noetherian. These
observations supply the finite-type and Noetherian hypotheses in the following steps.
Uses: lem-weil-pbc-proper-fp-permanence, lem-pc-projective-proper, def-weil-proper-morphism, lem-
sfb-finite-type-composition-base-change, lem-weil-pbc-finite-type-over-noetherian.

3. Let $\xi$ be the generic point of the integral scheme $Y$ and $\eta$ that of $T$, supplied by
sobriety. Every nonempty open of $Y$ contains $\xi$. Continuity gives
$g(Y)\subseteq\overline{\{g(\xi)\}}$; dominance and uniqueness of generic points imply
$g(\xi)=\eta$. Thus $\xi$ corresponds to a point $\widetilde\xi$ of $Y_\eta$, using the fibre
projection homeomorphism onto $g^{-1}(\eta)$. The given pure dimension one of $Y_\eta$ and the
equidimensional-open local-dimension theorem, applied with the whole fibre as its open subset,
give $\dim_{\widetilde\xi}Y_\eta=1$.
Uses: def-pc-integral-scheme, lem-sc-scheme-sober, def-sc-generic-point, def-pc-scheme-fibre, lem-
sbc-equidimensional-open-local-dimension.

4. For $y\in Y$ write $d(y)=\dim_{\widetilde y}Y_{g(y)}$. The locus $U_0=\{y:d(y)\leq0\}$ is open
by the local-fibre-dimension openness theorem, applicable by step 2. Step 3 shows $\xi\notin U_0$.
Since any nonempty open of $Y$ contains $\xi$, $U_0$ is empty. Local dimension at an actual point
is nonnegative, so $d(y)\geq1$ for every $y\in Y$. This is the asserted ordinary-fibre local lower
bound; it uses neither flatness nor normality.
Uses: lem-weil-pbc-local-fibre-dimension-open, def-sc-generic-point, def-kun-topological-
dimension-at-point.

5. Fix a geometric point $\bar t:\operatorname{Spec}\Omega\to T$ and put
$B=Y\times_T\operatorname{Spec}\Omega$, $C=X\times_S\operatorname{Spec}\Omega$, using $q\bar t$
for the second map. Associativity of fibre products identifies $B\to C$ with the base change of
$h:Y\to X\times_ST$, so it is finite. For each $b\in B$ with image $y\in Y$, fibre-dimension
invariance under base change identifies $\dim_b B$ with $d(y)$, hence gives $\dim_b B\geq1$. The
given geometric-fibre hypothesis makes $C$ pure of dimension one. If $B$ is empty the purity
conclusion is vacuous; otherwise $C$ is nonempty. Applying the equidimensional-open theorem to
$C$, followed by the supremum-of-local-dimensions formula, gives $\dim C=1$.
Uses: def-pc-fibre-product, lem-weil-pbc-finite-morphism-permanence, lem-sc-fibre-dimension-after-
base-change, lem-sbc-equidimensional-open-local-dimension, lem-weil-pbc-dimension-supremum-local-
dimensions, def-weil-pure-dimension.

6. For every $c\in C$, the scheme-theoretic fibre $B_c$ of $B\to C$ is finite over $\kappa(c)$ by
finite base change. The finite-over-field theorem writes it as $\operatorname{Spec}D$ with $D$
finite-dimensional over $\kappa(c)$. Apply the finite-algebra discrete-spectrum theorem to the
local ring $R=\kappa(c)$, whose only prime is zero: $\operatorname{Spec}D$ is finite discrete. An
irreducible nonempty closed subset of a discrete space is a singleton, so its dimension is zero
when nonempty; when empty its dimension is $-\infty$. Thus every $B_c$ has dimension at most zero.
Uses: lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-finite-over-field-affine-finite-dim,
lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum, def-kun-topological-krull-dimension.

7. Apply the fibre-and-image dimension bound to the $\Omega$-morphism $B\to C$: both schemes are
finite type over $\Omega$ by step 2, $\dim C\leq1$ by step 5, and all its fibres have dimension at
most zero by step 6. With $d=1,n=0$ it gives $\dim B\leq1$. The whole $B$ is an open neighbourhood
of any $b\in B$, so $\dim_bB\leq\dim B\leq1$. Together with step 5 this gives $\dim_bB=1$
everywhere. The constant-local-dimension component theorem applies because $B$ is Noetherian by
step 2. Every irreducible component of $B$ therefore has dimension one, as required. The empty
case was already handled in step 5.
Uses: lem-zl-finite-type-fibre-image-dimension-bounds, def-kun-topological-dimension-at-point,
lem-sbc-constant-local-dimension-components. -/
theorem finite_curve_factor_projective_pure
    (k : Type u) [Field k]
    {S X T Y : Scheme.{u}}
    (pS : S ⟶ Spec (.of k)) (pX : X ⟶ Spec (.of k))
    (pT : T ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ S) (q : T ⟶ S) (ν : Y ⟶ X) (g : Y ⟶ T)
    (hf : f ≫ pS = pX) (hq : q ≫ pS = pT) (hν : ν ≫ pX = pY)
    (hg : g ≫ pT = pY)
    [IsIntegral S] [IsIntegral X] [IsIntegral T] [IsIntegral Y]
    [LocallyOfFiniteType pS] [QuasiCompact pS]
    [LocallyOfFiniteType pX] [QuasiCompact pX]
    [LocallyOfFiniteType pT] [QuasiCompact pT]
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [IsHProjective f] [IsHProjective pS]
    [IsFinite q] [Surjective q] [IsFinite ν] [Surjective ν]
    [IsDominant g]
    (hcompat : ν ≫ f = g ≫ q)
    (hfinite : IsFinite (pullback.lift ν g hcompat))
    (hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ S),
      Scheme.IsPureDimension (pullback (C := Scheme.{u}) f s) 1)
    (hgGeneric : Nonempty (pullback (C := Scheme.{u}) g T.fromSpecFunctionField) ∧
      Scheme.IsPureDimension (pullback (C := Scheme.{u}) g T.fromSpecFunctionField) 1)
    : IsHProjective pX ∧ IsHProjective pY ∧ IsHProjective pT ∧ IsHProjective g ∧
      (∀ y : Y, ((1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDimAt (g.asFiber y)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        Scheme.IsPureDimension (pullback (C := Scheme.{u}) g t) 1) := by
  sorry

end AlgebraicGeometry
