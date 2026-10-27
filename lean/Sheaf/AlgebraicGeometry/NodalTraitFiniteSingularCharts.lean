/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.NodalPointEtaleLocality
public import Sheaf.TraceFormula.StrictSemistableCurve
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.TraceFormula.GenericFibrePointsSmooth
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.SmoothTraitCurveLocalProperties
import Sheaf.AlgebraicGeometry.TraitNodalEtaleDvrModel
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource

/-! # Finite nonsmooth locus and pointed nodal charts over a trait

Source: Stacks Project, models.tex, Tags 0CDE, 0CDD and 0CDC
(blueprint: lem-sfb-nodal-trait-finite-singular-charts).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finitely presented nodal curve over a DVR with smooth generic fibre has finitely
many nonsmooth points, pointed binomial charts, and the stated total-space local geometry.
The origin is specified by its special-fibre image and vanishing of both coordinates.
Source: Stacks Project, models.tex, Tags 0CDE, 0CDD and 0CDC
(blueprint: lem-sfb-nodal-trait-finite-singular-charts).

Proof:
1. A DVR is Noetherian by [def-sc-discrete-valuation-ring]. Finite presentation includes quasi-
   compactness and local finite presentation by [def-sbc-locally-finite-presentation]; a finite
   polynomial presentation is in particular finite type. Thus [lem-weil-pbc-finite-type-over-
   noetherian] gives that $X$ is Noetherian. Its underlying space is Noetherian too: choose a
   finite affine cover, apply [lem-sc-affine-noetherian-underlying-space] on each member, and
   restrict any ascending chain of opens to these finitely many members. Each restriction
   stabilizes, hence the original chain stabilizes. We may use the nodal hypotheses at all
   nonsmooth geometric points, not just closed ones. Indeed, on an affine chart of a geometric
   fibre over $\Omega$, a nonclosed point is a component generic point, since the reduced fibre is
   pure one-dimensional. Apply [lem-trf-generic-fibre-points-smooth] to that affine chart over
   $\Omega$. It is flat and finitely presented over the field, is Noetherian by the finite-type
   theorem, and all its geometric fibres are reduced by the original geometric-fibre assumption.
   Its generic points are smooth. Therefore every nonsmooth geometric point is closed and
   satisfies exactly the assumed node equation.
2. Apply [lem-trf-nodal-family-fitting-singular], whose flatness, local finite presentation and
   geometric nodality hypotheses hold by assumption and step 1. Its closed subscheme
   $N=\operatorname{Sing}(f)$ has underlying set exactly the nonsmooth locus, and $N\to S$ is
   unramified. This set is contained in $X_k$: by the base-change clause of the same theorem for
   $S'=\operatorname{Spec}K$, the underlying set of
   $\operatorname{Sing}(f)\times_S\operatorname{Spec}K$, i.e. the set of points of $N$ over the
   generic point, is the nonsmooth locus of $X_K\to\operatorname{Spec}K$, which is empty because
   $X_K$ is smooth. By [lem-weil-pbc-unramified-base-change-open], $N_k\to\operatorname{Spec}k$ is
   unramified; [lem-trf-unramified-field-fibre-decomposition] identifies $N_k$ as a disjoint union
   of spectra of finite separable extensions of $k$. Thus its underlying topology is discrete. The
   special-fibre closed immersion identifies $|N_k|$ homeomorphically with all of $|N|$: every
   point of $N$ lies above the closed point of $S$. The closed subset $|N|\subseteq|X|$ is quasi-
   compact (extend an open cover by its open complement and use quasi-compactness of $X$). Its
   singleton open cover therefore has a finite subcover. Each singleton is closed in the discrete
   subspace $|N|$, hence closed in $X$ because $|N|$ is closed. This proves the finite closed
   special-point assertion, including $N=\varnothing$.
3. Let $V\subseteq X$ be the relative smooth locus supplied in step 2. Its nonempty fibres are
   pure one-dimensional: their geometric base changes are open subsets of the given pure one-
   dimensional geometric curves, hence have dimension one at every point; [lem-sc-fibre-dimension-
   after-base-change] gives the same local fibre dimensions before field extension. In the finite-
   type field setting this is the equidimensional-fibre formulation of relative dimension in [def-
   sbc-smooth-morphisms]. Apply [lem-sfb-smooth-trait-curve-local-properties] to $V\to S$. Every
   $\mathcal O_{X,x}=\mathcal O_{V,x}$ for $x\in V$ is regular and has dimension at most two; if
   $x$ is closed in $X_k$, it remains closed in $V_k$ and this dimension is exactly two. No
   assertion that every nonsmooth point is nonregular has been used.
4. For $x\in N$, apply [lem-sfb-trait-nodal-etale-dvr-model]. Step 1 verifies its condition at
   every nonsmooth geometric point. Its smooth-generic clause gives an injective local etale DVR
   extension $R\to R'$ with the original $\pi$ still a uniformizer and etale $S$-maps $p:U\to X$,
   $q:U\to M_n$, with $p(u)=x$ and $n\geq1$. These are precisely the required structural maps; it
   remains to check the image of $u$ under $q$, since the cited statement does not explicitly
   prescribe that image.
5. Write $w=q(u)$. In $M_n$, $D(a)$ has ring $R'[a,a^{-1}]$ by eliminating $b=\pi^n/a$, and
   likewise for $D(b)$. These opens are smooth over $R'$ directly by [def-sbc-smooth-morphisms]: a
   map from the finite presentation $R'[t,s]/(ts-1)$ to $B/I$, $I^2=0$, lifts by choosing lifts
   $t_0,s_0$ with $t_0s_0=1+i$ and replacing $s_0$ by $s_0(1-i)$. The etale map
   $\operatorname{Spec}R'\to S$ is smooth by [lem-weil-pbc-etale-smooth-zero-dimensional-fibres],
   so these opens are smooth over $S$ by [lem-trf-smooth-composition]. If $w$ belonged to either
   open, the pointwise smoothness equivalence in [lem-trf-etale-source-smoothness], first for $q$
   and then for $p$, would make $f$ smooth at $x$, a contradiction. Thus both $a,b$ vanish at $w$.
   Since $u$ lies above the closed point of $S$ and $\pi$ remains a uniformizer of the local ring
   $R'$, also $\pi$ vanishes at $w$. The ideal $(\pi,a,b)$ is maximal with quotient $k'$, so $w=o$
   as required.
6. For any pointed diagram as in the statement, apply [lem-sfb-etale-stalk-invariants] to both $p$
   at $u$ and $q$ at $u$. It gives regularity equivalences between $\mathcal O_{X,x}$, $\mathcal
   O_{U,u}$ and $\mathcal O_{M_n,o}$, and equality of their Krull dimensions. Apply [lem-sfb-dvr-
   binomial-local-geometry] over the DVR $R'$ with uniformizer $\pi$. It states that $\dim\mathcal
   O_{M_n,o}=2$ and that this ring is regular exactly for $n=1$. Hence $X$ is regular at $x$ if
   and only if $n=1$, in every such diagram, and $\dim\mathcal O_{X,x}=2$ at every nonsmooth
   point.
7. Every point lies either in $V$ or in $N$. Step 3 gives the local dimension bound and regularity
   on $V$, and step 6 gives dimension two on $N$; together they give the stated dimension
   assertions, including every closed point of $X_k$. The nonregular points are a subset of the
   finite closed special set $N$ of step 2. At such a point the chart of steps 4--5 has $n\geq1$,
   and step 6 excludes $n=1$, so $n\geq2$. Empty fibres, the empty scheme and disconnected fibres
   cause no change in any step. All inputs apply to arbitrary DVRs and arbitrary residue
   characteristic.
-/
theorem nodal_trait_finite_singular_charts
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R))
    [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hgeneric : Smooth (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))))
    (hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of R)),
      IsReduced (pullback f g) ∧ (pullback f g).IsPureDimension 1)
    (hnodal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of R)) (z : ↥(pullback (C := Scheme.{u}) f g)),
      IsClosed ({z} : Set ↥(pullback f g)) → z ∉ (pullback.snd f g).smoothLocus →
        Nonempty
          (@AlgEquiv Ω
            (AdicCompletion (IsLocalRing.maximalIdeal ((pullback f g).presheaf.stalk z))
              ((pullback f g).presheaf.stalk z))
            (MvPowerSeries (Fin 2) Ω ⧸
              Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})
            _ _ _ ((pullback.snd f g).completedLocalScalarMap z).toAlgebra inferInstance)) :
    IsNoetherian X ∧
    Set.Finite {x : X | x ∉ f.smoothLocus} ∧
    (∀ x : X, x ∉ f.smoothLocus →
      IsClosed ({x} : Set X) ∧ f x = IsLocalRing.closedPoint R) ∧
    (∀ x : X, x ∈ f.smoothLocus → IsRegularLocalRing (X.presheaf.stalk x)) ∧
    (∀ x : X, x ∉ f.smoothLocus →
      ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
        (φ : R →+* R') (n : ℕ) (U : Scheme.{u}) (p : U ⟶ X)
        (q : U ⟶ (StrictSemistableModel.nodal (A := .of R') ((φ π) ^ n)).scheme) (v : U),
        Function.Injective φ ∧ IsLocalHom φ ∧ Etale (Spec.map (CommRingCat.ofHom φ)) ∧
        Irreducible (φ π) ∧ 1 ≤ n ∧ Etale p ∧ Etale q ∧ p v = x ∧
        p ≫ f = q ≫ (StrictSemistableModel.nodal (A := .of R') ((φ π) ^ n)).baseMap ≫
          Spec.map (CommRingCat.ofHom φ) ∧
        (StrictSemistableModel.nodal (A := .of R') ((φ π) ^ n)).baseMap (q v) =
          IsLocalRing.closedPoint R' ∧
        ∀ i : Fin 2, Ideal.Quotient.mk _ (MvPolynomial.X i) ∈ (q v).asIdeal) ∧
    (∀ (x : X), x ∉ f.smoothLocus →
      ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
        (φ : R →+* R') (n : ℕ) (U : Scheme.{u}) (p : U ⟶ X)
        (q : U ⟶ (StrictSemistableModel.nodal (A := .of R') ((φ π) ^ n)).scheme) (v : U),
        Function.Injective φ → IsLocalHom φ → Etale (Spec.map (CommRingCat.ofHom φ)) →
        Irreducible (φ π) → 1 ≤ n → Etale p → Etale q → p v = x →
        p ≫ f = q ≫ (StrictSemistableModel.nodal (A := .of R') ((φ π) ^ n)).baseMap ≫
          Spec.map (CommRingCat.ofHom φ) →
        (StrictSemistableModel.nodal (A := .of R') ((φ π) ^ n)).baseMap (q v) =
          IsLocalRing.closedPoint R' →
        (∀ i : Fin 2, Ideal.Quotient.mk _ (MvPolynomial.X i) ∈ (q v).asIdeal) →
        (IsRegularLocalRing (X.presheaf.stalk x) ↔ n = 1)) ∧
    (∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2) ∧
    (∀ z : f.fiber (IsLocalRing.closedPoint R), IsClosed ({z} : Set _) →
      ringKrullDim (X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) z)) = 2) ∧
    Set.Finite {x : X | ¬ IsRegularLocalRing (X.presheaf.stalk x)} ∧
    (∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
      IsClosed ({x} : Set X) ∧ f x = IsLocalRing.closedPoint R ∧
      ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
        (φ : R →+* R') (n : ℕ) (U : Scheme.{u}) (p : U ⟶ X)
        (q : U ⟶ (StrictSemistableModel.nodal (A := .of R') ((φ π) ^ n)).scheme) (v : U),
        Function.Injective φ ∧ IsLocalHom φ ∧ Etale (Spec.map (CommRingCat.ofHom φ)) ∧
        Irreducible (φ π) ∧ 2 ≤ n ∧ Etale p ∧ Etale q ∧ p v = x ∧
        p ≫ f = q ≫ (StrictSemistableModel.nodal (A := .of R') ((φ π) ^ n)).baseMap ≫
          Spec.map (CommRingCat.ofHom φ) ∧
        (StrictSemistableModel.nodal (A := .of R') ((φ π) ^ n)).baseMap (q v) =
          IsLocalRing.closedPoint R' ∧
        ∀ i : Fin 2, Ideal.Quotient.mk _ (MvPolynomial.X i) ∈ (q v).asIdeal) := by
  sorry

end AlgebraicGeometry
