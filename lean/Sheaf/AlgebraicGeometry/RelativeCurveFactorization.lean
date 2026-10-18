/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.FieldTheory.FinTrdeg
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

/-!
# Factorization through a relative curve

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, proof of Theorem 3.5,
Step 5, printed p. 163 (blueprint: lem-trf-relative-curve-factorization).

The base is a field spectrum or an excellent integral trait. The modification is
finite over a dense open, and the induced extension of generic residue fields has
transcendence degree one. Excellence is stated for all affine coordinate rings.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Factorization of a proper dominant integral scheme through a relative curve.
Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, Theorem 3.5, proof,
Step 5, printed p. 163 (blueprint: lem-trf-relative-curve-factorization).

The two alternatives in `hS` express the base up to scheme isomorphism, without
choosing a ring presentation. The witness `η` is the generic point of `X₀`;
dominance of `g` makes `g η` the generic point of `Y`. Thus the algebra structure
in the last clause is exactly the field inclusion induced by `g`, via its residue
field map, rather than an independently chosen extension.

Proof (the nine steps of the DAG node):
1. Write $S=\operatorname{Spec}A$, $k=\kappa(s)$ and $K=\kappa(X)$. Dominance sends the generic
   point of $X$ to $s$. The generic fibre is integral: on affine charts its rings are
   localizations of domains by $A\setminus\{0\}$, and its generic point is the generic point of
   $X$, with residue field $K$. It is of finite type over $k$, since localizing a finite list of
   algebra generators preserves that list. Thus [lem-sc-closed-irreducible-dimension-trdeg],
   applied to the entire generic fibre, gives $\operatorname{trdeg}_kK=d$. A nonempty affine
   chart in this fibre has a finite-type domain as coordinate ring and fraction field $K$ by
   [lem-sc-integral-function-field-affine-fraction]; its algebra generators generate $K$ as a
   field. Apply [lem-weil-pbc-finitely-generated-field-finite-transcendence-basis] and the
   definition of transcendence degree to choose a basis $t_1,\ldots,t_d$ of $K/k$.

2. Set $n=d-1$ and $Y=\mathbf P^n_S$. Its standard charts are
   $\operatorname{Spec}A[z_1,\ldots,z_n]$ by [lem-weil-pbc-projective-space-standard-charts].
   They are domains, and their generic points coincide on their nonempty pairwise overlaps, so
   $Y$ is integral; each chart maps its generic point to $s$, so $Y\to S$ is dominant. The
   identity closed embedding into $\mathbf P^n_S$ proves projectivity by [def-kun-projective],
   and [lemma-nagata-projective-space-base-change-proper] gives properness, hence finite type.
   The same chart description after replacing $A$ by $k$ gives $\kappa(Y_s)=k(z_1,\ldots,z_n)$;
   the indeterminates are a transcendence basis. Hence
   [lem-sc-closed-irreducible-dimension-trdeg] gives $\dim Y_s=n$. For $n=0$ the chart is
   $\operatorname{Spec}A$ and the field is $k$.

3. Choose a nonempty affine $V=\operatorname{Spec}B\subset X$ from a finite-type affine cover
   over $A$. By [lem-sc-integral-function-field-affine-fraction], write $t_i=b_i/c_i$ with
   $b_i,c_i\in B$ and $c_i\ne0$, for $1\le i\le n$. Put $c=\prod_i c_i$ (empty product $1$), and
   $U=\operatorname{Spec}B[1/c]$. This is nonempty and dense in $X$. The $A$-algebra map
   $A[z_1,\ldots,z_n]\to B[1/c]$, $z_i\mapsto t_i$, gives an $S$-morphism $r:U\to Y$ into the
   standard affine chart, by [def-weil-affine-spectrum] and
   [lem-weil-pbc-projective-space-standard-charts]. Its composite into $K$ is injective:
   $A\subset k$ and the $t_i$ are algebraically independent over $k$. Thus the generic point
   maps to the zero prime of this chart, the generic point of $Y$, so $r$ is dominant and
   induces $\kappa(Y)=k(t_1,\ldots,t_n)\subset K$.

4. Let $\gamma=(j,r):U\to X\times_SY$, where $j:U\hookrightarrow X$. The ring $A$ is Noetherian
   (a field, or an excellent ring). Thus $U$ is Noetherian by
   [lem-weil-pbc-finite-type-over-noetherian]. Every open of a Noetherian space is
   quasi-compact: otherwise a cover without a finite subcover gives a strictly increasing
   infinite chain of finite unions of its members. Consequently $j$ and $\gamma$ are
   quasi-compact, since preimages of affine opens are opens in $U$. Let $i:X_0\hookrightarrow
   X\times_SY$ be the scheme-theoretic image, with its factor map from $U$, supplied by
   [lem-weil-pbc-scheme-image-qc-kernel]. Write $a=\operatorname{pr}_X i$ and
   $g=\operatorname{pr}_Y i$. As $Y\to S$ is separated,
   [lemma-nagata-scheme-image-partial-section] says $a^{-1}(U)\to U$ is an isomorphism.

5. The support of $X_0$ is the closure of $\gamma(U)$ by [lemma-nagata-scheme-image-ideal-qc],
   so it is nonempty and irreducible. To check reducedness explicitly, take an affine open $W$
   in $X\times_SY$ meeting $X_0$. The open $\gamma^{-1}(W)$ is nonempty by density. Its sections
   inject into $K$ by [lem-sc-integral-scheme-stalks-in-function-field], applied to the integral
   scheme $U$. The affine ideal defining $X_0\cap W$ is $\ker(\mathcal O(W)\to\mathcal
   O_U(\gamma^{-1}W))$ by [lem-weil-pbc-scheme-image-qc-kernel]. This is a prime ideal, since
   the target embeds in a field; the quotient is therefore a domain. These affine charts cover
   $X_0$, so $X_0$ is reduced, hence integral. The open $a^{-1}(U)\cong U$ is dense in $X_0$.

6. The projections $X\times_SY\to X$ and $X\times_SY\to Y$ are proper by
   [lem-weil-pbc-proper-base-change], using respectively the properness of $Y\to S$ and the
   given properness of $X\to S$. Since $i$ is a closed immersion,
   [lem-weil-pbc-closed-immersion-proper] makes both $a$ and $g$ proper. The image of $a$
   contains the dense open $U$, and the image of $g$ contains the dense image $r(U)$, so both
   are dominant. The isomorphism $a^{-1}(U)\to U$ of [lemma-nagata-scheme-image-partial-section]
   is finite (on affine rings it is an isomorphism), so $a$ is generically finite in the
   required convention, with degree one.

7. Identify $\kappa(X_0)$ with $K$ using the common nonempty affine open $a^{-1}(U)\cong U$ and
   [lem-sc-integral-function-field-affine-fraction]. Under this identification, the field map
   induced by $g$ is the inclusion $k(t_1,\ldots,t_n)\subset K$ computed in step 3, since
   $g|_U=r$. The tower formula [lem-kun-transcendence-degree-tower] gives
   $d=n+\operatorname{trdeg}_{k(t_1,\ldots,t_n)}K$. The two known degrees are finite and
   $n=d-1$, so the remaining degree is one. This also treats $d=1$, when the intermediate field
   is simply $k$.

8. The ring $A$ is excellent: this is assumed for a trait and follows from
   [lem-exc-fields-excellent] for a field. The scheme $Y$ is of finite type over $A$. The
   composite $X_0\xrightarrow aX\to S$ is proper by [lem-weil-pbc-proper-composition], hence of
   finite type. For every affine open $W$ in either $Y$ or $X_0$,
   [lem-weil-pbc-lft-affine-pairs] applied with the entire affine base $S=\operatorname{Spec}A$
   says $\mathcal O(W)$ is a finite-type $A$-algebra. It is excellent by
   [lem-exc-finite-type-localization-excellent], taking the multiplicative subset $\{1\}$. This
   proves exactly the requested excellence of all affine coordinate rings.

9. All maps were constructed over $S$: by the fibre-product relation, $(X\to S)\circ a=(Y\to
   S)\circ g$. With $X_0,Y,a,g$ as above, steps 2, 5, 6, 7 and 8 give every asserted clause. No
   finite-field, perfectness, separability or smoothness hypothesis was used.
-/
theorem exists_relativeCurveFactorization
    {S X : Scheme.{u}}
    (hS : (∃ (k : Type u) (_ : Field k), Nonempty (S ≅ Spec (.of k))) ∨
      ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
        (_ : IsDiscreteValuationRing R), IsExcellent R ∧ Nonempty (S ≅ Spec (.of R)))
    (s : S) (hs : IsGenericPoint s Set.univ)
    (f : X ⟶ S) [IsProper f] [IsDominant f]
    [IsIntegral X] (hft : LocallyOfFiniteType f ∧ QuasiCompact f)
    (d : ℕ) (hd : 1 ≤ d)
    (hdim : topologicalKrullDim (f.fiber s) = (d : WithBot ℕ∞)) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ S) (X₀ : Scheme.{u})
      (a : X₀ ⟶ X) (g : X₀ ⟶ Y),
      (∀ U : Y.Opens, IsAffineOpen U → IsExcellent Γ(Y, U)) ∧
      IsIntegral Y ∧ IsHProjective q ∧ IsDominant q ∧
      LocallyOfFiniteType q ∧ QuasiCompact q ∧
      topologicalKrullDim (q.fiber s) = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
      (∀ U : X₀.Opens, IsAffineOpen U → IsExcellent Γ(X₀, U)) ∧
      IsIntegral X₀ ∧ IsProper a ∧ IsDominant a ∧
      (∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (a ∣_ U)) ∧
      IsProper g ∧ IsDominant g ∧ a ≫ f = g ≫ q ∧
      ∃ η : X₀, IsGenericPoint η Set.univ ∧
        @Algebra.trdeg (Y.residueField (g η)) (X₀.residueField η) _ _
          (g.residueFieldMap η).hom.toAlgebra = 1 := by
  sorry

end AlgebraicGeometry
