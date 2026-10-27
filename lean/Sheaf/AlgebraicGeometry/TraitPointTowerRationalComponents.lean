/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.Compactification.StrictTransform
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.TraceFormula.NodalOpenLocus
import WeilConjectures.Blowup.InvertibleCenter
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Complement
import WeilConjectures.Compactification.StrictTransformBlowup
import Sheaf.AlgebraicGeometry.DvrNodalChartBlowupCalculus
import Sheaf.AlgebraicGeometry.LocalSurfaceMaximalBlowupGeometry
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Rational components in a tower of point blowups over a trait

Source: Stacks Project, divisors.tex, Tag 080E; resolve.tex, Tags 0AGQ and 0AGR;
models.tex, Tags 0CDC and 0CDD; de Jong, Lemma 3.13 proof, printed p.609.
(blueprint: lem-sfb-trait-point-tower-rational-components).

The helpers only name the actual reduced geometric fibre and its two projections.
Components are represented by reduced closed immersions whose ranges are irreducible
components. This retains their scheme structure and their specified coefficient field.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The reduction of the actual geometric fibre, without changing its scheme structure.
Source: Stacks Project, Tag 01J4, in the geometric-component induction of de Jong,
Lemma 3.13 (blueprint: lem-sfb-trait-point-tower-rational-components). -/
def traitTowerGeometricReduction {X S : Scheme.{u}} (g : X ⟶ S)
    (Ω : Type u) [Field Ω] (c : Spec (.of Ω) ⟶ S) : Scheme.{u} :=
  (pullback g c).nilradical.subscheme

/-- The canonical map from the reduced geometric fibre to the original source.
Source: Stacks Project, Tag 01J4; de Jong, Lemma 3.13
(blueprint: lem-sfb-trait-point-tower-rational-components). -/
def traitTowerGeometricReductionToSource {X S : Scheme.{u}} (g : X ⟶ S)
    (Ω : Type u) [Field Ω] (c : Spec (.of Ω) ⟶ S) :
    traitTowerGeometricReduction g Ω c ⟶ X :=
  (pullback g c).nilradical.subschemeι ≫ pullback.fst g c

/-- The specified coefficient-field structure on the reduced geometric fibre.
Source: Stacks Project, Tag 01J4; de Jong, Lemma 3.13
(blueprint: lem-sfb-trait-point-tower-rational-components). -/
def traitTowerGeometricReductionToField {X S : Scheme.{u}} (g : X ⟶ S)
    (Ω : Type u) [Field Ω] (c : Spec (.of Ω) ⟶ S) :
    traitTowerGeometricReduction g Ω c ⟶ Spec (.of Ω) :=
  (pullback g c).nilradical.subschemeι ≫ pullback.snd g c

/-- Mixed blowups of nodal singular points and regular surface points have only rational
positive-dimensional geometric components. Their scheme-theoretic strict transforms
project isomorphically to the original components and embed in the next reduced fibre.
Source: Stacks Project, Tags 080E, 0AGQ, 0AGR, 0CDC, 0CDD; de Jong, Lemma 3.13, p.609.
(blueprint: lem-sfb-trait-point-tower-rational-components).

Step 1. Fix $c:\operatorname{Spec}\Omega\to X_0$ and put
$Y_j=X_j\times_{X_0}\operatorname{Spec}\Omega$, $B_j=(Y_j)_{\mathrm{red}}$. Each reduced point
centre has a finite-type quasi-coherent ideal, since its ambient scheme is Noetherian. By
[lemma-nagata-blowup-proper] each arrow is proper, hence finite type by
[def-weil-proper-morphism]. By [lem-sfb-finite-type-composition-base-change], $Y_j$ is finite type
over $\Omega$, so [lem-weil-pbc-finite-type-over-noetherian] makes it Noetherian. Its underlying
space, also that of $B_j$, has finitely many irreducible components by
[lem-sc-noetherian-finite-irreducible-components]. At $j=0$, $Y_0=\operatorname{Spec}\Omega$,
giving the induction base including the entire assertion for $m=0$.

Step 2. For a centre $z=z_j$, its residue field $l=\kappa(z)$ is finite over $k$: $z$ is closed in
the special fibre, which is finite type over $k$ (initially $X_0$ is H-projective and subsequent
blowups are finite type); apply [lem-weil-pbc-zariski-lemma] on an affine neighbourhood in that
fibre. If the image of $c$ in $T$ is not the closed point,
$Z=z\times_{X_0}\operatorname{Spec}\Omega$ is empty. Otherwise $Z$ is a closed subscheme of
$z\times_k\operatorname{Spec}\Omega$: the additional equations express equality of the two maps to
the separated $k$-scheme $(X_0)_k$. Indeed [lem-pc-projective-proper] makes $X_0\to T$ proper, so
[def-weil-proper-morphism] makes its base change to $k$ separated. By
[lem-weil-pbc-fibre-product-affine-spectra] the larger product has algebra $l\otimes_k\Omega$,
spanned over $\Omega$ by a $k$-basis of $l$. Thus $Z=\operatorname{Spec}D$ with $D$ finite
dimensional over $\Omega$, possibly zero. It is Artinian by
[lem-weil-pbc-finite-dim-algebra-artinian] and has finitely many points by
[lem-sfb-artinian-spectrum-finite]. For every prime $\mathfrak p$ of $D$, the finite-dimensional
domain $D/\mathfrak p$ is a field (multiplication by a nonzero element is injective, hence
surjective), and equals $\Omega$: the minimal polynomial of any element splits into linear
factors. Thus every reduced point of $Z$ is $\operatorname{Spec}\Omega$. This permits nonreduced
$D$ and inseparable $l/k$.

Step 3. In case (a), shrink to an affine open neighbourhood of $z$ contained in the stipulated
nodal neighbourhood. The restricted family is flat finitely presented with smooth generic fibre
and the stated nodal geometric fibres; the affine restriction is finitely presented: its
coordinate algebra is finite type over the Noetherian ring $A$, hence finitely presented by
[lem-weil-pbc-finite-type-noetherian-finite-presentation]. Apply
[lem-sfb-nodal-trait-finite-singular-charts] to this restriction. Since $z$ is nonregular, it has
the common pointed etale chart with $M_n=\operatorname{Spec}R'[x,y]/(xy-\pi^n)$, $n\ge2$. The
exceptional geometric fibre of its point blowup is one $\mathbf P^1$ for $n=2$, and two $\mathbf
P^1$'s meeting in a point for $n>2$, by [lem-sfb-dvr-nodal-chart-blowup-calculus]. To use this
over the specified $\Omega$-point of $Z$, extend its residue-field map to the chart point using
[lem-weil-pbc-algebraic-extension-embeds-algebraically-closed]; the chart residue extension is
finite separable. By [lem-sfb-flat-pullback-blowup-chart-restrictions], shrink the etale
neighbourhood to isolate that point; both pulled-back centre ideals are then the reduced point
ideals. Their blowups give the same geometric fibre over this chosen lift. Hence the exceptional
fibre of $b_{j+1}$ over each reduced point of $Z$ has exactly the asserted one-line or two-line
description over $\Omega$. This uses only nodality near this centre.

Step 4. In case (b), put $R=\mathcal O_{X_j,z}$, a regular local ring of dimension two. Its
canonical local-spectrum morphism is flat and pulls the reduced centre back to the maximal ideal
by [lem-weil-pbc-spec-local-ring-canonical-morphism]. The comparison of
[lem-sfb-flat-pullback-blowup-chart-restrictions] therefore identifies its exceptional fibre with
that of $b_{j+1}$ over $z$. By [lem-sfb-local-surface-maximal-blowup-geometry], this fibre is
$\mathbf P^1_l$. For each reduced point of $Z$, base change along its map $l\to\Omega$ gives
$\mathbf P^1_\Omega$; the base-change identification is just associativity in
[def-nagata-projective-space-base-change]. Consequently the reduced inverse image of $Z$ is a
finite union of closed projective lines in either case (a) or (b): every point maps to one of its
finitely many reduced points, and the corresponding geometric fibres cover the underlying inverse
image. Nilpotents in $Z$ do not add points.

Step 5. Assume the dimension and component assertions at stage $j$, and let $L\cong\mathbf
P^1_\Omega$ be one of its positive-dimensional components, given its reduced closed subscheme
structure in $Y_j$. Let $\mathcal I$ be the centre ideal on $X_j$ and $J=\mathcal I\mathcal O_L$.
Its vanishing set is contained in $Z$; hence it is finite and does not contain the generic point
of $L$. On each of the two affine charts $\operatorname{Spec}\Omega[t]$ of [def-sc-p1-standard],
$J$ is an ideal of $\Omega[t]$. It is nonzero because it is the unit ideal at the generic point.
By [lem-pur-polynomial-field-pid] it equals $(f)$ for a nonzero polynomial $f$. Multiplication by
$f$ identifies the chart's structure sheaf with this ideal (the polynomial ring is a domain). Thus
$J$ is invertible, including when the centre intersection is empty or nonreduced. By
[thm-nagata-strict-transform-is-blowup] the strict transform of the morphism $L\to X_j$ is
$\operatorname{Bl}_J L$; by [cor-nagata-blowup-cartier-iso] its projection to $L$ is an
isomorphism. No separability is used in this argument.

Step 6. Write $L^{\mathrm{st}}$ for that strict transform. By [def-nagata-strict-transform] it is
a closed subscheme of $L\times_{X_j}X_{j+1}$. The closed immersion $L\hookrightarrow Y_j$, pulled
back by $X_{j+1}\to X_j$, gives a closed immersion $L\times_{X_j}X_{j+1}\hookrightarrow Y_{j+1}$
by [lem-weil-pbc-closed-immersion-base-change]. Hence $L^{\mathrm{st}}$ is closed in $Y_{j+1}$. As
it is isomorphic to the reduced scheme $L$, its map factors through $B_{j+1}$: affine-locally the
defining surjection kills every nilpotent, since the target ring is reduced. The resulting map
from the reduction ring remains surjective, so this factorization is a closed immersion. By the
closure definition, its support is the closure of the inverse image of $L\setminus Z$; this is
dense in $L$ since $Z$ is finite. This proves exactly the claimed scheme-theoretic
strict-transform assertion, including its specified $\Omega$-structure.

Step 7. By [thm-nagata-global-blowup-complement], $Y_{j+1}\to Y_j$ is an isomorphism away from
$Z$. Each point outside the inverse image of $Z$ therefore lies either on the inverse image of one
of the finitely many old lines, or over a zero-dimensional old component. The former points lie in
the corresponding $L^{\mathrm{st}}$ by its closure definition. Each zero-dimensional component of
the finite-type $\Omega$-scheme $B_j$ is a single closed reduced $\Omega$-point, by
[lem-weil-pbc-zariski-lemma]; if it is outside $Z$, its inverse image is again a closed point.
Points over $Z$ lie on the finitely many exceptional lines in Steps 3--4. Thus the support of
$B_{j+1}$ is covered by finitely many closed subschemes isomorphic to $\mathbf P^1_\Omega$ and
finitely many closed points. An irreducible subset of a finite union of closed sets lies in one of
them: otherwise its intersections with them would express it as a finite union of proper closed
subsets. Consequently every irreducible component is one of these lines or one of these points. A
proper irreducible closed subset of a projective line is a point, as its intersection with either
standard affine chart is cut out by a nonzero polynomial, with finitely many roots. Hence the
dimension is at most one, and every positive-dimensional component is a whole projective line.
This completes the induction for every $j$ and every $c$.
-/
theorem traitPointTowerRationalComponents
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F]
    (m : ℕ) (X : Fin (m + 1) → Scheme.{u})
    [hIntegral : ∀ j, IsIntegral (X j)] [hNoetherian : ∀ j, IsNoetherian (X j)]
    (f : X 0 ⟶ Spec (.of A)) [IsHProjective f]
    (b : ∀ i : Fin m, X i.succ ⟶ X i.castSucc)
    (g : ∀ j : Fin (m + 1), X j ⟶ X 0)
    (hg0 : g 0 = 𝟙 (X 0))
    (hg : ∀ i : Fin m, b i ≫ g i.castSucc = g i.succ)
    (z : ∀ i : Fin m, X i.castSucc)
    (I : ∀ i : Fin m, (X i.castSucc).IdealSheafData)
    (hz : ∀ i : Fin m, IsClosed ({z i} : Set (X i.castSucc)) ∧
      (g i.castSucc ≫ f) (z i) = IsLocalRing.closedPoint A)
    (hI : ∀ i : Fin m, I i = ((X i.castSucc).fromSpecResidueField (z i)).ker)
    (hb : ∀ i : Fin m, ∃ e : X i.succ ≅ (I i).blowup,
      e.hom ≫ (I i).blowupMap = b i)
    (hcentres : ∀ i : Fin m,
      (Flat (g i.castSucc ≫ f) ∧ LocallyOfFinitePresentation (g i.castSucc ≫ f) ∧
        QuasiCompact (g i.castSucc ≫ f) ∧ QuasiSeparated (g i.castSucc ≫ f) ∧
        Smooth (pullback.snd (g i.castSucc ≫ f)
          (Spec.map (CommRingCat.ofHom (algebraMap A F)))) ∧
        (∃ U : (X i.castSucc).Opens, z i ∈ U ∧
          ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (.of A)),
            IsReduced (pullback (U.ι ≫ g i.castSucc ≫ f) a) ∧
            (pullback (U.ι ≫ g i.castSucc ≫ f) a).IsPureDimension 1 ∧
            ∀ x : ↥(pullback (C := Scheme.{u}) (U.ι ≫ g i.castSucc ≫ f) a),
              IsClosed ({x} : Set _) →
              (∃ V : (pullback (U.ι ≫ g i.castSucc ≫ f) a).Opens,
                x ∈ V ∧ Smooth (V.ι ≫ pullback.snd (U.ι ≫ g i.castSucc ≫ f) a)) ∨
              IsOrdinaryNode K (pullback (U.ι ≫ g i.castSucc ≫ f) a) x) ∧
        ¬ IsRegularLocalRing ((X i.castSucc).presheaf.stalk (z i))) ∨
      (IsRegularLocalRing ((X i.castSucc).presheaf.stalk (z i)) ∧
        ringKrullDim ((X i.castSucc).presheaf.stalk (z i)) = (2 : WithBot ℕ∞)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (c : Spec (.of Ω) ⟶ X 0) :
    (∀ j : Fin (m + 1),
      topologicalKrullDim (traitTowerGeometricReduction (g j) Ω c) ≤ 1 ∧
      (irreducibleComponents (traitTowerGeometricReduction (g j) Ω c)).Finite ∧
      ∀ (L : Scheme.{u}) (l : L ⟶ traitTowerGeometricReduction (g j) Ω c),
        IsReduced L → IsClosedImmersion l →
        Set.range l ∈ irreducibleComponents (traitTowerGeometricReduction (g j) Ω c) →
        0 < topologicalKrullDim L →
        ∃ e : L ≅ ProjectiveLine (Spec (.of Ω)),
          e.hom ≫ ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω) =
            l ≫ traitTowerGeometricReductionToField (g j) Ω c) ∧
    (∀ (i : Fin m) (L : Scheme.{u})
      (l : L ⟶ traitTowerGeometricReduction (g i.castSucc) Ω c),
      IsReduced L → IsClosedImmersion l →
      Set.range l ∈ irreducibleComponents (traitTowerGeometricReduction (g i.castSucc) Ω c) →
      0 < topologicalKrullDim L →
      IsIso (strictTransformToSource
        (l ≫ traitTowerGeometricReductionToSource (g i.castSucc) Ω c)
        (b i) (I i).support.compl) ∧
      ∃ s : strictTransform (l ≫ traitTowerGeometricReductionToSource (g i.castSucc) Ω c)
          (b i) (I i).support.compl ⟶ traitTowerGeometricReduction (g i.succ) Ω c,
        IsClosedImmersion s ∧
        s ≫ traitTowerGeometricReductionToSource (g i.succ) Ω c =
          strictTransformMap (l ≫ traitTowerGeometricReductionToSource (g i.castSucc) Ω c)
            (b i) (I i).support.compl ∧
        s ≫ traitTowerGeometricReductionToField (g i.succ) Ω c =
          strictTransformToSource (l ≫ traitTowerGeometricReductionToSource (g i.castSucc) Ω c)
            (b i) (I i).support.compl ≫ l ≫
              traitTowerGeometricReductionToField (g i.castSucc) Ω c) := by
  sorry

end AlgebraicGeometry
