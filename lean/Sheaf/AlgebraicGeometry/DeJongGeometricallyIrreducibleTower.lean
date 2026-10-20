/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.Paper.OrgogozoInductionData
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.KrullDimension

import Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.ReductionGenericFibre
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.GenericComponentsSplit
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
public import Mathlib.AlgebraicGeometry.Noetherian

public import Mathlib.AlgebraicGeometry.Fiber

public import Mathlib.AlgebraicGeometry.Properties

public import Mathlib.Topology.Sober

public import Mathlib.Topology.Defs.Filter

public import Sheaf.RingTheory.ExcellentRing
import Sheaf.AlgebraicGeometry.ClosedDominantDimension
import Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve
import Sheaf.AlgebraicGeometry.GeometricallyIntegralCurveFactorization

/-!
# de Jong geometrically irreducible alteration tower

Source: de Jong, Families of curves and alterations (1997), Theorem 5.9 (i)--(iii),
Situation 5.8, printed pp. 615--617 (blueprint: lem-trf-de-jong-geometrically-irreducible-tower).

## Main statements

* `exists_deJong_geometricallyIrreducibleTower` states the alteration tower with nodal curve
  fibres over an excellent base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Orgogozo

namespace AlgebraicGeometry

/-- The composite of a finite family of composable scheme morphisms indexed by `Fin n`.
Source: the compositional clause in de Jong, Families of curves and alterations (1997),
Theorem 5.9 (blueprint: lem-trf-de-jong-geometrically-irreducible-tower). -/
def towerComposite : {n : ℕ} → (P : Fin (n + 1) → Scheme.{u}) →
    (q : ∀ j : Fin n, P j.succ ⟶ P j.castSucc) → P ⟨n, Nat.lt_succ_self n⟩ ⟶ P 0
  | 0, P, _ => 𝟙 (P 0)
  | n + 1, P, q =>
      q ⟨n, Nat.lt_succ_self n⟩ ≫
        towerComposite (fun i : Fin (n + 1) ↦ P i.castSucc) (fun j ↦ q j.castSucc)

/-- de Jong's alteration tower for a geometrically irreducible generic fibre.
Source: de Jong, Families of curves and alterations (1997), Theorem 5.9 (i)--(iii),
Situation 5.8, printed pp. 615--617 (blueprint: lem-trf-de-jong-geometrically-irreducible-tower).

Proof plan (the node's eleven steps):

1. Prove the assertion by strong induction on $d\geq1$, uniformly for all the bases in the
   statement. If $d=1$, apply [lem-trf-excellent-base-marked-semistable-curve] to $W\to S$ with
   $Z=\varnothing$. Its square gives $S_1$, $P_1$, $b$, $h$ and the single curve map, with all the
   required fibre clauses. The finite-dimension verification for its excellent Noetherian sources
   is included in Step 11 below. Hence assume $d\geq2$ and the assertion for all positive
   dimensions less than $d$.

2. Put $K=\kappa(\eta_S)$. The integral finite-type scheme $W_K$ has one irreducible component. By
   [lem-pur-finite-inseparable-geometric-reduction] choose a finite purely inseparable extension
   $K'/K$ for which $(W_{K'})_{\mathrm{red}}$ is geometrically reduced. Normalize $S$ in $K'$
   using [lem-weil-pbc-normalization-in-residue-field-extension], obtaining integral $S_0$ with
   function field $K'$. This normalization is finite: for every affine domain $A$ of $S$,
   excellence implies Nagata by [lem-exc-quasi-excellent-nagata]; the prime $0$ in
   [def-weil-pbc-nagata-ring] and [def-weil-pbc-japanese-domain] says exactly that the integral
   closure of $A$ in $K'$ is a finite $A$-module. The finite dominant map $S_0\to S$ is proper by
   [lem-weil-pbc-finite-proper], and its closed image contains the generic point, hence is all of
   $S$.

3. Geometric irreducibility of $W_K$ makes $W_{K'}$ irreducible. In $W\times_S S_0$ take the
   reduced closure $W_0$ of its generic fibre, using
   [lem-weil-pbc-reduced-induced-closed-subscheme]. The generic fibre of $W_0\to S_0$ is
   $(W_{K'})_{\mathrm{red}}$ by [lem-pur-reduction-generic-fibre]; it is geometrically integral:
   after every further field extension, the reduction immersion still has nilpotent defining ideal
   (the rings are Noetherian), hence the same underlying irreducible space as the corresponding
   base change of $W_K$, and Step 2 supplies geometric reducedness. The map $W_0\to W$ is finite:
   affine locally the base change of the finite algebra of $S_0$ is a finite module and its
   quotient is still finite. It is dominant (its generic fibre contains the point over the generic
   point of $W$), hence surjective because it is finite and therefore closed. It is an alteration.
   The morphism $W_0\to S_0$ is proper by base change and closed immersion
   [lem-weil-pbc-proper-fp-permanence]. The finite dominant generic-fibre map to $W_K$ and
   [lem-trf-closed-dominant-dimension] give generic dimension $d$. The schemes $S_0,W_0$ are
   integral excellent Noetherian of finite dimension by Step 11.

4. Apply [lem-trf-geometrically-integral-curve-factorization] to $W_0\to S_0$. Write its proper
   birational modification as $X\to W_0$ and its factorization as $X\xrightarrow{v}Y\to S_0$. Thus
   the generic fibre of $v$ is a geometrically integral curve, and that of $Y\to S_0$ is
   geometrically integral of dimension $r=d-1\geq1$. All these schemes are integral excellent
   Noetherian and of finite dimension. The modification is surjective because its closed image
   contains a dense open. It is finite over that open, so it is an alteration.

5. Apply [lem-trf-excellent-base-marked-semistable-curve] to $v:X\to Y$, with empty boundary.
   Denote its square by $C\to X$ over $B\to Y$ and its curve map by $c:C\to B$. Both horizontal
   maps are alterations, $C$ and $B$ are integral excellent Noetherian, and $c$ is proper flat
   finitely presented with the required geometric curve fibres and smooth geometrically integral
   generic fibre. The composite $B\to S_0$ is proper by [lem-weil-pbc-proper-fp-permanence] and
   dominant. Its generic fibre is integral of dimension $r$: $k(B)/k(Y)$ is finite because $B\to
   Y$ is an alteration, and [lem-sc-closed-irreducible-dimension-trdeg] computes both dimensions
   over $K'$. No geometric irreducibility of this generic fibre is assumed.

6. Apply [lem-sbc-generic-components-split] to $B_{K'}$, giving a finite separable extension
   $L/K'$ over which all components are geometrically irreducible. Normalize $S_0$ in $L$,
   obtaining a finite surjective integral alteration $S_2\to S_0$ by the construction of Step 2.
   Choose a component of $B_L$ dominating $B_{K'}$ and take its reduced closure $B_2$ in
   $B\times_{S_0}S_2$ [lem-weil-pbc-reduced-induced-closed-subscheme]. Such a component exists: a
   prime of the nonzero finite-dimensional $k(B)$-algebra $k(B)\otimes_{K'}L$ gives its generic
   point. There is no smaller prime after localization since this algebra is zero-dimensional, so
   its closure is a component of $B_L$. Consequently $B_2\to B$ is finite dominant (as in Step 3),
   hence an alteration. Its generic fibre over $S_2$ is the chosen reduced component
   [lem-pur-reduction-generic-fibre], geometrically irreducible by the splitting node, and has
   dimension $r$ by [lem-trf-closed-dominant-dimension] on its finite dominant map to $B_{K'}$.
   Properness of $B_2\to S_2$ follows from [lem-weil-pbc-proper-fp-permanence]. Step 11 supplies
   excellence, Noetherianness and finite dimensions.

7. The induction hypothesis now applies to $B_2\to S_2$: its generic dimension is $r=d-1$, not
   $d$, and all its other hypotheses were checked in Step 6. Obtain an alteration $S_1\to S_2$, a
   tower $Q_{d-1}\to\cdots\to Q_0=S_1$ of $d-1$ required curves, and an alteration $Q=Q_{d-1}\to
   B_2$, commuting over $S_2$. The composite $Q\to B$ is proper by
   [lem-weil-pbc-proper-fp-permanence], and surjective because both factors are surjective. It is
   finite over a dense open: if $U\subset B$ makes $B_2|_U\to U$ finite and $V\subset B_2$ makes
   $Q|_V\to V$ finite, remove from $U$ the closed image of $B_2|_U\setminus V$. That image omits
   the generic point because $B_2$ is integral and finite dominant over $B$, whose generic fibre
   is its single generic point. On the remaining dense open both maps are finite, and products of
   their finite module generators prove their composite finite. Thus $Q\to B$ is an alteration.

8. Set $P=C\times_B Q$, with its two projections [def-pc-fibre-product]. The map $q_d:P\to Q$ is
   proper flat and finitely presented by [lem-weil-pbc-proper-fp-permanence],
   [lem-weil-pbc-flat-morphism-base-change] and [lem-weil-pbc-qcqs-morphism-permanence]. For any
   geometric point of $Q$, its fibre is exactly the fibre of $c$ at the composite geometric point
   of $B$, by the fibre-product universal property. Hence it is nonempty connected reduced of pure
   dimension one, with only the stated ordinary double points. In particular the last curve can be
   appended without any claim about vertical components of $W\times_S S_1$.

9. The scheme $P$ is integral. Indeed, $Q\to B$ is dominant, so $P_{k(Q)}$ is obtained by
   extending the ground field of the smooth geometrically integral generic fibre of $c$; it is
   therefore integral and nonempty by [def-pc-geometrically-irreducible]. For an affine open
   $\operatorname{Spec}A\subset Q$ and a nonempty affine open $\operatorname{Spec}D\subset P$
   above it, flatness and [lem-weil-pbc-flat-morphism-affine-criterion] make $D$ flat over the
   domain $A$. Tensoring the injection $A\hookrightarrow\operatorname{Frac}A$ gives an injection
   $D\hookrightarrow D\otimes_A\operatorname{Frac}A$, by [def-weil-pbc-flat-ring-map]. The latter
   ring is the ring of a nonempty affine open of the integral generic fibre: it cannot be zero by
   injectivity. It is a domain, hence so is $D$. Thus $P$ is reduced and every nonempty open meets
   its integral generic fibre. Two nonempty opens then intersect there, so $P$ is irreducible as
   well. This establishes integrality without selecting or normalizing a component, which could
   destroy flatness of the curve map.

10. The projection $P\to C$ is proper and surjective by base change of the alteration $Q\to B$
   [lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-surjective-base-change]. Over the inverse
   image in $C$ of the dense open of $B$ where $Q\to B$ is finite it is finite: affine locally
   tensoring its finite module generators gives finite generators after base change
   [def-weil-finite-integral-morphism]. This inverse image is dense and nonempty since $C$ is
   integral and dominates $B$. Hence $P\to C$ is an alteration. Composing it with $C\to X\to
   W_0\to W$ gives an alteration $h:P\to W$; composing $S_1\to S_2\to S_0\to S$ gives an
   alteration $b:S_1\to S$. For either composite the same dense-open removal argument of Step 7
   applies successively; properness is preserved by [lem-weil-pbc-proper-fp-permanence]. Put
   $P_j=Q_j$ for $j<d$ and $P_d=P$. The defining squares and the fibre-product projections give
   $gh=bq_1\cdots q_d$ exactly.

11. All auxiliary schemes formed by finite morphisms, proper modifications, reduced closed
   subschemes of finite-type schemes, or the final curve base change are of finite type over one
   of the original excellent Noetherian schemes or an induction output. Thus they are excellent by
   the affine finite-type statement [lem-exc-finite-type-localization-excellent], and Noetherian
   by [lem-weil-pbc-finite-type-over-noetherian]. Finite total dimensions follow from
   [lem-trf-closed-dominant-dimension]: a finite dominant map or proper birational modification
   has relative function-field transcendence degree zero, and the proper dominant maps $C\to B$
   and $P\to Q$ have transcendence degree one. In the base case this proves $\dim B=\dim S$ and
   $\dim C=\dim B+1<\infty$; in the induction step $B$ is an alteration of finite-dimensional $Y$,
   $S_2$ is finite over $S_0$, $B_2$ finite over $B$, and $P$ has dimension $\dim Q+1$. The
   intermediate $Q_j$ already have finite dimension by induction. This also justifies every
   earlier application requiring finite dimension. All required clauses now hold.
-/
theorem exists_deJong_geometricallyIrreducibleTower
    (S W : Scheme.{u}) [IsIntegral S] [IsIntegral W]
    [IsLocallyNoetherian S] [CompactSpace S] [IsLocallyNoetherian W] [CompactSpace W]
    (hS : IsExcellentScheme S) (hW : IsExcellentScheme W)
    (hSdim : ∃ n : ℕ, topologicalKrullDim S ≤ (n : WithBot ℕ∞))
    (hWdim : ∃ n : ℕ, topologicalKrullDim W ≤ (n : WithBot ℕ∞))
    (g : W ⟶ S) [IsProper g] [IsDominant g]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (d : ℕ) (hd : 1 ≤ d)
    (hηdim : topologicalKrullDim (g.fiber η) = (d : WithBot ℕ∞))
    (hηirr : GeometricallyIrreducible (g.fiberToSpecResidueField η)) :
    ∃ (P : Fin (d + 1) → Scheme.{u})
      (b : P 0 ⟶ S) (h : P ⟨d, Nat.lt_succ_self d⟩ ⟶ W)
      (q : ∀ j : Fin d, P j.succ ⟶ P j.castSucc),
      (∀ i : Fin (d + 1), IsIntegral (P i) ∧ IsExcellentScheme (P i) ∧
        IsLocallyNoetherian (P i) ∧ CompactSpace (P i) ∧
        ∃ n : ℕ, topologicalKrullDim (P i) ≤ (n : WithBot ℕ∞)) ∧
      IsAlteration b ∧ IsAlteration h ∧
      (∀ j : Fin d, IsProper (q j) ∧ Flat (q j) ∧ LocallyOfFinitePresentation (q j) ∧
        ∀ y : P j.castSucc,
          IsSemistableGeometricCurve
            (pullback.snd (q j) (geometricPoint (P j.castSucc) y))) ∧
      h ≫ g = towerComposite P q ≫ b := by
  sorry

end AlgebraicGeometry
