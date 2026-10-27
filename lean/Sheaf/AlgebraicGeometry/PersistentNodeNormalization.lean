/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.RingTheory.IntegralClosureFinitePi
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource
import Sheaf.AlgebraicGeometry.ProjectiveFiniteGeometricFibres
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import WeilConjectures.AlgebraicGeometry.Descent
import Sheaf.AlgebraicGeometry.FiniteEtaleNormalGenericComponents

/-!
# Normalization at persistent nodes over a trait

Source: Stacks Project, Models Tag 0CDD, Curves Tag 0CBY, and More on Morphisms Tag 0E25.
The global assertion is the explicit persistent/smoothing chart consequence of these tags.
(blueprint: lem-sfb-persistent-node-normalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The reduced closed singular subscheme of the generic fibre.
Source: Stacks Project, Curves Tag 0CBY, and Models Tag 0CDD.
(blueprint: lem-sfb-persistent-node-normalization). -/
noncomputable def persistentGenericSingular {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] {T : Scheme.{u}} (g : T ⟶ S) :
    Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨((pullback.snd f g).smoothLocus : Set (pullback (C := Scheme.{u}) f g))ᶜ,
      (pullback.snd f g).smoothLocus.isOpen.isClosed_compl⟩).subscheme

/-- The reduced singular subscheme of the generic fibre, mapped into the total space.
It is the reduced closed complement of the relative smooth locus in the generic fibre.
Source: Stacks Project, Models Tag 0CDD and Curves Tag 0CBY.
(blueprint: lem-sfb-persistent-node-normalization). -/
noncomputable def persistentGenericSingularMap {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] {T : Scheme.{u}} (g : T ⟶ S) :
    persistentGenericSingular f g ⟶ X :=
  (pullback.snd f g).smoothLocus.closedComplement ≫ pullback.fst f g

/-- The scheme-theoretic closure of the reduced generic singular subscheme.
Source: Stacks Project, Models Tag 0CDD, via scheme-theoretic image (Tag 01R5).
(blueprint: lem-sfb-persistent-node-normalization). -/
noncomputable def persistentNodes {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] {T : Scheme.{u}} (g : T ⟶ S) :
    Scheme.{u} :=
  (persistentGenericSingularMap f g).image

/-- The canonical closed immersion of the persistent-node closure.
Source: Stacks Project, Models Tag 0CDD, via scheme-theoretic image (Tag 01R5).
(blueprint: lem-sfb-persistent-node-normalization). -/
noncomputable def persistentNodesι {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] {T : Scheme.{u}} (g : T ⟶ S) :
    persistentNodes f g ⟶ X :=
  (persistentGenericSingularMap f g).imageι

/-- The inverse image of the persistent-node closure in the componentwise normalization.
Source: Stacks Project, Models Tag 0CDD and More on Morphisms Tag 0E25.
(blueprint: lem-sfb-persistent-node-normalization). -/
noncomputable def persistentBranches {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] {T : Scheme.{u}} (g : T ⟶ S) :
    Scheme.{u} :=
  pullback (C := Scheme.{u}) X.fromReducedNormalization (persistentNodesι f g)

/-- Normalization of a projective nodal trait family separates precisely the persistent
nodes, giving the finite étale double branch cover and the conductor pushout, including
its restriction to every open. Neither excellence nor connectedness is assumed.
`η` is pinned to the fraction-field immersion by `hη`; it is not an arbitrary base map.
The coordinate-ring criterion identifies the image of restriction with all integral
elements in the generic finite algebra. The final stalk clause also records that every
base uniformizer is a uniformizer at every closed point of either finite étale scheme.

Source: Stacks Project, Models Tag 0CDD, Curves Tag 0CBY, More on Morphisms Tag 0E25.
(blueprint: lem-sfb-persistent-node-normalization).

Proof plan (the node's complete chart and descent argument):
1. The DVR $R$ is Noetherian. Thus $X$ is Noetherian, since it is finitely presented and
projective over $S$. Cover its special fibre by the common pointed etale charts of the DVR
local-form node. Their models are $M_0=\operatorname{Spec}R'[u,v]/(uv)$ and
$M_n=\operatorname{Spec}R'[u,v]/(uv-\pi'^n)$, $n\geq0$ in the latter notation (the case $n=0$
there is smooth). Cover the remaining generic-fibre points by the nodal-family charts over etale
extensions of $K$. At a generic singular point the chart parameter must be zero, since
$uv=h\ne0$ is smooth over a field. These are etale covers of the source, not Zariski coordinate
claims about $X$ itself. For every affine $\operatorname{Spec}A\subset X$, flatness makes $A\to
A[1/\pi]$ injective, while the reduced generic fibre makes $A[1/\pi]$ reduced. Hence $X$ is
reduced.
2. First the affine description of componentwise normalization. Let $A$ be a reduced Noetherian
ring with minimal primes $\mathfrak p_1,\dots,\mathfrak p_t$. The irreducible components of
$\operatorname{Spec}A$ are the $V(\mathfrak p_i)$, with reduced induced structures
$\operatorname{Spec}(A/\mathfrak p_i)$, integral with function fields
$K_i=\operatorname{Frac}(A/\mathfrak p_i)$. Let $B_i$ be the integral closure of $A/\mathfrak
p_i$ in $K_i$. Integral closure commutes with localization, so the integral closure of the
structure sheaf in $K_i$ has sections $(B_i)_f$ on $D(f)$ and the normalization of
$\operatorname{Spec}(A/\mathfrak p_i)$ is $\operatorname{Spec}B_i$. Hence
$(\operatorname{Spec}A)^\nu=\coprod_i\operatorname{Spec}B_i=\operatorname{Spec}\prod_iB_i$, with
ring map $a\mapsto(a\bmod\mathfrak p_i)_i$. As $\prod_iA/\mathfrak p_i$ is generated over $A$ by
idempotents, it is integral over $A$, and the finite-product node identifies $\prod_iB_i$ with
the integral closure of $A$ in $\prod_iK_i$. For a normal domain $A$ the normalization is the
identity. Now put $A=R'[u,v]/(uv)$, with minimal primes $(u),(v)$, and $D=R'[u]\times R'[v]$. A
DVR is integrally closed (compare valuations of the terms of a monic equation), so both factors
of $D$ are normal domains by the polynomial-normality node and
$\operatorname{Spec}D\to\operatorname{Spec}A$ is the normalization. The map $A\hookrightarrow D$
identifies $A$ with pairs $(f,g)$ having $f(0)=g(0)$, and $D=A[e]$, $e=(1,0)$, is finite over
$A$. The conductor is $I=(u,v)=uR'[u]\times vR'[v]$, since $(f,g)D\subset A$ exactly when
$f(0)=g(0)=0$. Thus $A/I=R'$, $D/ID=R'\times R'$ and $A=D\times_{R'\times R'}R'$. The branches
are affine lines with origins smooth over $R'$. All of this works over a field as well.
3. An open immersion is etale, so the absolute smooth-pullback (C := Scheme.{u}) node gives
  $\nu^{-1}(V)\cong
V^\nu$ over every open $V\subseteq X$; with step 2 this is the affine description of $C$ in the
statement. Let $X^\circ\subseteq X$ be the open smooth locus of $X\to S$. The same node for
$X^\circ\to S$ gives $(X^\circ)^\nu=X^\circ\times_SS^\nu=X^\circ$, because $R$ is a normal
domain; so $\nu$ is an isomorphism over $X^\circ$, which contains all generic smooth points and
the $uv=1$ charts. In a smoothing chart $R'[u,v]/(uv-\pi'^n)$ with $n\ge1$ the arithmetic-chart
node makes the ring a normal domain, so by step 2 its normalization is the identity. At a
generic node the model is $K'[u,v]/(uv)$ and step 2 over the field $K'$ applies. Componentwise
normalization commutes with the two etale arrows of every common chart by the smooth-pullback
node. Consequently the normalization of $X$ is etale locally either the finite map of step 2 or
the identity. Take a finite collection of affine chart neighbourhoods covering the Noetherian
$X$; it is an fpqc covering. Finiteness descends for this covering, so $\nu:C\to X$ is finite.
This proves finiteness without assuming that $R$ is excellent or Japanese.
4. Compute the closure $N$ on these same charts. On an affine chart its ideal is the kernel of
the map to the generic singular subscheme. Tensoring this kernel with an etale (hence flat)
chart algebra preserves it; localization at $\pi$ also commutes with this tensor product. In the
persistent model the generic singular subscheme has ideal $(u,v)$ and its closure is
$\operatorname{Spec}R'$; the quotient $R'$ has no $\pi$-torsion. In a smoothing or smooth model
the generic singular subscheme is empty and so is its closure. These descriptions also show that
$N\to S$ is smooth by etale source locality and has zero-dimensional fibres; hence it is etale.
They show every geometric fibre of $N$ has finitely many points: it is a closed zero-dimensional
subscheme of a Noetherian geometric curve, with only its finitely many nodes in its support. The
closed immersion $N\hookrightarrow X$ followed by the projective embedding of $X$ is a closed
immersion, so $N\to S$ is projective. The projective-finite-fibres node, with Noetherian target
$S$, makes it finite. Outside $N$ all the normalization charts are identities; fpqc descent of
isomorphisms therefore proves $C\setminus\nu^{-1}N\cong X\setminus N$.
5. The local models of $C$ over the DVR charts are the two smooth branches in step 2 and the
unchanged smoothing charts in step 3. They have flat nodal geometric fibres, and their generic
fibres are smooth. Etale source locality of nodal families and of smoothness gives flatness,
local finite presentation and nodal geometric fibres for $C\to S$, and smoothness for
$C_K\to\operatorname{Spec}K$. Each fibre is nonempty because $\nu$ is surjective: on every chart
it is the identity or $\operatorname{Spec}D\to\operatorname{Spec}A$ of step 2, which is onto
because every prime of $A$ contains $u$ or $v$, and the charts are jointly surjective. A finite
map over the projective $X/S$, with affine Noetherian base $S$, is projective by the
finite-over-projective node (the two projective-space conventions agree here). Thus $C/S$ is
quasi-compact and separated; together with its local finite presentation this gives finite
presentation. Equivalently, on finitely many affine charts the finite type $R$-algebras have
finitely generated presentation ideals because $R$ is Noetherian.
6. Let $B=C\times_XN$. It is closed in $C$, since its defining ideal is the extension of the
ideal of $N$. It is finite over $N$ by finite base change, and finite over $S$ by finite
composition. On every persistent chart the pair $B\to N$ is the two origins
$\operatorname{Spec}(R'\times R')\to\operatorname{Spec}R'$ of step 2. Elsewhere both are empty.
Etale source locality of smoothness shows that $B\to N$ and $B\to S$ are smooth of dimension
zero, hence etale; it also puts $B$ in the relative smooth locus of $C$. The rank-two assertion
descends: on a finite affine etale covering of the finite $N$, the finite module defining $B$ is
free of rank two, and the fpqc module-descent node reflects local freeness of that rank. Thus
$B\to N$ is finite etale of constant degree two. No ordering of the two global branches is
asserted.
7. For the pushout assertion first pull the square back to an affine etale chart $U\to X$. Its
normalization is finite, so all four schemes in this pulled-back square are affine. On the
persistent standard model the ring identity of step 2 is precisely the affine pinching pushout
node, with $A$ there equal to $D$ here, quotient $D\twoheadrightarrow R'\times R'$, and the
diagonal $R'\to R'\times R'$. It persists after the flat etale pullback (C := Scheme.{u}) to $U$:
  tensor the exact
sequence
$$0\to A\to D\oplus R'\xrightarrow{(d,r)\mapsto d|_B-(r,r)}R'\times R'\to0.$$
Its kernel is the same fibre-product ring after tensoring. For a smoothing or smooth chart,
$B=N=\varnothing$ and $C=U$, so the square is the identity pushout. Thus the pulled-back square
on every affine etale chart is a pushout in schemes, for arbitrary target schemes, not merely
affine targets.
8. Fix a scheme $Z$ and compatible maps $C\to Z$, $N\to Z$. Step 7 supplies a unique map $U\to
Z$ on each affine etale chart of $X$. On a double overlap cover by affine etale refinements of
the same charts; step 7 there gives uniqueness, so the two maps agree. Representable fpqc
descent glues these maps uniquely to $X\to Z$, whose restrictions are the supplied maps (check
them after the induced etale covers of $C$ and $N$). This is the universal property of the
pushout. For an arbitrary open $V\subseteq X$, repeat exactly this argument using affine charts
contained in the inverse image of $V$; all ring identities localize. Hence its inverse-image
square is also a pushout. No claim that arbitrary nonflat base change preserves pushouts is
used.
9. The generic square has $N_K$ as its reduced singular subscheme and, by the field version of
step 2 and the unchanged smooth charts, $C_K$ is the normalization of $X_K$. Its conductor ideal
is $(u,v)$ at every split node and the unit ideal elsewhere. After an etale extension these are
exactly the quotient and double-branch ideals already computed; flatness reflects the equality
of these ideals. Thus this is the normalization and conductor square, including nonsplit nodes.
For the last determination assertion apply the finite-etale-generic-components node to $N\to S$
and $B\to S$: $S$ is normal integral Noetherian. Their coordinate rings are precisely the
products of the integral closures of $R$ in their generic field factors. Any generic morphism
between these finite algebras preserves integral elements, so the generic map $B_K\to N_K$
extends uniquely to $B\to N$. This proves the asserted determination of both schemes and their
map.
10. A finite $R$-algebra is semilocal, since its maximal ideals lie over the maximal ideal of
$R$ and correspond to the finitely many maximal ideals of its finite-dimensional residue
algebra. The component decomposition just cited makes the local rings of nonempty $N$ and $B$
domains. Since their special fibres are finite etale over $k$, their localization at a closed
point has quotient modulo $\pi$ a field. Its maximal ideal is therefore generated by $\pi$.
Flatness makes $\pi$ nonzero and a nonzerodivisor. These local rings are Noetherian, so the DVR
equivalence in the definition applies. Hence they are regular one-dimensional local rings with
the same uniformizer as $R$. Their generic local rings are fields; this proves regularity of the
schemes and dimension one. If $N_K$ is empty then all persistent charts are absent,
$N=B=\varnothing$ and $C=X$; all arguments above, including the pushout and the degree-two
convention over the empty base, still apply.
-/
theorem persistent_node_normalization
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (η : Spec (.of K) ⟶ Spec (.of R))
    (hη : η = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R))
    [IsHProjective f] [Flat f] [LocallyOfFinitePresentation f]
    (hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of R)),
    Nonempty (pullback (C := Scheme.{u}) f g) ∧ IsReduced (pullback (C := Scheme.{u}) f g) ∧
      (pullback (C := Scheme.{u}) f g).IsPureDimension 1 ∧
      ∀ x : pullback (C := Scheme.{u}) f g, x ∉ (pullback.snd f g).smoothLocus →
        Nonempty (AdicCompletion
          (IsLocalRing.maximalIdeal ((pullback (C := Scheme.{u}) f g).presheaf.stalk x))
          ((pullback (C := Scheme.{u}) f g).presheaf.stalk x) ≃+*
            (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span
              {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) * (MvPowerSeries.X (1 : Fin 2) :
                MvPowerSeries (Fin 2) Ω)}))) :
    IsReduced X ∧
    IsFinite (persistentNodesι f η ≫ f) ∧ Etale (persistentNodesι f η ≫ f) ∧
    IsFinite X.fromReducedNormalization ∧ IsHProjective (X.fromReducedNormalization ≫ f) ∧ Flat
      (X.fromReducedNormalization ≫ f) ∧
    ∃ hfp : LocallyOfFinitePresentation (X.fromReducedNormalization ≫ f),
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of R)),
    Nonempty (pullback (C := Scheme.{u}) (X.fromReducedNormalization ≫ f) g) ∧ IsReduced (pullback
      (X.fromReducedNormalization ≫ f) g) ∧
      (pullback (C := Scheme.{u}) (X.fromReducedNormalization ≫ f) g).IsPureDimension 1 ∧
      ∀ x : pullback (C := Scheme.{u}) (X.fromReducedNormalization ≫ f) g, x ∉ (pullback.snd
        (X.fromReducedNormalization ≫ f) g).smoothLocus →
        Nonempty (AdicCompletion
          (IsLocalRing.maximalIdeal ((pullback (C := Scheme.{u}) (X.fromReducedNormalization ≫ f)
            g).presheaf.stalk
            x))
          ((pullback (C := Scheme.{u}) (X.fromReducedNormalization ≫ f) g).presheaf.stalk x) ≃+*
            (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span
              {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) * (MvPowerSeries.X (1 : Fin 2) :
                MvPowerSeries (Fin 2) Ω)}))) ∧
      Smooth (pullback.snd (X.fromReducedNormalization ≫ f) η) ∧
      (∀ U : X.Opens, Disjoint (U : Set X) (Set.range (persistentNodesι f η)) →
        IsIso (pullback.snd X.fromReducedNormalization U.ι)) ∧
      IsClosedImmersion (pullback.fst X.fromReducedNormalization (persistentNodesι f η)) ∧
      (∀ z : persistentBranches f η, pullback.fst X.fromReducedNormalization (persistentNodesι f
        η) z ∈
        (@Scheme.Hom.smoothLocus _ _ (X.fromReducedNormalization ≫ f) hfp :
          X.reducedNormalization.Opens)) ∧
      IsFinite (pullback.fst X.fromReducedNormalization (persistentNodesι f η) ≫
        X.fromReducedNormalization ≫ f) ∧ Etale (pullback.fst X.fromReducedNormalization
        (persistentNodesι f η) ≫ X.fromReducedNormalization ≫ f) ∧
      IsFinite (pullback.snd X.fromReducedNormalization (persistentNodesι f η)) ∧ Etale
        (pullback.snd X.fromReducedNormalization (persistentNodesι f η)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (g : Spec (.of Ω) ⟶ persistentNodes f η),
        Nat.card (pullback (C := Scheme.{u}) (pullback.snd X.fromReducedNormalization
          (persistentNodesι f η)) g) =
          2) ∧
      IsPushout (pullback.fst X.fromReducedNormalization (persistentNodesι f η)) (pullback.snd
        X.fromReducedNormalization (persistentNodesι f η)) X.fromReducedNormalization
        (persistentNodesι f η) ∧
      (∀ (V : Scheme.{u}) (j : V ⟶ X) [IsOpenImmersion j]
        (a : pullback (C := Scheme.{u}) (pullback.fst X.fromReducedNormalization (persistentNodesι
          f η) ≫
          X.fromReducedNormalization) j ⟶ pullback (C := Scheme.{u}) X.fromReducedNormalization j)
        (c : pullback (C := Scheme.{u}) (pullback.fst X.fromReducedNormalization (persistentNodesι
          f η) ≫
          X.fromReducedNormalization) j ⟶ pullback (C := Scheme.{u}) (persistentNodesι f η) j),
        a ≫ pullback.fst X.fromReducedNormalization j =
          pullback.fst (pullback.fst X.fromReducedNormalization (persistentNodesι f η) ≫
            X.fromReducedNormalization) j ≫ pullback.fst X.fromReducedNormalization
            (persistentNodesι f η) →
        a ≫ pullback.snd X.fromReducedNormalization j = pullback.snd (pullback.fst
          X.fromReducedNormalization (persistentNodesι f η) ≫ X.fromReducedNormalization) j →
        c ≫ pullback.fst (persistentNodesι f η) j =
          pullback.fst (pullback.fst X.fromReducedNormalization (persistentNodesι f η) ≫
            X.fromReducedNormalization) j ≫ pullback.snd X.fromReducedNormalization
            (persistentNodesι f η) →
        c ≫ pullback.snd (persistentNodesι f η) j = pullback.snd (pullback.fst
          X.fromReducedNormalization (persistentNodesι f η) ≫ X.fromReducedNormalization) j →
        IsPushout a c (pullback.snd X.fromReducedNormalization j) (pullback.snd (persistentNodesι
          f η) j)) ∧
      (Function.Injective (pullback.fst (persistentNodesι f η ≫ f) η).appTop.hom ∧
        ∀ z : Γ(pullback (C := Scheme.{u}) (persistentNodesι f η ≫ f) η, ⊤),
          (((pullback.snd (persistentNodesι f η ≫ f) η ≫ η).appTop).hom.comp (Scheme.ΓSpecIso (.of
            R)).inv.hom).IsIntegralElem z ↔
            ∃ a : Γ(persistentNodes f η, ⊤), (pullback.fst (persistentNodesι f η ≫ f)
              η).appTop.hom a = z) ∧
      (IsRegularScheme (persistentNodes f η) ∧
        (closedPoints (persistentNodes f η)).Finite ∧
        (Nonempty (persistentNodes f η) → topologicalKrullDim (persistentNodes f η) = 1) ∧
        ∀ x : persistentNodes f η, IsClosed ({x} : Set (persistentNodes f η)) →
          ∃ hd : IsDomain ((persistentNodes f η).presheaf.stalk x),
            @IsDiscreteValuationRing ((persistentNodes f η).presheaf.stalk x) _ hd ∧
            ∀ π : R, Irreducible π →
              IsLocalRing.maximalIdeal ((persistentNodes f η).presheaf.stalk x) =
                Ideal.span {((persistentNodes f η).presheaf.Γgerm x).hom.comp ((persistentNodesι f
                  η ≫ f).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) π}) ∧
      (Function.Injective (pullback.fst (pullback.fst X.fromReducedNormalization (persistentNodesι
        f η) ≫ X.fromReducedNormalization ≫ f) η).appTop.hom ∧
        ∀ z : Γ(pullback (C := Scheme.{u}) (pullback.fst X.fromReducedNormalization
          (persistentNodesι f η) ≫
          X.fromReducedNormalization ≫ f) η, ⊤),
          (((pullback.snd (pullback.fst X.fromReducedNormalization (persistentNodesι f η) ≫
            X.fromReducedNormalization ≫ f) η ≫ η).appTop).hom.comp (Scheme.ΓSpecIso (.of
            R)).inv.hom).IsIntegralElem z ↔
            ∃ a : Γ(persistentBranches f η, ⊤), (pullback.fst (pullback.fst
              X.fromReducedNormalization (persistentNodesι f η) ≫ X.fromReducedNormalization ≫ f)
              η).appTop.hom a = z) ∧
      (IsRegularScheme (persistentBranches f η) ∧
        (closedPoints (persistentBranches f η)).Finite ∧
        (Nonempty (persistentBranches f η) → topologicalKrullDim (persistentBranches f η) = 1) ∧
        ∀ x : persistentBranches f η, IsClosed ({x} : Set (persistentBranches f η)) →
          ∃ hd : IsDomain ((persistentBranches f η).presheaf.stalk x),
            @IsDiscreteValuationRing ((persistentBranches f η).presheaf.stalk x) _ hd ∧
            ∀ π : R, Irreducible π →
              IsLocalRing.maximalIdeal ((persistentBranches f η).presheaf.stalk x) =
                Ideal.span {((persistentBranches f η).presheaf.Γgerm x).hom.comp ((pullback.fst
                  X.fromReducedNormalization (persistentNodesι f η) ≫ X.fromReducedNormalization ≫
                  f).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) π}) ∧
      (∀ ψ : persistentBranches f η ⟶ persistentNodes f η,
        ψ ≫ (persistentNodesι f η ≫ f) = pullback.fst X.fromReducedNormalization (persistentNodesι
          f η) ≫ X.fromReducedNormalization ≫ f →
        pullback.fst (pullback.fst X.fromReducedNormalization (persistentNodesι f η) ≫
          X.fromReducedNormalization ≫ f) η ≫ ψ =
          pullback.fst (pullback.fst X.fromReducedNormalization (persistentNodesι f η) ≫
            X.fromReducedNormalization ≫ f) η ≫ pullback.snd X.fromReducedNormalization
            (persistentNodesι f η) →
        ψ = pullback.snd X.fromReducedNormalization (persistentNodesι f η)) ∧
      (∃ e : pullback (C := Scheme.{u}) (X.fromReducedNormalization ≫ f) η ≅ (pullback (C :=
        Scheme.{u}) f η).reducedNormalization,
        e.hom ≫ (pullback (C := Scheme.{u}) f η).fromReducedNormalization ≫ pullback.fst f η =
          pullback.fst (X.fromReducedNormalization ≫ f) η ≫ X.fromReducedNormalization ∧
        e.hom ≫ (pullback (C := Scheme.{u}) f η).fromReducedNormalization ≫ pullback.snd f η =
          pullback.snd (X.fromReducedNormalization ≫ f) η) ∧
      (∃ e : pullback (C := Scheme.{u}) (persistentNodesι f η ≫ f) η ≅ persistentGenericSingular f
        η,
        e.hom ≫ persistentGenericSingularMap f η = pullback.fst (persistentNodesι f η ≫ f) η ≫
          persistentNodesι f η ∧
        e.hom ≫ (pullback.snd f η).smoothLocus.closedComplement ≫ pullback.snd f η =
          pullback.snd (persistentNodesι f η ≫ f) η) ∧
      (∀ U : (pullback (C := Scheme.{u}) f η).affineOpens, ∀ a : Γ(pullback (C := Scheme.{u}) f η,
        U.1),
        a ∈ ((pullback.snd f η).smoothLocus.closedComplement).ker.ideal U ↔
          ∀ z : Γ((pullback (C := Scheme.{u}) f η).reducedNormalization,
            (pullback (C := Scheme.{u}) f η).fromReducedNormalization ⁻¹ᵁ U.1),
            ∃ c : Γ(pullback (C := Scheme.{u}) f η, U.1),
              ((pullback (C := Scheme.{u}) f η).fromReducedNormalization.app U.1).hom c =
                ((pullback (C := Scheme.{u}) f η).fromReducedNormalization.app U.1).hom a * z) := by
  sorry

end AlgebraicGeometry
