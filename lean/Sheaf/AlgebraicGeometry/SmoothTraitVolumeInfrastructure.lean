/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Sober
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.AffineSchematicDensityCriterion
import Sheaf.AlgebraicGeometry.PrincipalOpenDenseOfNonZeroDivisor
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import WeilConjectures.AlgebraicGeometry.RationalFunctionsGenericStalks
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.TFAE
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTopInvertible
import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-! # Local geometry and volume forms of smooth trait schemes

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §4.3, printed p.104, and §2.2,
Proposition 5; supporting Stacks Tags 00PD, 0AFS, 07NF, 01T6, 01RE, 0HA1, 02G1 and 033M.
(blueprint: lem-sfb-smooth-trait-volume-infrastructure)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A smooth finite-type trait scheme is Noetherian and regular with normal local domains.
Its generic fibre is a quasi-compact schematically dense open; its special fibre is reduced
with finitely many disjoint clopen irreducible components. At their generic points the ambient
stalk is a DVR with the base uniformizer. A nonempty pure-dimensional generic fibre fixes the
rank of the differential sheaf and makes its top exterior power invertible.

The fraction field is the canonical `FractionRing R`; the special fibre is the canonical
scheme-theoretic fibre at the closed point. Injectivity on every open is precisely the
injection of structure sheaves into the direct image from the generic fibre. The existential
`hdom` supplies the proof argument of the DVR class, without assuming any stalk property.

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §4.3, printed p.104, and §2.2,
Proposition 5; Stacks Tags 00PD, 0AFS, 07NF, 01T6, 01RE, 0HA1, 02G1 and 033M.
(blueprint: lem-sfb-smooth-trait-volume-infrastructure)

Proof plan from the reviewed DAG:

1. Every ideal of $R$ is principal, hence finitely generated, so $R$ is Noetherian. By
   [lem-sc-dvr-dimension-one] its dimension is one; its maximal ideal $(\pi)$ therefore makes it
   regular local by [def-weil-regular-scheme]. By [lem-weil-pbc-regular-local-localization], $R$
   is a regular ring. A nonzero prime properly below $(\pi)$ would give a prime chain of length
   two, so the primes of $R$ are $(0)$ and $(\pi)$. Every nonzero denominator is a unit times a
   power of $\pi$ by [lem-weil-pbc-dvr-unit-times-uniformizer-power], whence $R[1/\pi]=E$. By
   [lem-weil-pbc-principal-localization-open-immersion], $\operatorname{Spec}E=D(\pi)\subset T$.
   An open of $T$ containing its closed point is all of $T$ (a basic open containing that point is
   defined by a unit); thus every nonempty affine open of $T$ is either $T$ or
   $\operatorname{Spec}E$. Their coordinate rings are regular, the field case following
   immediately from the dimension-zero definition.

2. The affine scheme $T$ is quasi-compact by [lem-weil-pbc-affine-scheme-qcqs] and locally
   Noetherian by its single Noetherian affine chart [pqf-def-locnoeth]. Apply
   [lem-weil-pbc-finite-type-over-noetherian] to $f$ to obtain that $Z$ is Noetherian. The
   affine-local description in [def-sbc-smooth-morphisms] gives a covering by
   $W=\operatorname{Spec}B$ mapping to nonempty affine opens $V=\operatorname{Spec}A$ of $T$, with
   $A\to B$ smooth. Step 1 makes $A$ regular, so [lem-weil-pbc-regular-ring-smooth-ascent] makes
   $B$ regular. These charts prove that $Z$ is regular. By [rem-pc-regular-normal](1), every local
   ring of $Z$ is an integrally closed domain.

3. By [lem-pc-smooth-flat], $f$ is flat. Step 1 and [lem-weil-pbc-open-preimage-fibre-product]
   identify $Z_E$ with the open $f^{-1}D(\pi)$; on each smooth affine chart
   $W=\operatorname{Spec}B$ of Step 2 it is $D(\pi_B)$ by [lem-weil-pbc-basic-open-pullback]. If
   the chart maps into $\operatorname{Spec}E$, then $\pi_B$ is a unit. Otherwise its base ring is
   $R$, and $B$ is flat over $R$ by [lem-weil-pbc-smooth-ring-map-flat]. Apply
   [lem-trf-flat-tensor-preserves-injection] to multiplication by the nonzero $\pi$ on $R$: after
   tensoring with $B$ it is multiplication by $\pi_B$, hence this multiplication is injective.
   With $n=1$, [lem-trf-affine-schematic-density-criterion] now gives the sheaf injection on $W$.
   These injections on an open covering give $\mathcal O_Z\to j_*\mathcal O_{Z_E}$ injective.
   Moreover [lem-pc-principal-open-dense-of-nonzerodivisor] on the same charts gives topological
   density of $Z_E$ in $Z$.

4. Apply [lem-weil-pbc-noetherian-open-subscheme-noetherian] to the open $Z_E\subset Z$ of Step 3
   and the Noetherian scheme of Step 2. It makes $Z_E$ Noetherian and in particular quasi-compact.
   This also covers the empty open.

5. By [sbc-lem-smooth-criterion], both residue-field fibres of $f$ are smooth over their fields.
   They are of finite type by [lem-sfb-finite-type-composition-base-change], hence Noetherian by
   [lem-weil-pbc-finite-type-over-noetherian] (fields are Noetherian and their one-point spectra
   are quasi-compact). By [lem-trf-smooth-geometrically-normal], $Z_k$ is reduced and normal.
   Apply [rem-pc-regular-normal](2), whose hypothesis is Noetherianity and normality, to $Z_k$. It
   gives finitely many pairwise disjoint open-and-closed irreducible components, each with its
   open subscheme structure normal and integral. For $Z_k=\varnothing$ the component assertions
   are vacuous.

6. Let $C$ be one of the nonempty components from Step 5 and $\zeta$ its generic point, which
   exists by [lem-sc-scheme-sober]. Since $C$ is integral and open in $Z_k$,
   [lem-sc-rational-functions-generic-stalks] makes $\mathcal O_{Z_k,\zeta}=\mathcal O_{C,\zeta}$
   a field. Put $B=\mathcal O_{Z,\zeta}$. By [lem-sbc-scheme-fibre-stalk-quotient], $B/\pi
   B\cong\mathcal O_{Z_k,\zeta}$, so $\pi B$ is the maximal ideal of the local ring $B$. The base
   stalk at the closed point is $R_{(\pi)}=R$ by [lem-weil-pbc-affine-open-stalk-localization],
   since elements outside $(\pi)$ are units. Flatness of $f$ means that $B$ is flat over this $R$
   [def-weil-flat-morphism]. Tensoring the injection $R\xrightarrow{\pi}R$ with $B$ using
   [lem-trf-flat-tensor-preserves-injection] makes multiplication by $\pi$ injective on $B$. Since
   $B$ is a nonzero local domain by Step 2, its element $\pi$ is nonzero. The ring $B$ is
   Noetherian by regularity. Apply [lem-sc-principal-ideal-dvr]: $B$ is a DVR, and $\pi
   B=\mathfrak m_B$ says exactly that the image of $\pi$ is its uniformizer.

7. Assume now $Z_E\ne\varnothing$ and that all its irreducible components have dimension $d$. By
   [lem-sbc-equidimensional-open-local-dimension], applied over $E$ with $O=Z_E$, its local
   topological dimension at every point is $d$. Set $\mathcal M=\Omega^1_{Z/R}$. It is finite
   locally free by [lem-ag-smooth-relative-differentials-finite-locally-free]. Fix any $z\in Z$
   and a nonempty trivializing neighbourhood $W$ on which $\mathcal M$ has some finite rank $r$.
   Density from Step 3 gives $y\in W\cap Z_E$. Apply
   [lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension] to $f$ at $y$: it gives an affine
   neighbourhood on which the differential module is free of rank $\dim_y Z_E=d$. By
   [def-sc-relative-differential-sheaf], this is a trivialization of the same sheaf $\mathcal M$.
   Taking its stalk at $y$ and tensoring with $\kappa(y)$, the two trivializations give an
   isomorphism $\kappa(y)^r\cong\kappa(y)^d$, hence $r=d$. Thus all these neighbourhoods have rank
   $d$, which proves constant rank on all of $Z$, including points of the special fibre.

8. Apply [lem-sc-exterior-sheaf-top-invertible] to $\mathcal M$ of constant rank $d$ from Step 7.
   Its top exterior power $\Omega^d_{Z/R}=\bigwedge^d\mathcal M$ is locally isomorphic to
   $\mathcal O_Z$. It is quasi-coherent directly by [pqf-def-coherent]: on an affine open
   $\operatorname{Spec}A$ refining such a trivialization it is the sheaf associated with the
   module $A$. Thus it is invertible in [def-sc-invertible-module]. For $d=0$,
   [def-sc-sheaf-exterior-power] identifies it with $\mathcal O_Z$, so this case is included.
-/
theorem smooth_trait_volume_infrastructure
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (_hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of R))
    [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsNoetherian Z ∧ IsRegularScheme Z ∧
      (∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧ IsIntegrallyClosed (Z.presheaf.stalk z)) ∧
      IsOpenImmersion
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) ∧
      CompactSpace
        ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) ∧
      (∀ U : Z.Opens, Function.Injective
        ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).app U)) ∧
      IsReduced (f.fiber (IsLocalRing.closedPoint R)) ∧
      (irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))).Finite ∧
      (∀ C : Set (f.fiber (IsLocalRing.closedPoint R)),
        C ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)) → IsClopen C) ∧
      (∀ C D : Set (f.fiber (IsLocalRing.closedPoint R)),
        C ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)) →
        D ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)) →
        C ≠ D → Disjoint C D) ∧
      (∀ (C : Set (f.fiber (IsLocalRing.closedPoint R)))
        (ζ : f.fiber (IsLocalRing.closedPoint R)),
        C ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)) →
        IsGenericPoint ζ C →
        ∃ hdom : IsDomain (Z.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) ζ)),
          @IsDiscreteValuationRing
            (Z.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) ζ)) _ hdom ∧
          IsLocalRing.maximalIdeal
            (Z.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) ζ)) =
            Ideal.span { (Z.presheaf.germ ⊤ (f.fiberι (IsLocalRing.closedPoint R) ζ)
              trivial).hom (f.appTop ((Scheme.ΓSpecIso (.of R)).inv π)) }) ∧
      (∀ d : ℕ,
        Nonempty ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) →
        (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap R (FractionRing R))))).IsPureDimension d →
        SheafOfModules.IsFiniteLocallyFreeOfRank f.relativeDifferentials d ∧
          (Scheme.Modules.exteriorSheaf f.relativeDifferentials d).IsInvertible) := by
  sorry

end AlgebraicGeometry
