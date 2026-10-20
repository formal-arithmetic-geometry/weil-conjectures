/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveNodalTower
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.JapaneseDomain
import Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import Mathlib.RingTheory.Localization.Integral
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ProperDimZeroFiniteOverField
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ComponentsFiniteSeparableDescent
import WeilConjectures.AlgebraicGeometry.SubsetGeometricIrreducibility
import Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import WeilConjectures.AlgebraicGeometry.ProperBasic
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Sheaf.AlgebraicGeometry.AlterationRelativeCurvePreparation
import Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution
import Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction
import Sheaf.SixFunctors.TraceFormula.ProjectiveNodalFamilyGeometry

/-!
# Plurinodal alteration over a trait and smooth alteration over a field

Source: Lu--Zheng, Duality and nearby cycles over general bases, proof of Theorem 5.1,
pp. 42--43 (Orgogozo Lemma 4.7 and de Jong alterations); ILO, Travaux de Gabber,
Exposé IX, Theorem 1.2, p. 131, and Exposé X, Theorem 3.5, Steps 2 and 5,
pp. 162--164; Exposé X, Lemma 2.2, pp. 149--150.
(blueprint: lem-trf-plurinodal-alteration)

The trait clause quantifies over every dominating component of the reduced base change.
Its map lands in the canonical reduced closed subscheme of that component. A geometric
generic point is allowed to have any separably closed field, and is extended compatibly;
in particular purely inseparable trait changes have not been excluded.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Plurinodal alteration over an excellent strictly henselian equal-characteristic trait.
Source: Lu--Zheng, proof of Theorem 5.1, pp. 42--43; ILO, Exposé IX, Theorem 1.2,
p. 131, and Exposé X, Theorem 3.5, Steps 2 and 5, pp. 162--164.
(blueprint: lem-trf-plurinodal-alteration)

Proof plan (the node's twelve steps, shared with the field clause below):
1. For a finite fraction-field extension, normalize the excellent DVR. Nagata finiteness
   gives a finite algebra; the integral closure is normal Noetherian of dimension one.
   Use lem-exc-quasi-excellent-nagata, def-weil-pbc-nagata-ring,
   def-weil-pbc-japanese-domain, lem-sc-integral-closure-dedekind-surjective-fibres,
   and lem-weil-pbc-integral-closure-finite-extension-normal.
2. Henselian finite-algebra decomposition has one factor since the closure is a domain.
   Its residue field is the original algebraically closed field; normal dimension one
   makes it a DVR. It is excellent. Composita give common finite changes, and extending
   the chosen geometric field gives compatible geometric generic points. Use
   lem-weil-pbc-finite-over-henselian-local-product, lem-sc-normal-dim1-dvr, and
   lem-exc-finite-type-localization-excellent.
3. Flatness embeds affine coordinate rings into their generic-fibre rings, so a flat
   scheme over an integral base with integral generic fibre is integral. Nonempty charts
   meet the generic fibre and each other. Repeat after field extensions to establish
   geometric integrality for towers. Use lem-weil-pbc-flat-morphism-affine-criterion
   and def-weil-pbc-flat-ring-map.
4. Induct on generic dimension for an auxiliary integral proper W over the trait.
   Dimension zero gives Spec L for a finite extension; normalize the trait in L and
   extend its generic map by the proper valuative criterion. This is the length-zero
   tower. Use lem-kun-dimension-finite-type, lem-pc-dim-zero-finite-over-field,
   lemma-nagata-proper-valuative-criterion-existence-api,
   lem-weil-pbc-proper-to-separated and lem-weil-pbc-finite-proper.
5. In positive dimension use lem-trf-alteration-relative-curve-preparation, then
   lem-trf-relative-marked-nodal-reduction over its projective base. Apply induction to
   the altered base, whose generic dimension is one lower by
   lem-sc-closed-irreducible-dimension-trdeg. Use lem-weil-pbc-proper-composition.
6. Pull the nodal curve back to the tower from induction and append it. Step 3 proves
   integrality and geometric generic integrality; the generic field extension stays
   finite. Use lem-trf-projective-nodal-family-geometry,
   lem-trf-relative-marked-nodal-reduction, lem-weil-pbc-proper-base-change and
   lem-weil-pbc-proper-composition.
7. Stabilize all generic components after one finite separable extension using
   lem-sbc-components-finite-separable-descent and
   lem-sbc-subset-geometric-irreducibility. Make their reductions geometrically reduced
   after a finite inseparable extension using lem-pur-finite-inseparable-geometric-reduction.
   They are geometrically integral. Finiteness of the component set uses
   lem-weil-pbc-finite-type-algebra-noetherian and lem-weil-pbc-noetherian-finite-components.
8. Apply the auxiliary assertion to each reduced closure. Choose a common finite trait
   extension and pull back all towers. Their integral sources map into the unique
   dominating components of these base changes, exhausting every dominating component.
   Use lem-weil-pbc-closed-immersion-proper, lem-weil-pbc-proper-base-change,
   lem-weil-pbc-proper-composition, and lem-trf-projective-nodal-family-geometry.
9. Use lem-weil-pbc-generic-finite-morphism-open-neighborhood to turn finite generic
   field extensions into finiteness over dense opens; pqf-lem-proper-basic supplies
   quasi-compactness and quasi-separatedness. The nodal-family geometry gives the open
   smooth locus and closed nonsmooth support with finite fibres. Its reduced closed
   subscheme is proper by lem-pc-projective-proper and
   lem-weil-pbc-closed-immersion-proper, hence finite by
   thm-pqf-finite-iff-proper-finite-fibres. No degree is inverted.
10. For the field clause induct separately on dimension with a nowhere dense boundary,
    requiring its inverse image to lie in a strict normal crossings divisor. In dimension
    zero the finite extension of the algebraically closed field is trivial. Use
    lem-pc-dim-zero-finite-over-field and lem-kun-dimension-finite-type.
11. Apply curve preparation and marked nodal reduction. The inverse boundary is nowhere
    dense by dominance and integrality. Apply the pair induction to the lower-dimensional
    base and its bad closed subset. Use lem-trf-alteration-relative-curve-preparation,
    lem-trf-relative-marked-nodal-reduction and lem-sc-closed-irreducible-dimension-trdeg.
12. Pull back the nodal curve to the smooth altered base. Step 3 proves integrality.
    Pull back the finite etale smooth-locus boundary as a Cartier divisor using
    def-pc-relative-effective-cartier, lem-pc-recd-pullback, and
    lem-weil-pbc-etale-scheme-base-change. Apply lem-trf-nodal-pair-projective-resolution.
    The resulting smooth scheme is proper over the field and its composite alteration is
    dominant with finite generic field extension. Take empty boundary and use Step 9.
    Properness uses lem-weil-pbc-proper-base-change and lem-weil-pbc-proper-composition.
-/
theorem exists_plurinodal_alteration
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsStrictlyHenselianLocalRing R] [CharP R p]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (hexc : IsExcellent R)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
    (hη : Function.Injective (algebraMap R Ω))
    (X : Scheme.{u}) [IsIntegral X] (f : X ⟶ Spec (.of R))
    [IsProper f] [IsDominant f] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (_ : Algebra R R'), Module.Finite R R' ∧ Function.Injective (algebraMap R R') ∧
      (∃ (Ω' : Type u) (_ : Field Ω') (_ : IsSepClosed Ω')
        (j : Ω →+* Ω') (j' : R' →+* Ω'),
        j'.comp (algebraMap R R') = j.comp (algebraMap R Ω) ∧ Function.Injective j') ∧
      ∀ Z : Closeds ↥((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))).nilradical.subscheme),
        (Z : Set _) ∈ irreducibleComponents
          ↥((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R')))).nilradical.subscheme) →
        Dense ((Scheme.IdealSheafData.subschemeι
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R')))).nilradical ≫
            pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) '' (Z : Set _)) →
        ∃ (P : Scheme.{u}) (a : P ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)
          (t : P ⟶ Spec (.of R')),
          IsProjectiveNodalTower t ∧ IsProper a ∧ IsDominant a ∧
          (∃ U : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Opens,
            Dense (U : Set ↥((Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) ∧
              IsFinite (a ∣_ U)) ∧
          a ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R')))).nilradical.subschemeι ≫
              pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = t := by
  sorry

/-- Smooth proper alteration over an algebraically closed field of positive characteristic.
Source: Lu--Zheng, proof of Theorem 5.1, pp. 42--43 (de Jong smooth alteration);
ILO, Exposé X, Lemma 2.2, pp. 149--150, and Theorem 3.5, pp. 162--164.
(blueprint: lem-trf-plurinodal-alteration)

Proof: use Steps 10--12 of the twelve-step proof plan in
`exists_plurinodal_alteration`: induct on dimension for the stronger assertion for pairs
with nowhere dense boundary; prepare a relative curve, perform marked nodal reduction,
alter the lower-dimensional base by induction, and resolve the resulting nodal pair.
Steps 3 and 6 give integrality and finite generic field extension. Step 9 converts the
latter to finiteness over a dense open. With empty boundary the resulting smooth source
is proper over the field and the composite is proper and dominant. No prime-to-p degree
condition occurs. The dimension-zero case is the identity of Spec F.
-/
theorem exists_smooth_proper_alteration
    (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [IsAlgClosed F] [CharP F p]
    (X : Scheme.{u}) [IsIntegral X] (f : X ⟶ Spec (.of F))
    [IsProper f] :
    ∃ (P : Scheme.{u}) (g : P ⟶ Spec (.of F)) (a : P ⟶ X),
      Smooth g ∧ IsProper g ∧ IsProper a ∧ IsDominant a ∧ a ≫ f = g ∧
      ∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (a ∣_ U) := by
  sorry

end AlgebraicGeometry
