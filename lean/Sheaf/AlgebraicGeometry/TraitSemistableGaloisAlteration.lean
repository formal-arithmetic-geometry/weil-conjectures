/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.NormalScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.MvPolynomial.CommRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective

import Sheaf.AlgebraicGeometry.FiniteOverProjective
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.ProperDimZeroFiniteOverField
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.LogSmoothLogRegular
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Semistable Galois alteration over a complete trait

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XVI, §3.7,
printed p.254; Exposé X, Lemma 2.5 and proof, p.153; VI 1.4 and 1.8, pp.69--70
(blueprint: lem-per-trait-semistable-galois-alteration).

The chart algebra is the actual quotient by the semistable equation. The log
structures are identified with the canonical divisorial presheaves by isomorphisms
compatible with their structural inclusions. The generic torsor action is the
restriction of the same global finite group action.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The equation of a semistable trait chart, with `r ≤ n` identifying the first `r`
coordinates among all `n` coordinates. Source: ILO XVI 3.7, X 2.5
(blueprint: lem-per-trait-semistable-galois-alteration). -/
noncomputable def traitSemistableEquation (A : CommRingCat.{u}) (π : A)
    (n r : ℕ) (hrn : r ≤ n) : MvPolynomial (ULift.{u} (Fin n)) A :=
  (∏ i : Fin r, MvPolynomial.X (ULift.up (Fin.castLE hrn i))) - MvPolynomial.C π

/-- The actual algebra `A[t₁,…,tₙ]/(t₁⋯tᵣ-π)`. Source: ILO XVI 3.7, X 2.5
(blueprint: lem-per-trait-semistable-galois-alteration). -/
noncomputable def traitSemistableChartAlgebra (A : CommRingCat.{u}) (π : A)
    (n r : ℕ) (hrn : r ≤ n) : CommRingCat.{u} :=
  .of (MvPolynomial (ULift.{u} (Fin n)) A ⧸
    Ideal.span {traitSemistableEquation A π n r hrn})

/-- The structural projection of the standard semistable chart, induced by constants
and the quotient map. Source: ILO XVI 3.7, X 2.5
(blueprint: lem-per-trait-semistable-galois-alteration). -/
noncomputable def traitSemistableChartProjection (A : CommRingCat.{u}) (π : A)
    (n r : ℕ) (hrn : r ≤ n) : Spec (traitSemistableChartAlgebra A π n r hrn) ⟶ Spec A :=
  Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span {traitSemistableEquation A π n r hrn})).comp
      MvPolynomial.C))

/-- The semistable equivariant alteration of an integral regular quasi-projective
scheme flat of finite type over a complete strictly henselian mixed-characteristic
trait. Source: ILO XVI 3.7, p.254; Vidal 2004b, Proposition 4.4.1
(blueprint: lem-per-trait-semistable-galois-alteration).

Proof, following the seven steps recorded in the DAG:
1. Apply lem-per-normal-projective-compactification, normalizing the constants
   inside k(X), to obtain a normal integral projective compactification C over S₀
   with geometrically integral generic fibre and X dense open in C.
2. If this fibre has dimension zero, proper_dim_zero_finite_over_field and
   geometric integrality identify it with the generic point of S₀. The proper
   valuative criterion extends its inverse to a section of C → S₀. Separatedness
   and integrality make both composites identities. Take X′ = X and G trivial;
   the equation t - π supplies the semistable chart even on the generic open.
3. Otherwise apply lem-per-trait-marked-nodal-alteration to C/S₀. Retain its finite
   group, complete strictly henselian base extension, marked nodal tower, and
   connected finite étale generic G-torsor. No log smoothness of the tower is assumed.
4. Apply lem-per-marked-nodal-tower-semistable-modification to that marked split
   tower. Its equivariant projective birational modification Z is integral regular
   and has the required semistable charts over S′.
5. Compose the projective maps by IsHProjective.comp and restrict Z to X using
   projective_base_change. Remove the proper image of the complement of a dense
   G-stable isomorphism open of the modification. The remaining nonempty open
   supports the original connected finite étale G-torsor. Integrality, regularity
   and the semistable charts restrict to this nonempty open of Z.
6. The composite trait extension is finite: pairwise products of finite module
   generators generate the composite algebra. finite_over_projective_affineLocally
   embeds S′ projectively over affine Noetherian S. Projective composition and open
   restriction give quasi-projectivity over both bases. Properness gives finite
   type for Z; Noetherianity makes its open X′ quasi-compact, hence finite type too.
7. Give X′ the divisorial structure of its generic fibre. In a chart t₁⋯tᵣ = π,
   the map ℕ → ℕʳ sends 1 to (1,…,1); it is injective with free group cokernel
   ℤʳ⁻¹. Its comparison is étale followed by an affine-space projection, hence
   smooth (smooth_and_fibre_dimension_zero_of_etale, affine-space smoothness,
   smooth_comp). The base chart 1 ↦ π is the canonical trait log structure.
   The chart definition gives log smoothness. The trait is log regular by its
   field stratum and dimension formula; logSmooth_logRegular gives log regularity
   of X′ and identifies these charts with the divisorial structure. Inverting the
   product trivializes it exactly on the generic fibre. The group preserves that
   fibre and therefore preserves this log structure. The same argument covers r=n=1.
-/
theorem exists_trait_semistable_galois_alteration
    (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsStrictlyHenselianLocalRing R] [CharZero (FractionRing R)]
    (hchar : ∃ p : ℕ, p.Prime ∧ CharP (IsLocalRing.ResidueField R) p)
    (X : Scheme.{u}) [IsIntegral X] (hreg : IsRegularScheme X)
    (s : X ⟶ Spec R) [Flat s] [LocallyOfFiniteType s] [QuasiCompact s]
    (hqp : ∃ (N : ℕ) (i : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec R)),
      IsImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (N + 1)); Spec R) ↘ Spec R = s) :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G)
      (A : CommRingCat.{u}) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
      (_ : IsStrictlyHenselianLocalRing A)
      (B Y : FineSaturatedLogScheme.{u}) (eS : B.scheme ≅ Spec A)
      (q : Y.scheme ⟶ Spec A) (a : Y.scheme ⟶ X) (t : Spec A ⟶ Spec R)
      (lq : EtaleLogHom Y B) (π : A)
      (ρY : G →* Aut Y.scheme) (ρB : G →* Aut B.scheme),
      IsFinite t ∧ IsDominant t ∧ IsIntegral Y.scheme ∧ IsRegularScheme Y.scheme ∧
      LocallyOfFiniteType q ∧ QuasiCompact q ∧
      LocallyOfFiniteType (q ≫ t) ∧ QuasiCompact (q ≫ t) ∧
      (∃ (N : ℕ) (i : Y.scheme ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec A)),
        IsImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (N + 1)); Spec A) ↘ Spec A = q) ∧
      (∃ (N : ℕ) (i : Y.scheme ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec R)),
        IsImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (N + 1)); Spec R) ↘ Spec R = q ≫ t) ∧
      a ≫ s = q ≫ t ∧ IsHProjective a ∧ IsDominant a ∧
      (∀ g : G, (ρY g).hom ≫ a = a) ∧
      (∀ g : G, (ρB g).hom ≫ eS.hom ≫ t = eS.hom ≫ t) ∧
      (∀ g : G, (ρY g).hom ≫ q = q ≫ eS.inv ≫ (ρB g).hom ≫ eS.hom) ∧
      (∃ (U : X.Opens) (_ : Nonempty U) (E : Scheme.GaloisCoverAction G U.toScheme)
        (eE : E.Z ≅ (a ⁻¹ᵁ U).toScheme),
        ConnectedSpace E.Z ∧ eE.hom ≫ (a ∣_ U) = E.π ∧
        ∀ g : G, E.smul g ≫ eE.hom ≫ (a ⁻¹ᵁ U).ι =
          eE.hom ≫ (a ⁻¹ᵁ U).ι ≫ (ρY g).hom) ∧
      Irreducible π ∧
      (∀ y : Y.scheme, ∃ (n r : ℕ) (_ : 1 ≤ r) (hrn : r ≤ n)
        (V : Y.scheme.Etale)
        (c : V.left ⟶ Spec (traitSemistableChartAlgebra A π n r hrn)),
        y ∈ Set.range V.hom ∧ Etale c ∧
          c ≫ traitSemistableChartProjection A π n r hrn = V.hom ≫ q) ∧
      (∃ e : B.logStructure.monoidSheaf.obj ≅ divisorialLogPresheaf
        (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ eS.inv),
        e.hom ≫ divisorialStructuralMap
          (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ eS.inv) =
            B.logStructure.alpha) ∧
      (∃ e : Y.logStructure.monoidSheaf.obj ≅ divisorialLogPresheaf
        (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))))),
        e.hom ≫ divisorialStructuralMap
          (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))))) =
            Y.logStructure.alpha) ∧
      Y.logStructure.trivialityLocus = Set.range
        (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))))) ∧
      (∀ g : G, ∃ lg : EtaleLogHom Y Y, lg.base = (ρY g).hom) ∧
      Y.IsLogRegular ∧ lq.base ≫ eS.hom = q ∧ lq.IsLogSmooth := by
  sorry

end AlgebraicGeometry
