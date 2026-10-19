# AlgebraicGeometry.ProEtale.normalizedOriginScalarUnit and companion scalar comparisons

## Reason

The comparison-coherence theorem must use the scalar unit and associator, and the
normalized-witness proof must import that theorem. Move the five existing scalar
comparison declarations to a support module to avoid a cycle. The old module publicly
imports the support module. This changes only their module location and docstring node
references: every name, universe, binder, type, visibility and definition body is retained.
The theorem and NormalizedOriginCompatibility keep their existing signatures and meaning.
Remove unused public and proof imports from the witness module.

## Old

In `Sheaf.Paper.NormalizedEtaleOriginWitnesses`:

```lean
def normalizedOriginRestrictionUnit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R] (φ : R →+* R) (hφ : φ = RingHom.id R) :
    Sheaf.restrictScalars J φ ≅ 𝟭 (Sheaf J (ModuleCat.{u + 1} R)) :=
  NatIso.ofComponents
    (fun F ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsId' φ hφ) ≪≫
        F.obj.rightUnitor))
    (fun {F G} f ↦ by
      apply (fullyFaithfulSheafToPresheaf J _).map_injective
      ext U x
      rfl)

/-- Canonical self-extension unit, the adjunction mate of identity scalar restriction.
It is the derived map x tensor a to ax, not a chosen automorphism.
Source: Stacks 06YY, unit balancing in the coefficient refinement of Tag 09B1
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses). -/
def normalizedOriginScalarUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]
    (φ : R →+* R) (hφ : φ = RingHom.id R) :
    pbcFixedScalarExtension J φ ≅ 𝟭 (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  Adjunction.leftAdjointIdIso (Adjunction.ofIsRightAdjoint _)
    (Functor.mapDerivedCategoryNatIso (normalizedOriginRestrictionUnit J φ hφ) ≪≫
      Functor.mapDerivedCategoryIdIso _)

/-- The canonical scalar unit at a positive quotient, including the first quotient.
Source: Stacks 06YY and 09B1, coefficient refinement
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses). -/
def normalizedOriginQuotientUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    pbcFixedScalarExtension J (pbcWitnessQuotientMap d n n (le_refl n)) ≅ 𝟭 _ :=
  normalizedOriginScalarUnit J _
    (Scheme.adicQuotientMap_id d.ideal ⟨n + 1, Nat.succ_pos n⟩)

/-- Canonical reassociation for three quotient levels. This is the published
scalar-extension composition comparison, with the actual quotient-factor identity.
Source: Stacks 06YY and 09B1, coefficient refinement
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses). -/
def normalizedOriginQuotientComp
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (k m n : ℕ) (hnm : n ≤ m) (hmk : m ≤ k) :
    pbcFixedScalarExtension J (pbcWitnessQuotientMap d k m hmk) ⋙
        pbcFixedScalarExtension J (pbcWitnessQuotientMap d m n hnm) ≅
      pbcFixedScalarExtension J (pbcWitnessQuotientMap d k n (hnm.trans hmk)) :=
  pbcFixedScalarExtensionComp J _ _ _
    (Scheme.adicQuotientMap_comp d.ideal ⟨k + 1, Nat.succ_pos k⟩
      ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩
      (Nat.add_le_add_right hnm 1) (Nat.add_le_add_right hmk 1)).symm

/-- Direct quotient scalar extension, in the published fixed-ring presentation.
Source: Stacks 06YY and 09B1, coefficient refinement
(blueprint: lem-weil-pbc-normalized-etale-origin-witnesses). -/
abbrev normalizedOriginReduction
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (m n : ℕ) (h : n ≤ m) :=
  pbcFixedScalarExtension J (pbcWitnessQuotientMap d m n h)
```

Original imports at inspection:

```lean
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
```

## New

In `Sheaf.Paper.NormalizedOriginScalarComparisons`, under the same namespace and
`@[expose] public noncomputable section`, with the original `universe u`:

```lean
def normalizedOriginRestrictionUnit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R] (φ : R →+* R) (hφ : φ = RingHom.id R) :
    Sheaf.restrictScalars J φ ≅ 𝟭 (Sheaf J (ModuleCat.{u + 1} R)) :=
  NatIso.ofComponents
    (fun F ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsId' φ hφ) ≪≫
        F.obj.rightUnitor))
    (fun {F G} f ↦ by
      apply (fullyFaithfulSheafToPresheaf J _).map_injective
      ext U x
      rfl)

/-- Canonical self-extension unit, the adjunction mate of identity scalar restriction.
It is the derived map x tensor a to ax, not a chosen automorphism.
Source: Stacks 06YY, unit balancing in the coefficient refinement of Tag 09B1
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
def normalizedOriginScalarUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]
    (φ : R →+* R) (hφ : φ = RingHom.id R) :
    pbcFixedScalarExtension J φ ≅ 𝟭 (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  Adjunction.leftAdjointIdIso (Adjunction.ofIsRightAdjoint _)
    (Functor.mapDerivedCategoryNatIso (normalizedOriginRestrictionUnit J φ hφ) ≪≫
      Functor.mapDerivedCategoryIdIso _)

/-- The canonical scalar unit at a positive quotient, including the first quotient.
Source: Stacks 06YY and 09B1, coefficient refinement
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
def normalizedOriginQuotientUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    pbcFixedScalarExtension J (pbcWitnessQuotientMap d n n (le_refl n)) ≅ 𝟭 _ :=
  normalizedOriginScalarUnit J _
    (Scheme.adicQuotientMap_id d.ideal ⟨n + 1, Nat.succ_pos n⟩)

/-- Canonical reassociation for three quotient levels. This is the published
scalar-extension composition comparison, with the actual quotient-factor identity.
Source: Stacks 06YY and 09B1, coefficient refinement
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
def normalizedOriginQuotientComp
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (k m n : ℕ) (hnm : n ≤ m) (hmk : m ≤ k) :
    pbcFixedScalarExtension J (pbcWitnessQuotientMap d k m hmk) ⋙
        pbcFixedScalarExtension J (pbcWitnessQuotientMap d m n hnm) ≅
      pbcFixedScalarExtension J (pbcWitnessQuotientMap d k n (hnm.trans hmk)) :=
  pbcFixedScalarExtensionComp J _ _ _
    (Scheme.adicQuotientMap_comp d.ideal ⟨k + 1, Nat.succ_pos k⟩
      ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩
      (Nat.add_le_add_right hnm 1) (Nat.add_le_add_right hmk 1)).symm

/-- Direct quotient scalar extension, in the published fixed-ring presentation.
Source: Stacks 06YY and 09B1, coefficient refinement
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
abbrev normalizedOriginReduction
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (m n : ℕ) (h : n ≤ m) :=
  pbcFixedScalarExtension J (pbcWitnessQuotientMap d m n h)
```

The witness module now imports:

```lean
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.NormalizedOriginScalarComparisons
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.Paper.NormalizedOriginComparisonCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
```

The support module publicly imports `Sheaf.Paper.WitnessCompatibility` and
`Sheaf.Paper.AdicCoefficientDatum`. No target meaning changes: the five definition
bodies are identical, and the original module publicly reexports them. No target
signature, universe, hypothesis or conclusion changes. The independent reader should
verify the relocation and reexport when checking the public-import change.

## Users

The required current `tools/downstream.py --uses` source scan covered 188 transitive
importers. All five relocated definition bodies were also compared byte for byte with the
current original module; all are identical. The signatures of NormalizedOriginCompatibility
and normalizedEtaleOriginWitnesses are identical to their originals. The name scan
found only the five downstream scalar-unit users below (all other moved names occurred
only in the original module). Holders were read at inspection; no held module was edited.
The original five direct importers were copied unchanged for compilation against the three new
files, then excluded from the delivery. All compiled without errors or warnings.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.NormalizedEtaleOriginWitnesses` | A8 | Own module: proof completed from coherence; public reexport retains all moved declarations. |
| `Sheaf.Paper.FiniteExceptionalSystemAdjunction` | unclaimed | New direct scalar-unit user; definition body and public reexport are unchanged. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | U2 | Uses scalar unit; original direct consumer compiled unchanged. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Transitive scalar-unit user; same declaration and definition body remain available through public reexport. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | Uses scalar unit; original direct consumer compiled unchanged. |
| `Sheaf.SixFunctors.GeoCartierCoeffExtension` | Z8 | Uses scalar unit; original direct consumer compiled unchanged. |
| `Sheaf.Paper.AdicSmoothBaseChange` | unclaimed | Direct importer; original compiled unchanged. |
| `Sheaf.Paper.PreservationConstructible` | B5 | Direct importer; original compiled unchanged. |
| `Sheaf.Paper.NormalizedOriginScalarComparisons` | new, A8 delivery | Receives the five definitions verbatim, without a new proof hole. |
| `Sheaf.Paper.NormalizedOriginComparisonCoherence` | new, A8 delivery | Uses the relocated unit and associator; no downstream statement is changed. |

No consumer adaptation is included or necessary. The 188 modules that merely import
transitively retain the same exported scalar declarations. No statement becomes stronger
or weaker as a result of the relocation.

## Status

landed 20261019T002501-L-2139940 2026-10-19 (merge of deliver/A8/Sheaf.Paper.NormalizedEtaleOriginWitnesses)
