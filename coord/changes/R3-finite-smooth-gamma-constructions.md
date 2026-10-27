# FiniteSmoothGammaNormalization constructions

## Reason

Move the existing constructions to a lower module so three genuine constituent normalization lemmas can import them without an import cycle. The original module publicly reexports the lower module. No signature, definition body, instance, attribute or existing public import changes. The one theorem is decomposed with a complete assembling proof.

## Old

The following declarations were in Sheaf.Paper.FiniteSmoothGammaNormalization:

```lean
/-- A finite-type fibre product over a Noetherian scheme is Noetherian. This packages
Mathlib's locally Noetherian and compact-space base-change instances into IsNoetherian.
Source: the item's proof Step 2, finite-type-over-Noetherian permanence
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
instance finiteSmoothPullbackNoetherian {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] :
    IsNoetherian (pullback f f) := {}

/-- The type of the compact-support comparison families in etaleSupportMapCompatibility.
This only names its existing quantified family type for use in the coordinate constructions.
Source: Stacks Tags 0F4Y and 0GKM
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
abbrev FiniteSmoothCompactSupportComparisons (A : Type (u + 1)) [CommRing A] :=
  ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification e),
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory

/-- The graph and homotopy normalization equations of etaleSupportMapCompatibility.
The sheaf arrow extends sheet sections by zero off their graphs; its degreewise descent,
followed by the total-derived unit, is the inverse comparison. Thus N is never an
unconstrained isomorphism. Source: Stacks Tags 0F4Y, 0GKM, 0F7L
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def FiniteSmoothComparisonNormalized (A : Type (u + 1)) [CommRing A]
    (N : FiniteSmoothCompactSupportComparisons A) : Prop :=
  ∃ a : ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
      (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (c : Compactification e),
      etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⟶
        openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
          lowerStar (ModuleCat.{u + 1} A) c.g,
    ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
      (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (c : Compactification e),
      (∀ M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
        (a e c).app M ≫ (compactificationSheafToDirectImage A c).app M =
          etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M) ∧
      (∀ P : HomotopyCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
          (ComplexShape.up ℤ),
        (N e c).inv.app (DerivedCategory.Qh.obj P) =
          compactSupportComparisonOnHomotopy A e c (a e c) P)

/-- Transport the graph-normalized fixed-compactification comparison to R e_!.
Source: Stacks Tags 0F4Y and 0GKM, as normalized by etaleSupportMapCompatibility
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothSumComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  (rightDerivedLowerShriekIso A (HasCompactification.compactification e)).symm ≪≫
    N e (HasCompactification.compactification e)

/-- The counit-preserving right-adjoint comparison rho_e, constructed by adjoint uniqueness.
The last transport changes exact degreewise inverse image into its left-derived model.
Source: the item's proof Step 1, Stacks Tags 0F4Y and 0GKM
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothAdjointCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    rightDerivedUpperShriek (ModuleCat.{u + 1} A) e ≅
      (upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctor :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) e).rightAdjointUniq
    (((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
      inferInstance).mapDerivedCategoryAdjunction).ofNatIsoLeft
      (finiteSmoothSumComparison A N e).symm) ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm

/-- Coordinates omega_e ≅ A_V induced by rho_e at A_T.
Source: the item's proof Step 1 (blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothOmegaCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    dualizingComplex (ModuleCat.{u + 1} A) e ≅
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A V) :=
  (finiteSmoothAdjointCoordinates A N e).app _ ≪≫
    leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) e

/-- Coordinates on the section invariant, obtained by pulling back rho_e at the unit.
Source: the item's proof Steps 1--3
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothSectionCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] (s : T ⟶ V) :
    sectionInvariant A e s ≅ MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A T) :=
  (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.mapIso
    (finiteSmoothOmegaCoordinates A N e) ≪≫
      leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) s

/-- First factor: pull back the actual exceptional base-change map by the diagonal.
The inverse section compositor identifies Delta^* p_2^* omega_f with omega_f.
Source: three-factor formula, prop-asd-smooth-base-change, proof Step 3
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothDiagonalFactor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    dualizingComplex (ModuleCat.{u + 1} A) f ⟶
      sectionInvariant A (pullback.fst f f) (pullback.diagonal f) :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f)).inv.app _ ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.diagonal f)).leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f f).flip)

/-- Type of deformation comparisons for the actual diagonal Rees space.
Source: lem-pur-noetherian-etale-section-specialization, normalized kappa
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def FiniteSmoothDeformationComparisons (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (hc : HasCompactification
      (Scheme.Hom.deformationSpaceProj (pullback.fst f f) (pullback.diagonal f))) :=
  letI := hc
  NoetherianSectionSpecialization.family A (pullback.fst f f) (pullback.diagonal f) ≅
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) X ↘ X)).leftDerivedFunctor.obj
        (sectionInvariant A (pullback.fst f f) (pullback.diagonal f))

/-- The normalization condition on the preceding comparison is exactly its t=1 condition.
Source: lem-pur-noetherian-etale-section-specialization, Normalized
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def FiniteSmoothDeformationNormalized (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f]
    (hc : HasCompactification
      (Scheme.Hom.deformationSpaceProj (pullback.fst f f) (pullback.diagonal f)))
    (κ : FiniteSmoothDeformationComparisons A f hc) : Prop :=
  letI := hc
  NoetherianSectionSpecialization.Normalized A (pullback.fst f f) (pullback.diagonal f)
    (pullback.diagonal_fst f) κ

/-- Proofs of the rank-zero geometry and the uniquely normalized deformation comparison.
The only non-proof field is kappa, whose t=1 normalization determines it uniquely by
lem-pur-noetherian-etale-section-specialization; no arbitrary existence choice is made.
Source: the item's proof Steps 2, 4--6
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
structure FiniteSmoothGammaData (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] where
  /-- The actual normal projection identifies the rank-zero cone with X. -/
  normalIso : IsIso (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
  /-- Compactifiability of the actual extended-Rees family. -/
  deformationCompact : HasCompactification
    (Scheme.Hom.deformationSpaceProj (pullback.fst f f) (pullback.diagonal f))
  /-- The normalized family comparison, not an arbitrary comparison of its fibres. -/
  comparison : FiniteSmoothDeformationComparisons A f deformationCompact
  /-- Normalization by the specified mate on the fibre t=1. -/
  normalized : FiniteSmoothDeformationNormalized A f deformationCompact comparison

/-- The actual section invariant on the normal cone, retaining its Rees construction.
Source: the item's proof Step 4 (blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothNormalInvariant (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] (G : FiniteSmoothGammaData A f) : DerivedCategoryModule A X :=
  letI := G.normalIso
  sectionInvariant A (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
    (pullback.diagonal f).normalConeZeroSection

/-- Second factor: the specified specialization, evaluated at zero from normalized kappa.
Source: the item's proof Step 6; lem-pur-noetherian-etale-section-specialization
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothDeformationFactor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] (G : FiniteSmoothGammaData A f) :
    sectionInvariant A (pullback.fst f f) (pullback.diagonal f) ⟶
      finiteSmoothNormalInvariant A f G :=
  letI := G.normalIso
  letI := G.deformationCompact
  NoetherianSectionSpecialization.specialization A (pullback.fst f f)
    (pullback.diagonal f) G.comparison

/-- Normal-cone coordinates from the same graph-normalized sum adjunction.
Source: the item's proof Steps 1, 6--7
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothNormalCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (G : FiniteSmoothGammaData A f) :
    finiteSmoothNormalInvariant A f G ≅
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A X) :=
  letI := G.normalIso
  letI := LocallyOfFiniteType.isLocallyNoetherian
    (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
  letI := QuasiCompact.compactSpace_of_compactSpace
    (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
  letI : IsNoetherian (pullback.diagonal f).ker.normalCone := {}
  finiteSmoothSectionCoordinates A N
    (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
    (pullback.diagonal f).normalConeZeroSection

/-- In rank zero the integration is the identity-adjunction trace. Its adjunct is the
vector-bundle purity map; invert it and restrict by the zero section. The actual normal
cone is transported to (X,1_X) by its projection and zero section, using the exceptional
base-change mate. Thus this formula retains the canonical geometric transport.
Source: def-amb-vector-integration, rank-zero local trace; thm-amb-vector-bundle-purity;
the item's proof Step 7 (blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothRankZeroFactor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] (G : FiniteSmoothGammaData A f) :
    finiteSmoothNormalInvariant A f G ⟶
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A X) := by
  letI := G.normalIso
  let π := Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f)
  let z := (pullback.diagonal f).normalConeZeroSection
  have hz : z ≫ π = 𝟙 X :=
    Scheme.Hom.normalConeZeroSection_normalConeProj (pullback.diagonal_fst f)
  let sq : IsPullback z (𝟙 X) π (𝟙 X) := IsPullback.of_vert_isIso ⟨by simpa using hz⟩
  exact (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).inv.app _ ≫
    NoetherianSectionSpecialization.sectionMap A π (𝟙 X) (𝟙 X) z sq z (𝟙 X)
      (by simp) ≫
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app _ ≫
    ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (𝟙 X)).rightAdjointUniq
      (Adjunction.id.ofNatIsoLeft (unboundedEtaleLowerShriekId A X).symm)).hom.app _

/-- Gamma is the canonical smooth tensor map after the inverse three-factor orientation.
Source: sk-thm-smooth-purity, displayed gamma formula
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothGammaMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (α : dualizingComplex (ModuleCat.{u + 1} A) f ≅
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A X))
    (K : DerivedCategoryModule A Y) :
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K :=
  (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).inv ≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).map α.inv ≫
    smoothTensorDualityMap (ModuleCat.{u + 1} A) f
      (isIso_projectionMap_of_finite A f) K

```

## New

The identical declaration block is now in Sheaf.Paper.FiniteSmoothGammaConstructions, publicly imported by its old owner. Existing declaration names, signatures and bodies are byte-for-byte unchanged. The original six public imports are retained.

The new declaration block is verbatim:

```lean
/-- A finite-type fibre product over a Noetherian scheme is Noetherian. This packages
Mathlib's locally Noetherian and compact-space base-change instances into IsNoetherian.
Source: the item's proof Step 2, finite-type-over-Noetherian permanence
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
instance finiteSmoothPullbackNoetherian {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] :
    IsNoetherian (pullback f f) := {}

/-- The type of the compact-support comparison families in etaleSupportMapCompatibility.
This only names its existing quantified family type for use in the coordinate constructions.
Source: Stacks Tags 0F4Y and 0GKM
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
abbrev FiniteSmoothCompactSupportComparisons (A : Type (u + 1)) [CommRing A] :=
  ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification e),
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory

/-- The graph and homotopy normalization equations of etaleSupportMapCompatibility.
The sheaf arrow extends sheet sections by zero off their graphs; its degreewise descent,
followed by the total-derived unit, is the inverse comparison. Thus N is never an
unconstrained isomorphism. Source: Stacks Tags 0F4Y, 0GKM, 0F7L
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def FiniteSmoothComparisonNormalized (A : Type (u + 1)) [CommRing A]
    (N : FiniteSmoothCompactSupportComparisons A) : Prop :=
  ∃ a : ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
      (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (c : Compactification e),
      etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⟶
        openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
          lowerStar (ModuleCat.{u + 1} A) c.g,
    ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
      (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (c : Compactification e),
      (∀ M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
        (a e c).app M ≫ (compactificationSheafToDirectImage A c).app M =
          etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M) ∧
      (∀ P : HomotopyCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
          (ComplexShape.up ℤ),
        (N e c).inv.app (DerivedCategory.Qh.obj P) =
          compactSupportComparisonOnHomotopy A e c (a e c) P)

/-- Transport the graph-normalized fixed-compactification comparison to R e_!.
Source: Stacks Tags 0F4Y and 0GKM, as normalized by etaleSupportMapCompatibility
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothSumComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  (rightDerivedLowerShriekIso A (HasCompactification.compactification e)).symm ≪≫
    N e (HasCompactification.compactification e)

/-- The counit-preserving right-adjoint comparison rho_e, constructed by adjoint uniqueness.
The last transport changes exact degreewise inverse image into its left-derived model.
Source: the item's proof Step 1, Stacks Tags 0F4Y and 0GKM
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothAdjointCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    rightDerivedUpperShriek (ModuleCat.{u + 1} A) e ≅
      (upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctor :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) e).rightAdjointUniq
    (((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
      inferInstance).mapDerivedCategoryAdjunction).ofNatIsoLeft
      (finiteSmoothSumComparison A N e).symm) ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm

/-- Coordinates omega_e ≅ A_V induced by rho_e at A_T.
Source: the item's proof Step 1 (blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothOmegaCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    dualizingComplex (ModuleCat.{u + 1} A) e ≅
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A V) :=
  (finiteSmoothAdjointCoordinates A N e).app _ ≪≫
    leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) e

/-- Coordinates on the section invariant, obtained by pulling back rho_e at the unit.
Source: the item's proof Steps 1--3
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothSectionCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] (s : T ⟶ V) :
    sectionInvariant A e s ≅ MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A T) :=
  (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.mapIso
    (finiteSmoothOmegaCoordinates A N e) ≪≫
      leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) s

/-- First factor: pull back the actual exceptional base-change map by the diagonal.
The inverse section compositor identifies Delta^* p_2^* omega_f with omega_f.
Source: three-factor formula, prop-asd-smooth-base-change, proof Step 3
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothDiagonalFactor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    dualizingComplex (ModuleCat.{u + 1} A) f ⟶
      sectionInvariant A (pullback.fst f f) (pullback.diagonal f) :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f)).inv.app _ ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.diagonal f)).leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f f).flip)

/-- Type of deformation comparisons for the actual diagonal Rees space.
Source: lem-pur-noetherian-etale-section-specialization, normalized kappa
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def FiniteSmoothDeformationComparisons (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (hc : HasCompactification
      (Scheme.Hom.deformationSpaceProj (pullback.fst f f) (pullback.diagonal f))) :=
  letI := hc
  NoetherianSectionSpecialization.family A (pullback.fst f f) (pullback.diagonal f) ≅
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) X ↘ X)).leftDerivedFunctor.obj
        (sectionInvariant A (pullback.fst f f) (pullback.diagonal f))

/-- The normalization condition on the preceding comparison is exactly its t=1 condition.
Source: lem-pur-noetherian-etale-section-specialization, Normalized
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def FiniteSmoothDeformationNormalized (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f]
    (hc : HasCompactification
      (Scheme.Hom.deformationSpaceProj (pullback.fst f f) (pullback.diagonal f)))
    (κ : FiniteSmoothDeformationComparisons A f hc) : Prop :=
  letI := hc
  NoetherianSectionSpecialization.Normalized A (pullback.fst f f) (pullback.diagonal f)
    (pullback.diagonal_fst f) κ

/-- Proofs of the rank-zero geometry and the uniquely normalized deformation comparison.
The only non-proof field is kappa, whose t=1 normalization determines it uniquely by
lem-pur-noetherian-etale-section-specialization; no arbitrary existence choice is made.
Source: the item's proof Steps 2, 4--6
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
structure FiniteSmoothGammaData (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] where
  /-- The actual normal projection identifies the rank-zero cone with X. -/
  normalIso : IsIso (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
  /-- Compactifiability of the actual extended-Rees family. -/
  deformationCompact : HasCompactification
    (Scheme.Hom.deformationSpaceProj (pullback.fst f f) (pullback.diagonal f))
  /-- The normalized family comparison, not an arbitrary comparison of its fibres. -/
  comparison : FiniteSmoothDeformationComparisons A f deformationCompact
  /-- Normalization by the specified mate on the fibre t=1. -/
  normalized : FiniteSmoothDeformationNormalized A f deformationCompact comparison

/-- The actual section invariant on the normal cone, retaining its Rees construction.
Source: the item's proof Step 4 (blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothNormalInvariant (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] (G : FiniteSmoothGammaData A f) : DerivedCategoryModule A X :=
  letI := G.normalIso
  sectionInvariant A (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
    (pullback.diagonal f).normalConeZeroSection

/-- Second factor: the specified specialization, evaluated at zero from normalized kappa.
Source: the item's proof Step 6; lem-pur-noetherian-etale-section-specialization
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothDeformationFactor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] (G : FiniteSmoothGammaData A f) :
    sectionInvariant A (pullback.fst f f) (pullback.diagonal f) ⟶
      finiteSmoothNormalInvariant A f G :=
  letI := G.normalIso
  letI := G.deformationCompact
  NoetherianSectionSpecialization.specialization A (pullback.fst f f)
    (pullback.diagonal f) G.comparison

/-- Normal-cone coordinates from the same graph-normalized sum adjunction.
Source: the item's proof Steps 1, 6--7
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothNormalCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (G : FiniteSmoothGammaData A f) :
    finiteSmoothNormalInvariant A f G ≅
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A X) :=
  letI := G.normalIso
  letI := LocallyOfFiniteType.isLocallyNoetherian
    (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
  letI := QuasiCompact.compactSpace_of_compactSpace
    (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
  letI : IsNoetherian (pullback.diagonal f).ker.normalCone := {}
  finiteSmoothSectionCoordinates A N
    (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
    (pullback.diagonal f).normalConeZeroSection

/-- In rank zero the integration is the identity-adjunction trace. Its adjunct is the
vector-bundle purity map; invert it and restrict by the zero section. The actual normal
cone is transported to (X,1_X) by its projection and zero section, using the exceptional
base-change mate. Thus this formula retains the canonical geometric transport.
Source: def-amb-vector-integration, rank-zero local trace; thm-amb-vector-bundle-purity;
the item's proof Step 7 (blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothRankZeroFactor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] (G : FiniteSmoothGammaData A f) :
    finiteSmoothNormalInvariant A f G ⟶
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A X) := by
  letI := G.normalIso
  let π := Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f)
  let z := (pullback.diagonal f).normalConeZeroSection
  have hz : z ≫ π = 𝟙 X :=
    Scheme.Hom.normalConeZeroSection_normalConeProj (pullback.diagonal_fst f)
  let sq : IsPullback z (𝟙 X) π (𝟙 X) := IsPullback.of_vert_isIso ⟨by simpa using hz⟩
  exact (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).inv.app _ ≫
    NoetherianSectionSpecialization.sectionMap A π (𝟙 X) (𝟙 X) z sq z (𝟙 X)
      (by simp) ≫
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app _ ≫
    ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (𝟙 X)).rightAdjointUniq
      (Adjunction.id.ofNatIsoLeft (unboundedEtaleLowerShriekId A X).symm)).hom.app _

/-- Gamma is the canonical smooth tensor map after the inverse three-factor orientation.
Source: sk-thm-smooth-purity, displayed gamma formula
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothGammaMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (α : dualizingComplex (ModuleCat.{u + 1} A) f ≅
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A X))
    (K : DerivedCategoryModule A Y) :
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K :=
  (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).inv ≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).map α.inv ≫
    smoothTensorDualityMap (ModuleCat.{u + 1} A) f
      (isIso_projectionMap_of_finite A f) K

```

## Users

The source graph reports 510 transitive importers. Every one receives the identical constructions through the old public module; none needs adaptation. Group ownership is not modified or relied upon. Only the direct importer needs recompilation for this interface-preserving relocation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTowerTensorCounit | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicActualSystemsNormalized | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicNormalizedPurityLift | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicNormalizedPuritySystems | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicPurityScalarNaturality | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicPuritySourceFiniteness | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicPuritySourceNormalization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicPuritySourceTransitionSquare | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicUnitTraceConstruction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicUnitTraceReductionData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicUnitTraceScalarData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AffineCounitScalar | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AffineIntegrationExponentTransition | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AffineOrderedCounitDescentComparison | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AffineOrderedCounitSuccessor | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AffineOrderedCounitZero | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ArithmeticRoots | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CentredDiagonalSourcePasting | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartCounitScalarTransport | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartDiagonalAssemblyData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartDiagonalSourceMate | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartDiagonalSourceSquare | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartDncNaturality | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartDncSquare | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartDncVectorFactorData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartDncVectorFactors | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartEpsilonPasting | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartExceptionalCounitEquation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartExceptionalMateCoherence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartIntegrationAdjoints | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartNormalIntegrationSquare | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ChartTargetOpenDescent | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CochainLocalizationTensorIso | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CommonStageSmoothOperationCore | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CommonStageSmoothOperationShift | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CompositeProjectionCoefficients | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CompositionComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CompositionIteratedMateExpansion | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CompositionModelOrientationDescent | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CompositionSingleMatePresentation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CondensedIntegralEndpoints | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CondensedTateIntegralTower | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CondensedTateIntegralTowerData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CurveIntermediateExtension | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.DiagonalDncChartNormalization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.DiagonalOrientationCharts | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.DualizingObjectPurity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.EtaleOrientationLocality | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionCompletedStrictLimit | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionComposition | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionIntegralDescent | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionIntegralModels | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionLimitEquations | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionRationalComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionRationalDescent | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionRationalModels | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionReductionDescent | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionReductionLimits | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionStrictLimits | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldExtensionTowers | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldOrientationSystemComparison | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldOrientationSystemComparisonData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldOrientationSystemCoordinates | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldOrientationSystemFiniteOrientation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldOrientationSystemHeart | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldOrientationSystemNormalizations | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldOrientationSystemRigidity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldOrientedExchangeSquares | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldPuritySystemTranspose | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldPuritySystemTransposeBase | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldPuritySystemTransposeCompatibility | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldPurityTransposeArrows | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteDiagonalDncReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteDncNormalizationReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteFirstRootChart | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteGeometricOrientationExchange | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteGeometricPurityCoordinates | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteGeometricPurityFactors | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteGeometricPurityMate | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteGeometricTensorExchange | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteNormalizedOrientationScalar | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteOrientationReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FinitePositiveChartFrameExt | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FinitePositiveChartRecursion | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FinitePositiveRootChartPower | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FinitePositiveRootCharts | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteProductReductionComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteProductScalarPresentation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FinitePublishedRootChartPower | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FinitePurityCounitSystem | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FinitePuritySourceUnitReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionAffineOrientation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionChartCalculus | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionLineChartScalars | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionLineInputConstructible | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionOfPurity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionReassociation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionRootCharts | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionTensorFactors | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionTensorPurity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionTensorSource | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteReductionThetaFactor | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteRootLinePowerTransition | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteRootTensorPresentation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteScalarCochainComparisonIso | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteScalarMonoidalRepresentative | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteScalarRepresentativeIso | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteScalarTensorData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteScalarTensorSource | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSectionIntegratedScalar | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSectionIntegratedSpecialization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSignedTwistProducts | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSmoothDiagonalScalar | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSmoothOrientationBaseChange | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSmoothPurityMaps | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSourceChartPowerTransition | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSourceChartScalarTransition | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteSupportedReductionEquation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTateBalancedScalarPullback | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTateScalarSourceData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTateScalarSourceExistence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTateScalarSourceNormalization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTateSourceMap | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTateSourceStructuralCoherence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorComparisonEquations | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorFixedComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorLineChartReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorPresentationReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorProductFrameExt | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorProductMap | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorProductMapIsIso | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorPullbackCompositionReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorPullbackTensorReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorReductionData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorSemilinearReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorShiftCoherence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorShiftFirst | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorShiftSecond | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorSignedReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.FixedPresentationUniformizerReductions | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.GeneralChartComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.GeneralCondensedWeilRealization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.GeometricSmoothReconstructionSetup | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralAdjunctionBijection | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralCoefficientModelComparison | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralCompositorLimitRealization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralEquivarianceMate | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralEquivarianceNaturality | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralGeometricComparisonData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralGeometricComparisonRealization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralGeometricPurityRealization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralGeometricReindexingRealization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralGeometricSupportRealization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralGeometricTransposeIdentity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralPurityCounitReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralReconstructionComparisonData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralReconstructionComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IteratedPurityScalarPasting | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.IteratedTateSourceComposite | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ModelChartOrientationAssembly | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ModelCompactComparisonUnit | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ModelOrientationChartDescent | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ModelOrientationSourceNaturality | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ModelOrientationTateDetection | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.NormalModelSectionOrientation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.NormalSectionIntegrationBaseChange | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.NormalSectionIntegrationData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.NormalSectionIntegrationOrientation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.NormalizedFieldPurityTrace | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.NormalizedIntegralTraceData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.NormalizedTateTensorTower | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.OrderedLineLevelBounds | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.OrderedTateScalarNormalization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.OrderedTateTowerCohomology | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.OrderedTowerOrientation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.OrientationGroundFieldRetagging | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.OrientationScalarPropagation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.OrientationScalarTowerTransport | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.P1CounitScalar | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PoincareDualityConventions | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ProjectionPurityAgreement | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ProjectionTensorIntegration | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.ProjectionUnitPresentationNormalization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PulledOrderedLineSingle | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PurAdicReconstruction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PurityCompactSupportTransport | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PurityCompositionCoherence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PurityConjugatesTowerReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PurityFiniteReductionTransport | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PurityFiniteTateSourceComparisonCalculus | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PurityKappaStages | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PurityOrientationDatum | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PurityPullbackLevelBounds | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PurityPullbackReductionTransport | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PurityTateDatum | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.PurityTowerReductionComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RationalExceptionalFinalEquations | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RationalPurityCoherenceDescent | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RationalPurityComparisonDescent | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RationalPurityExchangeEndpointData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RationalPurityExchangeEndpoints | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RationalPurityLocalizedFamilyData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RationalPurityScalarLocalization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RationalPuritySourceLocalization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RationalScalarComparisonData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RationalScalarComparisonIdentification | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RawChartScalarCounitPasting | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RegularImmersionPurityComparison | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.RetaggingCoordinateOrientations | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SectionDncIntegrationSquare | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SectionEtaleOpenCancellation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothOperationCoefficientModels | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothOperationDescentSpecification | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothOrientationPuritySquares | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothOrientationStageExchange | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothPurityBaseChangeData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothPurityCompositionFactors | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothPurityFieldExtension | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothPurityTowerGamma | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SmoothPurityTowerGammaData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.SpecifiedTowerAdjunctionCharts | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TateScalarPullbackCoherence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TensorTransposeTowerNaturality | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerFactorOrientation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerFactorTensor | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerGeometricPurityAssembly | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerGeometricPurityData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerGeometricPurityMate | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerIsomorphismPullback | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerMuEvaluation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerNormalizationPreservation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerOrientationEvaluation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerOrientationWordNormalization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerPurityAdjointTransport | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerPurityPresentationRetagging | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerPurityRealizedData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerPurityRealizedNormalization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerPurityRealizedTranspose | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerSemilinearPurityFactors | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerTateSplitNormalized | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerTensorAdjointDomains | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerTensorPresentationRetagging | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerTensorTransposeWords | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerTracePurityComparison | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerTracePurityComparisonData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TowerTraceScalarCounit | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TransportCondensedStageRealization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TransportIntegralBaseChangeRealization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TransportIntegralChartRealization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TransportIntegralCompositionRealization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TransportIntegralCounitData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TransportIntegralCounitRealization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TransportIntegralStageConstruction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackPbcPullback | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackPbcTwist | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackScalarShifts | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackSquareMaps | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackSquareScalars | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackTowerBounds | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackTowerDomain | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.TwistedPullbackTowerOrigins | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.UniformTowerTensorClosure | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.VectorIntegrationChartComparison | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.VectorIntegrationChartTranspose | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.VectorIntegrationIdentityAdjunct | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.VectorModelChartDescent | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.VectorTraceScalarDescent | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Paper.WeilPurityEquivarianceData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SecSmoothPurity.NestedAffineChartFormulas | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SecSmoothPurity.NestedAffineFormulaData | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SecSmoothPurity.ReductionOrientation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SixFunctors.KappaCoefficientCoherence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SixFunctors.KappaGeometricComparisons | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.SixFunctors.KappaMixedCoherence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Targets.PoincareUncurry | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.Targets.SmoothPurityQbar | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| Sheaf.ZetaWeil.WeightPurityRoots | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| TargetsCheck | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.PoincareDuality.Poincare | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.SmoothPurity.Defs | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.Statement | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.BorelMoore | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.CoefficientMorphism | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.Correspondence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.CorrespondencePair | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.CurvePieces | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.Dualizing | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.GenericQuotient | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.HomologyUnit | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.KunnethVerdier | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.LefschetzVerdier | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.LocalTerm | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.LocalTermLocality | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.Main | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.PointNormalization | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.Product | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.ProperCompatibility | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.ProperCurve | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.ProperPushforward | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.PullbackFamily | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.Statement | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.SupportedPairing | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.TraceClass | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.WeilBaseChange | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.TraceFormula.WeilTrace | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.WeilSheaf.Curve | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.WeilSheaf.EulerProduct | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.WeilSheaf.LFunction | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.WeilSheaf.RealPurity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.Examples | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.FinalTheorems | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.HasseWeil | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.IntegralFactors | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.LissePurity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.Rationality | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.RelativePurity | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.SmoothProper | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.TraceFormula | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.WeightSeparation | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.Weights | not adapted; ownership unaffected | Identical reexported API and data; no edit. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | not adapted; ownership unaffected | Identical reexported API and data; no edit. |

## Status

landed 20261027T131504-L-2945560 2026-10-27 (merge of deliver/R3/Sheaf.Paper.FiniteSmoothGammaNormalization)
