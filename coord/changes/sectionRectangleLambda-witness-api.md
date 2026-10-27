# AlgebraicGeometry.ProEtale.QuotientChange.sectionRectangleLambda

## Reason

Extract the balancing witness and its realization equation in a named proved
existence theorem, then choose that witness. The original extraction repeated
kernel checks of all three nested existential predicates, including generator
and K-flat equations, on every definition use. The extracted theorem is proved
by the original witness and its final equation. That equation uniquely determines
the isomorphism: cancel the invertible pullback and scalar comparisons; every
section object is isomorphic to a realization object, and naturality determines
the remaining components. Thus this presentation preserves the specified map.
It introduces no hollow data and no arbitrary choice from mere existence.

## Old

```lean
def sectionRectangleLambda (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : SectionScalarComparison φ U) (sV : SectionScalarComparison φ V)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (p : SectionPullNormalized φ h sU sV b) :
    sV.pair.derived ⋙ ModuleRingedComparison.derivedPullback Λ' h ≅
      ModuleRingedComparison.derivedPullback Λ h ⋙ sU.pair.derived :=
  p.choose_spec.2.choose_spec.2.choose
```

## New

```lean
theorem sectionRectangleLambda_witness (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : SectionScalarComparison φ U) (sV : SectionScalarComparison φ V)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (p : SectionPullNormalized φ h sU sV b) :
    ∃ d : sV.pair.derived ⋙ ModuleRingedComparison.derivedPullback Λ' h ≅
        ModuleRingedComparison.derivedPullback Λ h ⋙ sU.pair.derived,
      ∀ M : DerivedCategory (Modules Λ V),
        (ModuleRingedComparison.derivedEquivalence Λ' U).functor.map (b.hom.app M) ≫
            sU.derived.hom.app ((L Λ h).obj M) ≫
            sU.pair.derived.map ((scalarSectionPullComparison Λ h).hom.app M) =
          (scalarSectionPullComparison Λ' h).hom.app ((D φ V).obj M) ≫
            (ModuleRingedComparison.derivedPullback Λ' h).map (sV.derived.hom.app M) ≫
            d.hom.app ((ModuleRingedComparison.derivedEquivalence Λ V).functor.obj M) := by
  exact ⟨p.choose_spec.2.choose_spec.2.choose,
    p.choose_spec.2.choose_spec.2.choose_spec.2⟩

/-- The section K-flat balancing isomorphism supplied by SectionPullNormalized.
Its representative square uses the ordinary conjugate of the identity on sections.
The final comparison equation uniquely determines this d: the section realization
is essentially surjective and every other factor is invertible. Thus this choice
selects the specified comparison, rather than an undetermined scalar isomorphism.
Source: Stacks 03EK, 07A6, 0D6D
(blueprint: lem-sfb-scalar-geometric-exchange-rectangle). -/
def sectionRectangleLambda (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : SectionScalarComparison φ U) (sV : SectionScalarComparison φ V)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (p : SectionPullNormalized φ h sU sV b) :
    sV.pair.derived ⋙ ModuleRingedComparison.derivedPullback Λ' h ≅
      ModuleRingedComparison.derivedPullback Λ h ⋙ sU.pair.derived :=
  (sectionRectangleLambda_witness φ h sU sV b p).choose
```

## Users

The read-only downstream.py --uses search found only the item module using
sectionRectangleLambda or sectionRectangleRho. The two downstream importers are
Sheaf.Paper.FlatCoefficientSquareNormalization (held by R9) and
Sheaf.Paper.InternalScalarMateProjection (held by J3); neither mentions either
map. The original public signatures and visibility remain verbatim. The local
lambda_section and rho_section proofs now use the extracted equation. No
consumer adaptation is necessary. No target statement changes its meaning.

## Status

landed 20261024T015051-L-2318376 2026-10-24 (merge of deliver/J6/Sheaf.Paper.ScalarGeometricExchangeRectangle)
