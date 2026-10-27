# WeilConjectures.PurityFiniteSetting.SectionIntegration.normalIntegration

## Reason

The normal-bundle factor must be stated independently of the theorem that composes
it with DNC specialization. Its existing definition in SectionDncIntegrationSquare
would create an import cycle for those prerequisites. Move only this definition to
NormalSectionIntegrationData, and reexport that module from the old module. The
signature, construction, visibility, namespace and implicit arguments are identical.
The existing public imports of the item remain. This is a dependency relocation,
not a change to a mathematical object or a response to a compile-time limit.

## Old

In `Sheaf.Paper.SectionDncIntegrationSquare`:

```lean
def normalIntegration (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (X : Pair B d) :
    Dnc.normalSection P d X.g aB X.s X.section_eq ≅ P.diagonalTwist B d := by
  letI := P.noetherian aB
  letI := SmoothOfRelativeDimension.smooth d X.g
  letI := Dnc.compactifiable P X.g aB
  letI := Etale.FiniteRingSectionDeformation.geometry d X.g X.s X.section_eq
  let F := ConormalGradedAlgebra.piece X.s 1
  let q := Etale.FiniteSmoothPurity.reesConeComparison X.s
  let c := Etale.FiniteRingSectionDeformation.coneBundleIso d X.g X.s
  let e := q ≪≫ c
  let π := Scheme.Hom.normalConeProj X.g X.s
  let πF := VectorBundleZeroSection.π B d F
  let z := X.s.normalConeZeroSection
  let zF := VectorBundleZeroSection.zero B d F
  letI := (Etale.vectorIntegration_geometry B d F).1
  letI := (Etale.vectorIntegration_geometry B d F).2.1
  letI := Dnc.compactifiable P πF aB
  letI := P.noetherian (πF ≫ aB)
  have hp : e.hom ≫ πF = π := by
    dsimp [e, πF, F]
    rw [Category.assoc,
      (Etale.FiniteRingSectionDeformation.coneBundleIso_spec d X.g X.s X.section_eq).1,
      (Etale.FiniteSmoothPurity.reesConeComparison_spec X.s).1,
      Scheme.Hom.purityNormalProjection_eq X.s X.g X.section_eq]
  have hz : z ≫ e.hom = zF := by
    dsimp [e, z, zF, F]
    rw [← Category.assoc, (Etale.FiniteSmoothPurity.reesConeComparison_spec X.s).2.1,
      (Etale.FiniteRingSectionDeformation.coneBundleIso_spec d X.g X.s X.section_eq).2]
  have wp : e.inv ≫ π = πF := by
    rw [← hp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have wz : zF ≫ e.inv = z := by
    rw [← hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact Dnc.normalComparison P d X.g aB X.s X.section_eq ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
      (P.chartSectionEtaleRestriction N e.inv π πF wp z zF wz ≪≫
        Etale.FiniteRingSectionDeformation.bundleOrientation P.diagonalExponent
          (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
          P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F)
```

## New

In `Sheaf.Paper.NormalSectionIntegrationData`, reexported by
`Sheaf.Paper.SectionDncIntegrationSquare`:

```lean
def normalIntegration (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (X : Pair B d) :
    Dnc.normalSection P d X.g aB X.s X.section_eq ≅ P.diagonalTwist B d := by
  letI := P.noetherian aB
  letI := SmoothOfRelativeDimension.smooth d X.g
  letI := Dnc.compactifiable P X.g aB
  letI := Etale.FiniteRingSectionDeformation.geometry d X.g X.s X.section_eq
  let F := ConormalGradedAlgebra.piece X.s 1
  let q := Etale.FiniteSmoothPurity.reesConeComparison X.s
  let c := Etale.FiniteRingSectionDeformation.coneBundleIso d X.g X.s
  let e := q ≪≫ c
  let π := Scheme.Hom.normalConeProj X.g X.s
  let πF := VectorBundleZeroSection.π B d F
  let z := X.s.normalConeZeroSection
  let zF := VectorBundleZeroSection.zero B d F
  letI := (Etale.vectorIntegration_geometry B d F).1
  letI := (Etale.vectorIntegration_geometry B d F).2.1
  letI := Dnc.compactifiable P πF aB
  letI := P.noetherian (πF ≫ aB)
  have hp : e.hom ≫ πF = π := by
    dsimp [e, πF, F]
    rw [Category.assoc,
      (Etale.FiniteRingSectionDeformation.coneBundleIso_spec d X.g X.s X.section_eq).1,
      (Etale.FiniteSmoothPurity.reesConeComparison_spec X.s).1,
      Scheme.Hom.purityNormalProjection_eq X.s X.g X.section_eq]
  have hz : z ≫ e.hom = zF := by
    dsimp [e, z, zF, F]
    rw [← Category.assoc, (Etale.FiniteSmoothPurity.reesConeComparison_spec X.s).2.1,
      (Etale.FiniteRingSectionDeformation.coneBundleIso_spec d X.g X.s X.section_eq).2]
  have wp : e.inv ≫ π = πF := by
    rw [← hp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have wz : zF ≫ e.inv = z := by
    rw [← hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact Dnc.normalComparison P d X.g aB X.s X.section_eq ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
      (P.chartSectionEtaleRestriction N e.inv π πF wp z zF wz ≪≫
        Etale.FiniteRingSectionDeformation.bundleOrientation P.diagonalExponent
          (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
          P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F)
```

## Users

`python3 tools/downstream.py Sheaf.Paper.SectionDncIntegrationSquare --uses
WeilConjectures.PurityFiniteSetting.SectionIntegration.normalIntegration`
reported zero downstream modules and two local uses in the item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SectionDncIntegrationSquare | N3 | Reexports the unchanged definition; psi and the two theorem signatures keep exactly the same meaning. |
| Sheaf.Paper.NormalSectionIntegrationData | new, N3 | Owns the unchanged construction. |
| Sheaf.Paper.NormalSectionIntegrationBaseChange | new, N3 | States naturality of the normal factor only. |
| Sheaf.Paper.NormalSectionIntegrationOrientation | new, N3 | States identification of the normal factor only. |

No target signature or definition value changes. The item's DAG statement is
unchanged. Its statement dependencies acquire the new definition-ownership node,
and its Lean ownership record drops only the relocated declaration. No other
module requires adaptation. The independent review should check the verbatim body
and reexport, and confirm that the new prerequisites do not import the item.

## Status

landed 20261025T202646-L-2739006 2026-10-25 (merge of deliver/N3/Sheaf.Paper.SectionDncIntegrationSquare)
