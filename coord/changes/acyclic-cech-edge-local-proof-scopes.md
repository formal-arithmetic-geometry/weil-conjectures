# Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility local proof scopes

## Reason

The stage-3 static interface checker includes section variables, `include`/`omit`,
and local attributes in its interface fingerprint. This delivery adds these commands
for private comparison helpers and to prevent unfolding the sectionwise bicomplex
during proof elaboration. The change record documents that conservative interface
flag; no public declaration signature, public definition, public import, or exported
instance/attribute is changed. All helpers are private and proved.

The new variables are inside `Comparison`, `SiteChange`,
`SiteChangeResolutions`, `ForgetModules`, and `ForgetComparison` sections.
The irreducibility attributes are explicitly local, within closed proof sections.
The baseline global instance attribute remains identical. The scoped linter option
on the two compatibility declarations preserves original named proof binders that
are unused in their conclusions. It does not affect importers.

## Old

No statement or definition changes. The old non-declaration commands recorded by
the interface checker, verbatim apart from whitespace normalization, are:

```lean
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
attribute [instance] SheafOfModules.isGrothendieckAbelian
```

## New

The new non-declaration commands recorded by the same checker are:

```lean
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
attribute [instance] SheafOfModules.isGrothendieckAbelian
variable {C : Type u} [SmallCategory C] {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom) {E : Type*} [Category E] [Abelian E] [EnoughInjectives E] (P : E ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u}) [P.Additive]
omit [EnoughInjectives E] in
omit [EnoughInjectives E] in
omit [EnoughInjectives E] in
omit [EnoughInjectives E] in
omit [EnoughInjectives E] in
attribute [local irreducible] SiteCechComplex.resolutionDoubleComplex SiteCechComplex.alpha SiteCechComplex.beta
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (u : C ⥤ D) {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom) (S' : SiteCechComplex (fun t ↦ u.obj (f t)) (fun t ↦ u.map (hom t))) (c : ∀ (p : ℕ) (t : Fin (p + 1) → T), u.obj (S.W p t) ≅ S'.W p t) (hcpr : ∀ (p : ℕ) (t : Fin (p + 1) → T) (k : Fin (p + 1)), (c p t).hom ≫ S'.pr p t k = u.map (S.pr p t k))
include hcpr in
include hcpr in
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D) [u.IsContinuous J K] {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom) (S' : SiteCechComplex (fun t ↦ u.obj (f t)) (fun t ↦ u.map (hom t))) (c : ∀ (p : ℕ) (t : Fin (p + 1) → T), u.obj (S.W p t) ≅ S'.W p t) (hcpr : ∀ (p : ℕ) (t : Fin (p + 1) → T) (k : Fin (p + 1)), (c p t).hom ≫ S'.pr p t k = u.map (S.pr p t k)) {A : Sheaf J AddCommGrpCat.{u}} {B : Sheaf K AddCommGrpCat.{u}} (I : InjectiveResolution A) (L : InjectiveResolution B) (v : I.cocomplex ⟶ ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).mapHomologicalComplex (.up ℕ)).obj L.cocomplex)
include hcpr in
include hcpr in
attribute [local irreducible] SiteCechComplex.resolutionDoubleComplex SiteCechComplex.alpha SiteCechComplex.beta
variable {C : Type u} [SmallCategory C] (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks] (R : Sheaf J.toGrothendieck RingCat.{u}) {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U} (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
include hcover in
variable {C : Type u} [SmallCategory C] (J : Precoverage C) {E : Type*} [Category* E] [Abelian E] (Q : E ⥤ Sheaf J.toGrothendieck AddCommGrpCat.{u}) [Q.Additive] {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom)
variable {M : E} (I : InjectiveResolution M) (L : InjectiveResolution (Q.obj M)) (k : (Q.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ L.cocomplex)
variable [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
variable [EnoughInjectives E]
attribute [local irreducible] SiteCechComplex.resolutionDoubleComplex SiteCechComplex.alpha SiteCechComplex.beta
attribute [local irreducible] SiteCechComplex.resolutionDoubleComplex SiteCechComplex.alpha SiteCechComplex.beta
```

Every original public signature was compared after whitespace normalization and
is identical. Every original public import is preserved. The only new definitions
are private, explicit constructions of the actual cochain and total maps; none has
a proof gap. No public definition uses a private helper.

## Users

`tools/downstream.py` lists the following ten transitive importers. Each sees the
same public statements, definitions, imports and global attributes. There is no
consumer adaptation and no need to take or alter a consumer's claim. Holder status
is therefore not queried; this delivery changes none of their files.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison | not queried; no adaptation | same public interface; no edit |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | not queried; no adaptation | same public interface; no edit |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | not queried; no adaptation | same public interface; no edit |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | not queried; no adaptation | same public interface; no edit |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | not queried; no adaptation | same public interface; no edit |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | not queried; no adaptation | same public interface; no edit |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | not queried; no adaptation | same public interface; no edit |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | not queried; no adaptation | same public interface; no edit |
| Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback | not queried; no adaptation | same public interface; no edit |
| Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages | not queried; no adaptation | same public interface; no edit |

All three public signatures are unchanged, and no consumer can name the new private
helpers. The textual downstream search for the changed-command fingerprint reports
no named declaration change. The independent reader can verify the section endings
and `[local irreducible]` scopes directly; no forced-adaptation claim is made.

## Status

landed 20261018T071222-L-1677272 2026-10-18 (merge of deliver/S3/Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility)
