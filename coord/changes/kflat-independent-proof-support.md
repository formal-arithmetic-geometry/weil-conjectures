# CochainComplex.exists_isKFlatResolutionIndependentCoefficients

## Reason

The interface checker conservatively records changes to commands outside declarations.
The proof needs private helper declarations with section variables, local notation, local
instances, namespace openings, and a local instance-search size option. There is no
change to any existing public signature, definition, visibility, or public import.
This record makes the command changes reviewable. All new declarations are private
and fully proved. The three new smallness instances have local registrations. No other module needs adaptation.

## Old

The command fingerprint outside declarations was:

```lean
@[expose] public section
universe r u v
open CategoryTheory
```

The public theorem has exactly the same signature before and after this delivery.
Its old proof was `by sorry`.

## New

The command fingerprint outside declarations is:

```lean
@[expose] public section
universe r u v w
open CategoryTheory MonoidalCategory Limits Opposite
open scoped ZeroObject
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}} {M P N : PresheafOfModules.{r} (R ⋙ forget₂ _ _)}
omit [EssentiallySmall.{r} C] in
variable (M) in
omit [EssentiallySmall.{r} C] in
omit [EssentiallySmall.{r} C] in
omit [EssentiallySmall.{r} C] in
omit [EssentiallySmall.{r} C] in
omit [EssentiallySmall.{r} C] in
variable (M N) in
omit [EssentiallySmall.{r} C] in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
local notation "𝓢" => PresheafOfModules.sheafification.{r} (𝟙 (𝓡).obj)
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] {R : Sheaf J CommRingCat.{r}} [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory symmetricCategory
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
local notation "O" => (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
local notation "A" => SheafOfModules.{r} O
attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory symmetricCategory monoidalClosed_kfi
```

The theorem's complete proof and all helpers are in
`lean/Sheaf/Algebra/Homology/KFlatResolutionIndependentCoefficients.lean`.
The helper notation and attributes are local. The smallness helpers
`small_hom_kfi`, `essentiallySmall_over_kfi`, and `small_homObj_kfi` are
`private local instance` declarations, so they do not add global instance registrations. The extra universe is used only by the
private generic shrinking construction; it does not occur in the public theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients | J2 | Private proof support and complete proof; existing public signature unchanged. |

No declaration has a changed signature or definition, so there are no changed-name
users to adapt. In particular, the conservative command-fingerprint change does not
alter the statement or meaning of any target.

## Status

landed 20261016T054837-L-157689 2026-10-16 (merge of deliver/J2/Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients)
