# SheafOfModules.exists_pullback_adapted_flat_resolution

## Reason

The existing public theorem keeps exactly its original signature and public imports.
The proof adds private helpers, section variables, local notation and local instance
registrations. The interface checker conservatively records those command changes.
This record documents their scope; no definition or statement used by an importer changes.
The second reader removed the unnecessary public construction theorem and its
unlanded node; the existing theorem now directly instantiates the proved source
resolution and colimit-presentation API. All added imports are proof-only, and
all original public imports are unchanged.

## Old

The commands outside declarations were:

```lean
@[expose] public section
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits
```

## New

The commands outside declarations are:

```lean
@[expose] public section
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] {JC : GrothendieckTopology C} {JD : GrothendieckTopology D} {R : Sheaf JC CommRingCat.{w}} {RI : Sheaf JD CommRingCat.{w}} {L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w)}
universe u v r
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
open CategoryTheory.Functor MonoidalCategory
open scoped ZeroObject
local notation "O" => (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
local notation "A" => SheafOfModules.{r} O
attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory symmetricCategory
attribute [local instance] tensorPreadditive_adapted
attribute [local instance] tensorLeftColimits_adapted tensorRightColimits_adapted hasExactColimits_int_adapted
attribute [local instance] all_tensorLeftColimits_adapted all_tensorRightColimits_adapted
attribute [local instance] hasTensor_adapted hasGoodTensor₁₂_adapted hasGoodTensor₂₃_adapted hasTensor₄_adapted
```

All added helper declarations are private and proved. The returned duplicate
`changeOfRings_eq_ofUniverses_adapted` has been removed; its former use is
handled directly by definitional conversion at the flat-pullback call. The
same equality in `Sheaf.Paper.KFlatRingedToposPullback` is private, and importing
that downstream module would create a cycle. All added instance registrations
are local to helper sections. The public theorem installs its instances with
local `let` and `have` bindings. No new public statement or global instance is
introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedToposAdaptedFlatResolution | F4 | Private proof support and a complete proof; existing signature, public definitions, visibility and public imports unchanged. |

No existing signature or public definition changes, so no downstream adaptation is
required and no target changes meaning.

## Status

landed 20261016T082348-L-1528841 2026-10-16 (merge of deliver/F4/Sheaf.Algebra.Homology.RingedToposAdaptedFlatResolution)
