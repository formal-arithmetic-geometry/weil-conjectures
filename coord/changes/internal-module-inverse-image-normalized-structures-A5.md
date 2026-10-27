# CategoryTheory.InternalModuleInverseImage.directLax_existsUnique

## Reason

Prove the two remaining existence-and-uniqueness theorems for the canonical
lax direct image and braided inverse image. All new constructions and coherence
lemmas are private. No public signature, definition body, or mathematical meaning changes.
Four redundant public imports are removed: `Sheaf.CategoryTheory.SheafTensor`,
`Mathlib.Algebra.Category.Grp.FilteredColimits`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, and
`Mathlib.Algebra.Homology.DerivedCategory.Basic`; every interface used here is
available from the retained imports. The command-level interface gate may flag the new private
irreducibility attributes, section/omit/include commands, and transparency options;
this record explains their scope and the consumer audit.

## Old

```lean
set_option backward.isDefEq.respectTransparency false

theorem directLax_existsUnique :
    ∃! q : B.functor.LaxMonoidal, TensorNormalization K J f.direct B q := by
  sorry

theorem inverseBraided_existsUnique :
    ∃! q : A.functor.Braided,
      q.toMonoidal.toOplaxMonoidal = inverseOplax J K f A B adj ∧
      TensorNormalization J K f.inverse A q.toMonoidal.toLaxMonoidal := by
  sorry
```

## New

The two theorem signatures are verbatim identical and their proofs are complete.
`directLax_existsUnique` constructs `normalizedLax` and proves uniqueness with
`normalization_unique`. `inverseBraided_existsUnique` proves the mate maps are
invertible, uses `Functor.Monoidal.ofOplaxMonoidal`, proves braiding compatibility,
and obtains uniqueness from injectivity of the monoidal-to-oplax projection.

```lean
set_option backward.isDefEq.respectTransparency true
```

This elaborator option respects the irreducibility of the private constructions
`tensorLift`, `unitLift`, `transportedTensor`, `transportedUnit`,
`transportedPairing`, `transportedBilinear`, and `normalizedLax`, whose equations are used through
proved private lemmas. It prevents expanding full sheafification constructions
while checking tensor coherences. Scoped overrides retain the original elaboration
behavior in the existing `comparison_of_normalization` proof and in the few
private componentwise calculations that require it. The existing scoped heartbeat
limit is unchanged. No kernel-checking option is disabled.

The public definitions `directLax`, `inverseOplax`, `inverseBraided`,
`TensorNormalization`, `ComparisonStatement`, and `ComplexComparison` retain their
original bodies. Their chosen structures are still determined by the original
existence-and-uniqueness statements. No private helper appears in any public
signature or public definition body.

The existing private `terminalSource` is simplified to the inverse canonical
terminal comparison. Its old body was

```lean
private def terminalSource (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesFiniteProducts L] (V : Dᵒᵖ) :
    (L.obj (𝟙_ (Sheaf J (Type u)))).obj.obj V :=
  let h := (CartesianMonoidalCategory.isTerminalTensorUnit :
    IsTerminal (𝟙_ (Sheaf J (Type u)))).isTerminalObj L _
  (h.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit).inv.hom.app V PUnit.unit
```

and its new body is

```lean
private def terminalSource (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesFiniteProducts L] (V : Dᵒᵖ) :
    (L.obj (𝟙_ (Sheaf J (Type u)))).obj.obj V :=
  (inv (CartesianMonoidalCategory.terminalComparison L)).hom.app V PUnit.unit
```

Both are the unique section of the terminal sheaf `L.obj (𝟙_ _)`. The old
`uniqueUpToIso` construction caused repeated unfolding during ring/module comparison
elaboration; the direct inverse comparison removes that cost. This helper is private
and does not occur in any public statement or definition. The existing naturality
proof of the module comparison now composes four `CommSq`s before evaluation,
preserving the same component map. The private `sectionModuleIso` packages a
linear underlying isomorphism at the level of arbitrary module sheaves, and
`complexComparison_of_iso` proves the termwise and localization formulas for an
arbitrary natural isomorphism of zero-preserving functors. Their proofs are
complete; the existing comparison uses them with exactly its original maps.
Neither helper occurs in a public signature or definition body. Two additional
proved private graph-comparison lemmas share the ring/module additive and bilinear
transport calculations. The triple-tensor extensionality proof uses the monoidal
local-equivalence property of the sheafification unit. Right additivity is derived
from left additivity and the separately proved symmetry formula. These changes
remove repeated elaboration without changing the maps or their laws.

## Users

`tools/downstream.py Sheaf.CategoryTheory.InternalModuleInverseImageComparison
--uses CategoryTheory.InternalModuleInverseImage.directLax_existsUnique` finds ten
transitive importers (refreshed before delivery) and only this module as a textual user of the theorem.
All consumers retain precisely the same public interface and require no adaptation.
No other module is included in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.InternalModuleInverseImageComparison | A5 | Two proofs completed. |
| Sheaf.Paper.ContinuousAlgclScalarConstructibility | unclaimed | Identical public interface. |
| Sheaf.Paper.FiniteStageSupportedGeneration | unclaimed | Identical public interface. |
| Sheaf.Paper.FlatCoefficientSquareNormalization | R9 | Identical public interface. |
| Sheaf.Paper.InternalScalarMateProjection | J3 | Identical public interface. |
| Sheaf.Paper.InternalScalarMateTransitivity | J4 | Identical public interface. |
| Sheaf.Paper.InternalScalarPullbackNormalization | K2 | Identical public interface. |
| Sheaf.Paper.KummerStratumScalarMateDetection | unclaimed/rework | Identical public interface. |
| Sheaf.Paper.RestrictedCoefficientMateProjection | S7 | Identical public interface. |
| Sheaf.Paper.ScalarGeometricExchangeRectangle | J6 | Identical public interface. |
| Sheaf.Paper.StrictCompletionRestrictionComparison | F2 | Identical public interface. |

The final coherence proof derives the right-unit law from the left-unit law and
braiding, removing the duplicate right-unit section calculation and two unused
private tensor-unit helpers. All are internal proof changes.

The final mate graph calculation uses two proved private consequences of
TensorNormalization directly, avoiding the detour through equality of full lax
structures. The old private normalized_unit_graph lemma is consequently unused
and removed. No public declaration is removed.

Validation: the previous full file compiled cleanly in 47.5 seconds; the simplified
construction through inverseBraided_existsUnique compiled in 38.9 seconds.

## Status

landed 20261024T014404-L-2188990 2026-10-24 (merge of deliver/A5/Sheaf.CategoryTheory.InternalModuleInverseImageComparison)
