# CategoryTheory.ringFamilySheafModel_cech

## Reason

Restore the reverted V6 scalar-extension proof and its three supporting modules from
coord/repair-notes/Sheaf.Paper.FunctorialRingComplexCechComparison.json, preserving
the original module and node names. The repair request records a downstream
universe-inference failure in Sheaf.Paper.WeilTensorProduct. That consumer is checked
against the restored packet in addition to compilation of every delivered module.

No existing statement, definition, public import, universe binder or target changes.
Proofs in WeilTensorProduct are also adapted at the expensive instance conversions:
its opposite-additivity instance search is replaced by its explicit map-add equation;
the rational tensor bilinearity and presentation-completion proofs construct the
required structures from their existing map laws and equivalence instances.
The theorem's existing public interface stays verbatim. The supporting constructions
are the concrete constant-presheaf, scalar-extension and sheafification constructions
of the archived packet, with complete data definitions and two named proof obligations.

## Old

```lean
theorem ringFamilySheafModel_cech
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (m : RingComplexMaps (fun A I ↦ ringComplexGodement A I.val))
    (hm : RingComplexFunctorial (fun A I ↦ ringComplexGodement A I.val)
      (fun A I ↦ ringComplexGodementAugmentation A I.val) m)
    (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ∃ e : DerivedCategory.Q.obj (ringedExtendedCech O r f).1 ≅
        DerivedCategory.Q.obj
          (ringFamilySheafModel O (fun A I ↦ ringComplexGodement A I.val)
            (fun A I ↦ ringComplexGodementAugmentation A I.val) m hm r f).1,
      e.hom ≫ DerivedCategory.Q.map
          (ringFamilySheafModel O (fun A I ↦ ringComplexGodement A I.val)
            (fun A I ↦ ringComplexGodementAugmentation A I.val) m hm r f).2 =
        DerivedCategory.Q.map (ringedExtendedCech O r f).2 := by sorry
```

## New

The signature above and all public imports are identical. Replace only the proof
with the archived complete assembly:
resolve the global Godement complex, apply the two augmented scalar comparisons,
compose the resulting derived isomorphisms and calculate their augmentation.
The proof privately imports GlobalSectionRingFamilyBaseChange and
GlobalSectionScalarCechModel. Neither supporting module is publicly re-exported.

The archived V6 packet was restored with its original module and node identifiers.
The assigned theorem and the two supporting split statements compile. The archived
WeilTensorProduct universe error no longer reproduces in a statement probe; its full
source remains an unchanged downstream performance issue and is outside this delivery.

ExtendedCechCompletionModel exceeds the single-file limit unchanged at 62.2 seconds.
The private compose_three_squares helper below replaces only the concrete rewrite chain
in completion_unit_natural. It preserves all public declarations and compiles in 42.9
seconds.

## Users

The only textual consumer of ringFamilySheafModel_cech outside its own module is
Sheaf.Paper.ExtendedCechCompletionModel. The independent recorded failing importer
is checked in addition to this direct interface consumer. The target meaning does
not change; all existing statement definitions remain identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FunctorialRingComplexCechComparison | X7 | Restore the proof; unchanged interface. |
| Sheaf.Paper.ExtendedCechCompletionModel | unclaimed | Generic private naturality calculation reduces compile time. |
| Sheaf.Paper.WeilTensorProduct | unclaimed | Private additive proof avoids expensive instance search. |

## Status

landed 20261026T003226-L-155006 2026-10-26 (merge of deliver/X7/Sheaf.Paper.FunctorialRingComplexCechComparison)
