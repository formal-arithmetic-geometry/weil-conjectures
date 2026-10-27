# CategoryTheory.brownHypothesesFor_iff_compact_of_noetherian and brownHypotheses_of_finiteFieldDatum

## Reason

The smallness input requires only a compact locally Noetherian scheme. The existing
public compactness reduction unnecessarily restricts its usable geometric interface
to schemes of finite type over fields. Generalize the proved criterion to Noetherian
schemes, using the actual six-case admissibility predicate, and derive the existing
finite-type criterion from it without changing its signature.

The supported six-coefficient finite-field assembly was private and took an explicit
reordered disjunction. Expose a proved public specialization with the actual predicate
and an explicit structure morphism, for use by consumers whose field really comes
from a FiniteFieldDatum. This is an additional valid specialization, not a correction
or proof of the disputed arbitrary-field theorem.

## Old

Neither new public theorem existed. The unchanged finite-type criterion was proved
by extracting thickness and smallness directly from the private coefficient-case helper,
then applying brownHypothesesFor_iff. The finite-field assembly remains private with
exactly its former signature and proof.

## New

```lean
theorem brownHypothesesFor_iff_compact_of_noetherian
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    BrownHypothesesFor Λ X ↔
      ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
        letI := hSums
        ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
          (constantModelBoundedConstructible Λ X K.obj ∧
            DerivedCategory.finiteTorAmplitude _ K.obj) → IsCompactObject K
```

```lean
theorem brownHypotheses_of_finiteFieldDatum
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) {X : Scheme.{u}} (aX : X ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    BrownHypothesesFor Λ X
```

The finite-field proof installs the structure morphism and explicitly transfers its
three property instances from the corresponding hypotheses on `aX`.
Both declarations have complete proofs. Reordering a disjunction preserves all six
coefficient objects and their ring-object isomorphisms. The Noetherian criterion
asserts an equivalence, not compactness. The finite-field theorem uses exactly the
geometric field and hypotheses of the existing compactness theorem. The original
arbitrary-field theorem retains its signature, disputed warning and sole sorry.
All existing declarations, non-theorem bodies, visibility and imports are preserved.
The public finite-field signature requires the added public import
`Sheaf.Paper.FiniteFieldFiber`. A local instance priority selects the existing direct
sheaf braiding to avoid expensive comparison with the symmetric construction.
It changes no instance definition or exported attribute. No source-library module changes.

## Users

The source audit with downstream.py finds 403 transitive downstream modules and
three direct importers. Searching for the two newly introduced names finds no
existing external uses. No existing public interface changes, so none of those
consumers needs adaptation or has a changed statement. The existing finite-type
criterion keeps its full signature; its only uses are internal to the item.
In particular the three original Brown callers remain unchanged and continue to
expose the disputed arbitrary-field hole. Their parent nodes and dependencies are
not withdrawn or replaced by the finite-field specialization.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctorsBasics.BrownHypotheses | W4 | Add two proved public theorems; reuse the Noetherian criterion in the existing finite-type proof. |
| Sheaf.Paper.BrownExceptionalAdjoint | no current local claim found | Existing Brown theorem call and statement unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | no current local claim found | Existing Brown theorem call and statement unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | no current local claim found | Existing Brown theorem calls and statement unchanged; no adaptation. |

## Status

landed 20261025T101812-L-3737682 2026-10-25 (merge of deliver/W4/Sheaf.SixFunctorsBasics.BrownHypotheses)
