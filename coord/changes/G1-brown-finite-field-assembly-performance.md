# CategoryTheory.brownHypotheses_of_finiteFieldDatum

## Reason

The restored item exceeded the single-file compile limit (65.5 seconds on the
unchanged archived source). Eliminate the redundant private finite-field assembly
and its two conversions between differently ordered coefficient disjunctions.
Use the existing Noetherian criterion and finite-field objectwise compactness theorem
with the original admissibility hypothesis. Replace the private custom direct-sum
compactness transport calculation with the existing IsCompactObject/IsCompactObj
comparison and IsCompactObj.of_iso. Its private helper now only needs the matching
Hom/coproduct indexing universe used by its sole call site.

Every public signature, public import, definition body and attribute stays unchanged.
The disputed arbitrary-field Brown theorem and its hole stay unchanged. This is a
performance repair of the listed rework item, not a claimed proof of that theorem.

## Old

```lean
theorem brownHypotheses_of_finiteFieldDatum
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) {X : Scheme.{u}} (aX : X ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    BrownHypothesesFor Λ X := by
  apply @brownHypotheses_finiteIntermediateField D ℓ _ hℓ X ⟨aX⟩
    ‹IsSeparated aX› ‹LocallyOfFiniteType aX› ‹QuasiCompact aX› Λ _ _
  unfold IsLocalizingAdmissibleCoefficient at hΛ
  rcases hΛ with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
```

The private brownHypotheses_finiteIntermediateField helper additionally restated the
six coefficient alternatives and converted them back to the admissibility predicate.
Its only caller was the public theorem above; it is removed. The private compact_of_iso
used a direct-sum comparison calculation instead of the existing compactness API.

## New

```lean
theorem brownHypotheses_of_finiteFieldDatum
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) {X : Scheme.{u}} (aX : X ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    BrownHypothesesFor Λ X := by
  let _ : X.Over (Spec (.of D.k)) := ⟨aX⟩
  let _ : IsSeparated (X ↘ Spec (.of D.k)) := ‹IsSeparated aX›
  let _ : LocallyOfFiniteType (X ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType aX›
  let _ : QuasiCompact (X ↘ Spec (.of D.k)) := ‹QuasiCompact aX›
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  obtain ⟨_, htri, _, _, hcop, _⟩ := brownHypotheses_structural Λ X
  let _ := htri
  exact (brownHypothesesFor_iff_compact_of_noetherian ℓ X Λ hΛ).mpr
    ⟨hcop, fun K hK ↦
      brownHypotheses_finiteField_object_compactness D ℓ hℓ X Λ hΛ hcop K hK⟩
```

The private compact_of_iso proof now uses isCompactObject_iff_isCompactObj and
BrownRepresentability.IsCompactObj.of_iso; its Hom universe agrees with the coproduct
universe. There are no external references to either private helper (source search in
lean/ and quarantine/). No public API or target meaning changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctorsBasics.BrownHypotheses | G1 | Proof simplification; public interface identical. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not queried; no adaptation | Direct importer; same public declarations and instances. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not queried; no adaptation | Direct importer; same public declarations and instances. |

No existing module besides the item is modified. Named private-helper searches found
no external users, including among quarantined sources. The two direct importers need
no adaptation because their imported interface and all definitions are identical.

## Status

landed 20261027T084410-L-3676409 2026-10-27 (merge of deliver/G1/Sheaf.SixFunctorsBasics.BrownHypotheses)
