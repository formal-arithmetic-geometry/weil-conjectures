# FixedOrbitData and the explicit split-label action

## Reason
The geometric statement needs actual orbit representatives, not arbitrary m and K. Construct the induced action by explicit deck maps, pulled-back sections and evaluation of their labels at the zero prime. The action-law theorem supplies proofs only, not arbitrary data chosen from an unproved existence theorem.

## Old
FixedOrbitData, fixedOrbitData_of_action and the AffineTorsorSplitAction module are absent from the repository base. The original geometric theorem accepts arbitrary m and K; its full signature is in the accompanying geometric change record.

## New
```lean
structure FixedOrbitData (G : Type u) [Group G] (d : ℕ) where
  action : G →* Equiv.Perm (Fin d)
  rel : Fin d → Fin d → Prop
  rel_spec : ∀ x y, rel x y ↔ ∃ g, action g x = y
  m : ℕ
  representative : Fin m → Fin d
  stabilizer : Fin m → Subgroup G
  complete : ∀ x, ∃ i, rel (representative i) x
  distinct : ∀ i j, rel (representative i) (representative j) → i = j
  stabilizer_spec : ∀ i g, g ∈ stabilizer i ↔ action g (representative i) = representative i
```

fixedOrbitData_of_action proves existence of this data from a supplied permutation action by the finite quotient and Mathlib stabilizers. AffineTorsorSplitAction constructs fixedPunctureDeck, fixedPunctureGeneric, fixedSplitSection, fixedSplitLabel, fixedPunctureLabel and fixedPunctureDescentAction explicitly. Only fixedPunctureLabel_laws is postponed, as a named sourced theorem with a full proof in words. The geometric theorem requires D.action to equal this explicit action.

## Users
| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentGeometric` | D3 | defines FixedOrbitData and uses the induced action in its public statement |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction` | D3 | new module; no existing callers or signatures |

These are new declarations, absent from every existing target signature. Their underlying data are real constructions; no definition selects arbitrary data from an unproved existence theorem.

## Status
landed 20261013T222400-L-1221588 2026-10-13 (merge of deliver/D3/Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentGeometric)
