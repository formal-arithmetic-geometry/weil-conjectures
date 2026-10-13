# AlgebraicGeometry.Scheme.Modules.affine_pushout_ring_section_presentation

## Reason

The existing declaration begins with one leading space. leanindex.commands consequently
parses it and its proof as a continuation of the preceding local notation e₀, rather than
as a theorem. Replacing its sorry therefore triggers the conservative interface-change
check for "commands such as variable, open, notation or attribute". The theorem keyword
is now at column zero, following the project's command layout convention. This fixes
the declaration boundary for readers and the parser; no Lean signature, visibility,
notation, option, instance, attribute or public import changes.

This record reports the parser misclassification to the reviewer, rather than editing
or bypassing the tool. The static interface flag compares the old misparsed notation
with the properly delimited notation and theorem. The semantic interface is unchanged.

## Old

```lean
 theorem affine_pushout_ring_section_presentation [IsAffineHom f] (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B) (ε : B ⟶ U.sheaf) (hring : IsPushout r₀ t₀ b t ∧ b ≫ ε = 𝟙 U.sheaf ∧ t ≫ ε = e₀) (V : X.Opens) (hV : IsAffineOpen V) : letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra ∃ δ : Γ(U, f ⁻¹ᵁ V) →+* B.obj.obj (op (f ⁻¹ᵁ V)), (∀ c, (ε.hom.app (op (f ⁻¹ᵁ V))).hom (δ c) = c) ∧ (∀ r : B.obj.obj (op (f ⁻¹ᵁ V)), ∃ l : List (Γ(U, f ⁻¹ᵁ V) × Γ(U, f ⁻¹ᵁ V)), r = (l.map fun x ↦ (b.hom.app (op (f ⁻¹ᵁ V))).hom x.1 * δ x.2).sum)
```

## New

```lean
theorem affine_pushout_ring_section_presentation [IsAffineHom f] (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B) (ε : B ⟶ U.sheaf) (hring : IsPushout r₀ t₀ b t ∧ b ≫ ε = 𝟙 U.sheaf ∧ t ≫ ε = e₀) (V : X.Opens) (hV : IsAffineOpen V) : letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra ∃ δ : Γ(U, f ⁻¹ᵁ V) →+* B.obj.obj (op (f ⁻¹ᵁ V)), (∀ c, (ε.hom.app (op (f ⁻¹ᵁ V))).hom (δ c) = c) ∧ (∀ r : B.obj.obj (op (f ⁻¹ᵁ V)), ∃ l : List (Γ(U, f ⁻¹ᵁ V) × Γ(U, f ⁻¹ᵁ V)), r = (l.map fun x ↦ (b.hom.app (op (f ⁻¹ᵁ V))).hom x.1 * δ x.2).sum)
```

Only the initial theorem-keyword indentation differs; both signatures are identical
when whitespace is normalized. The proof body is the direct counit, tensor-pushout
comparison and finite-list induction delivered with this record.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffinePushoutRingSectionPresentation | D3 | Proof and keyword indentation only; same signature and exports. |
| Sheaf.AlgebraicGeometry.AffinePushoutFirstTensorSections | unclaimed | Calls the same declaration with the same type; no adaptation. |

The downstream tool reports these two textual uses (including the declaration's own
module). It also reports 413 transitive downstream modules; all see the same public
signature and imports. No downstream module is adapted in this delivery.

## Status

landed 20261013T000423-L-2252069 2026-10-13 (merge of deliver/D3/Sheaf.AlgebraicGeometry.AffinePushoutRingSectionPresentation)
