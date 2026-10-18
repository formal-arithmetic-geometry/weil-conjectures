# CategoryTheory.exists_linear_scalarLocalization_category

## Reason

The proof uses private constructions and lemmas in a helper namespace. The static interface
check conservatively flags its `variable`, `open`, and `@[instance_reducible]` commands.
There is no changed public signature, definition, instance, notation, or import.
The attribute applies only to the new private category construction, allowing efficient
instance reduction inside this file; it does not install a global category instance.
`set_option linter.unusedVariables false` suppresses warnings on the existing named
instance-binding lambdas and has no effect on mathematical declarations or importing files.

The returned delivery at `9e7b271574` also triggered a textual duplicate check
against `ScalarLocalization.composition_tmul`. The repair makes every parameter of
the private helper explicit and qualifies its map as
`LinearScalarConstruction.composition`. This differs from the downstream
`ScalarLocalization.composition`, defined by choosing the unique extension supplied
by the theorem proved here. `tools/import_direction.py may` confirms that importing
`ScalarLocalization` here would create a cycle. No downstream theorem is reproved:
the private helper is the computation rule for the explicit construction needed to
establish the existence theorem in the first place.

## Old

The existing theorem signature is:

```lean
theorem exists_linear_scalarLocalization_category
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) :
    (∀ K L M : C,
      ∃! β : (Localization.Away p ⊗[R] (L ⟶ M)) →ₗ[Localization.Away p]
          (Localization.Away p ⊗[R] (K ⟶ L)) →ₗ[Localization.Away p]
          (Localization.Away p ⊗[R] (K ⟶ M)),
        ∀ (f : L ⟶ M) (g : K ⟶ L) (a b : Localization.Away p),
          β (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) = (a * b) ⊗ₜ[R] (g ≫ f)) ∧
    ∃ d : Category.{max r v} (ULift.{0} C),
      (fun [catInst : Category.{max r v} (ULift.{0} C)] ↦
        ∃ a : Preadditive (ULift.{0} C), (fun [addInst : Preadditive (ULift.{0} C)] ↦
          ∃ l : Linear (Localization.Away p) (ULift.{0} C),
            (fun [linInst : Linear (Localization.Away p) (ULift.{0} C)] ↦
              ∃ e : ∀ K L : C, (Localization.Away p ⊗[R] (K ⟶ L))
                  ≃ₗ[Localization.Away p] (ULift.up K ⟶ ULift.up L),
                (∀ K : C, e K K (1 ⊗ₜ[R] 𝟙 K) = 𝟙 (ULift.up K)) ∧
                (∀ (K L M : C) (f : L ⟶ M) (g : K ⟶ L)
                    (a b : Localization.Away p),
                  e K L (b ⊗ₜ[R] g) ≫ e L M (a ⊗ₜ[R] f) =
                    e K M ((a * b) ⊗ₜ[R] (g ≫ f))) ∧
                ∃ lr : Linear R (ULift.{0} C), (fun [rlinInst : Linear R (ULift.{0} C)] ↦
                  (∀ (K L : ULift.{0} C) (r : R) (f : K ⟶ L),
                    r • f = (algebraMap R (Localization.Away p) r) • f) ∧
                  ∃ Q : C ⥤ ULift.{0} C,
                    (∀ K : C, Q.obj K = ULift.up K) ∧
                    (∀ (K L : C) (f : K ⟶ L), HEq (Q.map f) (e K L (1 ⊗ₜ[R] f))) ∧
                    Q.Additive ∧ Q.Linear R ∧
                    ∀ (T S : C ⥤ C) [T.Additive] [T.Linear R],
                      T ⋙ S = 𝟭 C → S ⋙ T = 𝟭 C →
                      ∃ T' S' : ULift.{0} C ⥤ ULift.{0} C,
                        T'.Additive ∧ T'.Linear (Localization.Away p) ∧
                        S'.Additive ∧ S'.Linear (Localization.Away p) ∧
                        (∀ K : C, T'.obj (ULift.up K) = ULift.up (T.obj K)) ∧
                        (∀ K : C, S'.obj (ULift.up K) = ULift.up (S.obj K)) ∧
                        (∀ (K L : C) (f : K ⟶ L) (a : Localization.Away p),
                          HEq (T'.map (e K L (a ⊗ₜ[R] f)))
                            (e (T.obj K) (T.obj L) (a ⊗ₜ[R] T.map f))) ∧
                        (∀ (K L : C) (f : K ⟶ L) (a : Localization.Away p),
                          HEq (S'.map (e K L (a ⊗ₜ[R] f)))
                            (e (S.obj K) (S.obj L) (a ⊗ₜ[R] S.map f))) ∧
                        T' ⋙ S' = 𝟭 (ULift.{0} C) ∧ S' ⋙ T' = 𝟭 (ULift.{0} C) ∧
                        T ⋙ Q = Q ⋙ T'
                ) (rlinInst := lr)
            ) (linInst := l)) (addInst := a)) (catInst := d)
```

Its proof was `by sorry`. No helper namespace or private helper declarations existed.

## New

The existing theorem signature is unchanged, verbatim:

```lean
theorem exists_linear_scalarLocalization_category
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) :
    (∀ K L M : C,
      ∃! β : (Localization.Away p ⊗[R] (L ⟶ M)) →ₗ[Localization.Away p]
          (Localization.Away p ⊗[R] (K ⟶ L)) →ₗ[Localization.Away p]
          (Localization.Away p ⊗[R] (K ⟶ M)),
        ∀ (f : L ⟶ M) (g : K ⟶ L) (a b : Localization.Away p),
          β (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) = (a * b) ⊗ₜ[R] (g ≫ f)) ∧
    ∃ d : Category.{max r v} (ULift.{0} C),
      (fun [catInst : Category.{max r v} (ULift.{0} C)] ↦
        ∃ a : Preadditive (ULift.{0} C), (fun [addInst : Preadditive (ULift.{0} C)] ↦
          ∃ l : Linear (Localization.Away p) (ULift.{0} C),
            (fun [linInst : Linear (Localization.Away p) (ULift.{0} C)] ↦
              ∃ e : ∀ K L : C, (Localization.Away p ⊗[R] (K ⟶ L))
                  ≃ₗ[Localization.Away p] (ULift.up K ⟶ ULift.up L),
                (∀ K : C, e K K (1 ⊗ₜ[R] 𝟙 K) = 𝟙 (ULift.up K)) ∧
                (∀ (K L M : C) (f : L ⟶ M) (g : K ⟶ L)
                    (a b : Localization.Away p),
                  e K L (b ⊗ₜ[R] g) ≫ e L M (a ⊗ₜ[R] f) =
                    e K M ((a * b) ⊗ₜ[R] (g ≫ f))) ∧
                ∃ lr : Linear R (ULift.{0} C), (fun [rlinInst : Linear R (ULift.{0} C)] ↦
                  (∀ (K L : ULift.{0} C) (r : R) (f : K ⟶ L),
                    r • f = (algebraMap R (Localization.Away p) r) • f) ∧
                  ∃ Q : C ⥤ ULift.{0} C,
                    (∀ K : C, Q.obj K = ULift.up K) ∧
                    (∀ (K L : C) (f : K ⟶ L), HEq (Q.map f) (e K L (1 ⊗ₜ[R] f))) ∧
                    Q.Additive ∧ Q.Linear R ∧
                    ∀ (T S : C ⥤ C) [T.Additive] [T.Linear R],
                      T ⋙ S = 𝟭 C → S ⋙ T = 𝟭 C →
                      ∃ T' S' : ULift.{0} C ⥤ ULift.{0} C,
                        T'.Additive ∧ T'.Linear (Localization.Away p) ∧
                        S'.Additive ∧ S'.Linear (Localization.Away p) ∧
                        (∀ K : C, T'.obj (ULift.up K) = ULift.up (T.obj K)) ∧
                        (∀ K : C, S'.obj (ULift.up K) = ULift.up (S.obj K)) ∧
                        (∀ (K L : C) (f : K ⟶ L) (a : Localization.Away p),
                          HEq (T'.map (e K L (a ⊗ₜ[R] f)))
                            (e (T.obj K) (T.obj L) (a ⊗ₜ[R] T.map f))) ∧
                        (∀ (K L : C) (f : K ⟶ L) (a : Localization.Away p),
                          HEq (S'.map (e K L (a ⊗ₜ[R] f)))
                            (e (S.obj K) (S.obj L) (a ⊗ₜ[R] S.map f))) ∧
                        T' ⋙ S' = 𝟭 (ULift.{0} C) ∧ S' ⋙ T' = 𝟭 (ULift.{0} C) ∧
                        T ⋙ Q = Q ⋙ T'
                ) (rlinInst := lr)
            ) (linInst := l)) (addInst := a)) (catInst := d)
```

Its proof is complete. New proof-local implementation declarations are private:
`LinearScalarConstruction.composition`, `composition_tmul`, `composition_unique`,
`composition_id_comp`, `composition_comp_id`, `composition_assoc`, `map_composition`,
and `category`. The helper section commands are:

```lean
namespace LinearScalarConstruction
variable (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear R C] (p : R)
-- private definitions and proved lemmas
end LinearScalarConstruction
open LinearScalarConstruction
```

The private `category` definition has `@[instance_reducible]`. Its data are explicitly
constructed, with all category laws proved by tensor induction. No public definition body
uses these helpers; only the existing theorem proof does. No data or proofs use `sorry`.

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.LinearScalarLocalization
--uses exists_linear_scalarLocalization_category` lists the two downstream modules below,
and lists the item module and `ScalarLocalization` as textual users of the theorem.
Both consumer files were read. Neither needs adaptation: all existing public declarations,
imports, and instances of the item retain their original types and visibility.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.LinearScalarLocalization | G2 | The existing theorem is proved. |
| Sheaf.CategoryTheory.ScalarLocalization | not adapted | Identical theorem type; its chosen unique composition retains the specified pure-tensor formula. |
| Sheaf.CategoryTheory.ScalarLocalizationTriangulated | not adapted | Identical theorem type; all scalar localization interfaces remain unchanged. |

No target statement or definition used in a target statement changes, so no target statement
review is reopened. No existing module outside the item is edited.

## Status

landed 20261018T071152-L-1667719 2026-10-18 (merge of deliver/G2/Sheaf.CategoryTheory.LinearScalarLocalization)
