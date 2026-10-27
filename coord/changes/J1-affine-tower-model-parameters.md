# AlgebraicGeometry.ProEtale.VectorIntegrationSite.AffineTowerTransport.Model

## Reason

The original indexed inductive specializes every constructor index to concrete scheme
constructions. Single-file profiling shows kernel checking of Model taking about eight
seconds, followed by the generated recursor/cases construction failing to finish before
the 60-second file limit, before proof helpers are reached. Local irreducibility of
ProjectiveSpace and AffineSpace does not solve kernel reduction of these indices.
Express the least closed predicate by its universal elimination property, with eight
abstract construction inputs, then specialize it to the original schemes. This preserves exactly the six closure rules, including
arbitrary compactifications and arbitrary opens. There is no mathematical statement
change, and no target signature change.

An additional generic proved `ordinaryUnit_plus` supplies the lower-bound proof in
`input`. Profiling showed that elaborating the same constant-unit bound at the
concrete finite quotient created two auxiliary proofs taking about four seconds each
to kernel-check. The generic lemma has exactly the same proposition and proof, and
proof irrelevance preserves the input object and its boundedness witness.

`FiniteInput` is also marked irreducible: its mathematical expression is unchanged.
The proof API unfolds it only in the generic introduction and transport helpers,
so concrete tower applications do not repeatedly expand both sites' constructibility
and Tor predicates. There are no downstream consumers to adapt.

## Old

```lean
inductive Model (S : Scheme.{u}) : Scheme.{u} → Prop
  | affine (d : ℕ) : Model S (affineTraceTower S d)
  | projective (d : ℕ) : Model S (ProjectiveSpace (ULift.{u} (Fin (d + 1))) S)
  | tower (d : ℕ) : Model S (projectiveTower S d)
  | relativeProjective {T : Scheme.{u}} (h : Model S T) (d : ℕ) :
      Model S (ProjectiveSpace (ULift.{u} (Fin (d + 1))) T)
  | completion (d : ℕ) (c : Compactification (affineTraceProjection S d)) : Model S c.Z
  | restriction {T : Scheme.{u}} (h : Model S T) (U : T.Opens) : Model S U.toScheme
```

The old `input` used the inline lower bound `⟨0, inferInstance⟩` for the
ordinary constant complex; the new body calls `ordinaryUnit_plus _ S` for that
same proof. `FiniteInput` previously had no reducibility attribute.

## New

```lean
def ModelFamily {X : Type*} (affine projective tower : ℕ → X)
    (relative : X → ℕ → X) (C : ℕ → Type*) (complete : ∀ d, C d → X)
    (O : X → Type*) (restrict : ∀ T, O T → X) (T : X) : Prop :=
  ∀ P : X → Prop,
    (∀ d, P (affine d)) → (∀ d, P (projective d)) → (∀ d, P (tower d)) →
    (∀ T, P T → ∀ d, P (relative T d)) → (∀ d c, P (complete d c)) →
    (∀ T, P T → ∀ U, P (restrict T U)) → P T

/-- Schemes occurring in the tower, its standard completions, and their open restrictions.
Source: blueprint paragraphs 2--3 and node Step 1
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
abbrev Model (S : Scheme.{u}) : Scheme.{u} → Prop :=
  ModelFamily (affineTraceTower S)
    (fun d ↦ ProjectiveSpace (ULift.{u} (Fin (d + 1))) S) (projectiveTower S)
    (fun T d ↦ ProjectiveSpace (ULift.{u} (Fin (d + 1))) T)
    (fun d ↦ Compactification (affineTraceProjection S d)) (fun _ c ↦ c.Z)
    (fun T ↦ T.Opens) (fun _ U ↦ U.toScheme)

namespace Model

/-- The affine coordinate towers belong to the model family. Source: node Step 1.
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
theorem affine (S : Scheme.{u}) (d : ℕ) : Model S (affineTraceTower S d) :=
  fun _ ha _ _ _ _ _ ↦ ha d

/-- Projective spaces belong to the model family. Source: node Step 1.
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
theorem projective (S : Scheme.{u}) (d : ℕ) :
    Model S (ProjectiveSpace (ULift.{u} (Fin (d + 1))) S) :=
  fun _ _ hp _ _ _ _ ↦ hp d

/-- Projective towers belong to the model family. Source: node Step 1.
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
theorem tower (S : Scheme.{u}) (d : ℕ) : Model S (projectiveTower S d) :=
  fun _ _ _ ht _ _ _ ↦ ht d

/-- Relative projective spaces remain in the family. Source: node Step 1.
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
theorem relativeProjective {S T : Scheme.{u}} (h : Model S T) (d : ℕ) :
    Model S (ProjectiveSpace (ULift.{u} (Fin (d + 1))) T) :=
  fun P ha hp ht hr hc ho ↦ hr _ (h P ha hp ht hr hc ho) d

/-- Every compactification of a tower projection belongs to the family. Source: node Step 1.
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
theorem completion (S : Scheme.{u}) (d : ℕ)
    (c : Compactification (affineTraceProjection S d)) : Model S c.Z :=
  fun _ _ _ _ _ hc _ ↦ hc d c

/-- Open restrictions remain in the family. Source: node Step 1.
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
theorem restriction {S T : Scheme.{u}} (h : Model S T) (U : T.Opens) :
    Model S U.toScheme :=
  fun P ha hp ht hr hc ho ↦ ho _ (h P ha hp ht hr hc ho) U

end Model
```

The boundedness proof is now factored as:

```lean
theorem ordinaryUnit_plus (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit R T) :=
  ⟨0, inferInstance⟩
```

The `input` body uses this proof in the constant object's `DerivedCategory.Plus`
witness. The data is unchanged. `FiniteInput` has the new attribute
`@[irreducible]`, with its full original defining expression unchanged.

## Users

`python3 tools/downstream.py Sheaf.Paper.AffineTowerIntegrationSiteTransport --uses Model`
reports zero downstream Lean modules and only the item itself as a user. The unfinished
DAG parents remain present; no module or mathematical dependency is withdrawn by this
representation change. `tools/downstream.py ... --uses FiniteInput` also reports zero downstream
modules, with three uses within this item. The two local geometry proofs apply the elimination property to the same six cases.
Leastness follows by taking any closed predicate as the quantified predicate; closure
follows by applying the corresponding rule. Conversely this encoding follows by
induction from the old family, and taking the old family as predicate gives the reverse
implication. Thus it changes no modeled scheme. The six Model introduction declarations retain their mathematical types.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | J1 | Specialize the least closed predicate; prove its geometry and transport theorem. |

## Status

landed 20261025T180745-L-4029814 2026-10-25 (merge of deliver/J1/Sheaf.Paper.AffineTowerIntegrationSiteTransport)
