# CategoryTheory.FormalSplitAttachment shared definitions

## Reason

The complete attachment proof has three separate mathematical components: explicit ordinal
operators, their functor realization, and the splitness argument. They need the definitions
originally in `Sheaf.Paper.SiteHypercoverFiniteExtension`, while that module must import their
proofs. Move the shared definitions into `Sheaf.Paper.SiteHypercoverFiniteExtensionBase` and
publicly re-export that module from the original module to avoid a cycle. This is a relocation,
not a mathematical change: the twelve existing signatures and definition bodies are identical.
The original theorem signature, including all universes and hypotheses, is identical.

The new modules expose normalization and its finite-label API, explicit operators and their
proved factorization identities, composition, realization, and splitness. None adds a proof hole.
There is no change to the meaning of any target statement, because all existing definitions
are verbatim. The five new DAG nodes attach the new APIs and the relocated declarations.

## Old

In `Sheaf.Paper.SiteHypercoverFiniteExtension`:

```lean
/-- A retained degree. Source: Stacks 0DAV
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def degree (q : Fin (n + 1)) : SimplexCategory.Truncated n :=
  ⟨SimplexCategory.mk q.val, Nat.le_of_lt_succ q.isLt⟩

/-- The family in a retained degree. Source: Stacks 0DAV
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def term (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (q : Fin (n + 1)) : FormalCoproduct.{w} D := K.obj (op (degree q))

/-- An ordinal operator on retained degrees. Source: Stacks 0DAV
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def operator (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    {q r : Fin (n + 1)} (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val) :
    term K r ⟶ term K q :=
  K.map (SimplexCategory.Truncated.Hom.tr α
    (Nat.le_of_lt_succ q.isLt) (Nat.le_of_lt_succ r.isLt)).op

/-- Indices outside all proper degeneracy images. Source: Stacks 0DAU
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def IsNondegenerate (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (q : Fin (n + 1)) (i : (term K q).I) : Prop :=
  ¬ ∃ (r : Fin (n + 1)) (_ : r.val < q.val)
    (σ : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val),
    Epi σ ∧ ∃ j : (term K r).I, (operator K σ).f j = i

/-- Normalized split labels, including the identity label. Source: Stacks 0DAU
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def Labels (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (q : ℕ) :=
  Σ r : Fin (n + 1),
    {σ : SimplexCategory.mk q ⟶ SimplexCategory.mk r.val // Epi σ} ×
      {i : (term K r).I // IsNondegenerate K r i}

/-- The canonical label-to-index map. Source: Stacks 0DAU
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def labelIndex (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (q : Fin (n + 1)) (a : Labels K q.val) : (term K q).I :=
  (operator K a.2.1.val).f a.2.2.val

/-- The explicit split condition of the node: bijective index normalization and
isomorphisms on every normalized component. Source: Stacks 0DAU
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def IsSplit (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) : Prop :=
  (∀ q : Fin (n + 1), Function.Bijective (labelIndex K q)) ∧
    ∀ (q : Fin (n + 1)) (a : Labels K q.val),
      IsIso ((operator K a.2.1.val).φ a.2.2.val)

/-- Compatible boundary projections, indexed by all lower simplices. Restriction to
codimension-one faces and their pairwise overlaps gives the node's finite boundary diagram;
conversely, every lower simplex factors through a face, uniquely up to those overlaps.
In dimension one this is just two projections with no compatibility equations.
Source: Stacks 0DAV (blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
structure BoundaryCone (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (T : FormalCoproduct.{w} D) where
  projection : ∀ (q : Fin (n + 1)),
    (SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)) → (T ⟶ term K q)
  naturality : ∀ (q r : Fin (n + 1))
    (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val)
    (β : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)),
    projection r β ≫ operator K α = projection q (α ≫ β)

/-- The universal property of the boundary matching object. Source: Stacks 0DAV
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def IsMatching (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    {M : FormalCoproduct.{w} D} (c : BoundaryCone K M) : Prop :=
  ∀ (T : FormalCoproduct.{w} D) (p : BoundaryCone K T),
    ∃! f : T ⟶ M, ∀ (q : Fin (n + 1))
      (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)),
      f ≫ c.projection q α = p.projection q α

/-- The new family, indexed by new simplices and old proper degeneracies.
Source: Stacks 0DAV (blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def attachedFamily (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) : FormalCoproduct.{w} D :=
  ⟨V.I ⊕ Labels K (n + 1),
    Sum.elim V.obj (fun a ↦ (term K a.1).obj a.2.2.val)⟩

/-- Inclusion of the new family. Source: Stacks 0DAV
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def newInclusion (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) : V ⟶ attachedFamily K V :=
  ⟨Sum.inl, fun _ ↦ 𝟙 _⟩

/-- Inclusion of an old normalized summand. Source: Stacks 0DAV
(blueprint: lem-weil-pbc-site-hypercover-finite-extension). -/
def oldInclusion (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) (a : Labels K (n + 1)) :
    (FormalCoproduct.incl D).obj ((term K a.1).obj a.2.2.val) ⟶ attachedFamily K V :=
  FormalCoproduct.Hom.fromIncl (Sum.inr a) (𝟙 _)
```

The original module publicly imported finite limits, formal coproducts, and simplicial basics.
Its only unproved theorem was `CategoryTheory.FormalSplitAttachment.exists_split_truncated_extension`.

## New

The same definitions now live in `Sheaf.Paper.SiteHypercoverFiniteExtensionBase`:

```lean
/-- A retained degree. Source: Stacks 0DAV
(blueprint: def-weil-pbc-site-split-attachment-data). -/
def degree (q : Fin (n + 1)) : SimplexCategory.Truncated n :=
  ⟨SimplexCategory.mk q.val, Nat.le_of_lt_succ q.isLt⟩

/-- The family in a retained degree. Source: Stacks 0DAV
(blueprint: def-weil-pbc-site-split-attachment-data). -/
def term (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (q : Fin (n + 1)) : FormalCoproduct.{w} D := K.obj (op (degree q))

/-- An ordinal operator on retained degrees. Source: Stacks 0DAV
(blueprint: def-weil-pbc-site-split-attachment-data). -/
def operator (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    {q r : Fin (n + 1)} (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val) :
    term K r ⟶ term K q :=
  K.map (SimplexCategory.Truncated.Hom.tr α
    (Nat.le_of_lt_succ q.isLt) (Nat.le_of_lt_succ r.isLt)).op

/-- Indices outside all proper degeneracy images. Source: Stacks 0DAU
(blueprint: def-weil-pbc-site-split-attachment-data). -/
def IsNondegenerate (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (q : Fin (n + 1)) (i : (term K q).I) : Prop :=
  ¬ ∃ (r : Fin (n + 1)) (_ : r.val < q.val)
    (σ : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val),
    Epi σ ∧ ∃ j : (term K r).I, (operator K σ).f j = i

/-- Normalized split labels, including the identity label. Source: Stacks 0DAU
(blueprint: def-weil-pbc-site-split-attachment-data). -/
def Labels (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (q : ℕ) :=
  Σ r : Fin (n + 1),
    {σ : SimplexCategory.mk q ⟶ SimplexCategory.mk r.val // Epi σ} ×
      {i : (term K r).I // IsNondegenerate K r i}

/-- The canonical label-to-index map. Source: Stacks 0DAU
(blueprint: def-weil-pbc-site-split-attachment-data). -/
def labelIndex (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (q : Fin (n + 1)) (a : Labels K q.val) : (term K q).I :=
  (operator K a.2.1.val).f a.2.2.val

/-- The explicit split condition of the node: bijective index normalization and
isomorphisms on every normalized component. Source: Stacks 0DAU
(blueprint: def-weil-pbc-site-split-attachment-data). -/
def IsSplit (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) : Prop :=
  (∀ q : Fin (n + 1), Function.Bijective (labelIndex K q)) ∧
    ∀ (q : Fin (n + 1)) (a : Labels K q.val),
      IsIso ((operator K a.2.1.val).φ a.2.2.val)

/-- Compatible boundary projections, indexed by all lower simplices. Restriction to
codimension-one faces and their pairwise overlaps gives the node's finite boundary diagram;
conversely, every lower simplex factors through a face, uniquely up to those overlaps.
In dimension one this is just two projections with no compatibility equations.
Source: Stacks 0DAV (blueprint: def-weil-pbc-site-split-attachment-data). -/
structure BoundaryCone (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (T : FormalCoproduct.{w} D) where
  projection : ∀ (q : Fin (n + 1)),
    (SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)) → (T ⟶ term K q)
  naturality : ∀ (q r : Fin (n + 1))
    (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val)
    (β : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)),
    projection r β ≫ operator K α = projection q (α ≫ β)

/-- The universal property of the boundary matching object. Source: Stacks 0DAV
(blueprint: def-weil-pbc-site-split-attachment-data). -/
def IsMatching (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    {M : FormalCoproduct.{w} D} (c : BoundaryCone K M) : Prop :=
  ∀ (T : FormalCoproduct.{w} D) (p : BoundaryCone K T),
    ∃! f : T ⟶ M, ∀ (q : Fin (n + 1))
      (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)),
      f ≫ c.projection q α = p.projection q α

/-- The new family, indexed by new simplices and old proper degeneracies.
Source: Stacks 0DAV (blueprint: def-weil-pbc-site-split-attachment-data). -/
def attachedFamily (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) : FormalCoproduct.{w} D :=
  ⟨V.I ⊕ Labels K (n + 1),
    Sum.elim V.obj (fun a ↦ (term K a.1).obj a.2.2.val)⟩

/-- Inclusion of the new family. Source: Stacks 0DAV
(blueprint: def-weil-pbc-site-split-attachment-data). -/
def newInclusion (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) : V ⟶ attachedFamily K V :=
  ⟨Sum.inl, fun _ ↦ 𝟙 _⟩

/-- Inclusion of an old normalized summand. Source: Stacks 0DAV
(blueprint: def-weil-pbc-site-split-attachment-data). -/
def oldInclusion (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) (a : Labels K (n + 1)) :
    (FormalCoproduct.incl D).obj ((term K a.1).obj a.2.2.val) ⟶ attachedFamily K V :=
  FormalCoproduct.Hom.fromIncl (Sum.inr a) (𝟙 _)
```

The original module publicly imports `Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits` and
`Sheaf.Paper.SiteHypercoverFiniteExtensionBase`. The latter publicly imports the original formal
coproduct and simplicial-basic modules, so the original public dependencies remain available.
The proof-only imports are the realization module, the splitness module, and finite sums.
The base module privately imports finite sigma types for its proved `finite_labels` theorem.
All twelve old signatures and bodies were compared mechanically with their originals and agree.
The original theorem is proved without changing its signature. No downstream source is adapted.

## Users

The table includes all eleven modules reported by `tools/downstream.py` for the original module,
as well as the changed module itself. Holders are the local claim snapshot; no other group's
module is changed. Searching the library finds only one direct importer,
`Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence`; its original source compiles unchanged
against the sandbox overlay. It does not directly mention the relocated declaration names.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.SiteHypercoverFiniteExtension` | D3 | Definition bodies moved verbatim; theorem proved with identical signature. |
| `Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover` | C3 | No source change; definitions and theorem signature remain identical through re-export. |
| `Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts` | C2 | No source change; definitions and theorem signature remain identical through re-export. |
| `Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex` | C3 | No source change; definitions and theorem signature remain identical through re-export. |
| `Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence` | F1 | Original source compiled unchanged against the new module. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | No source change; definitions and theorem signature remain identical through re-export. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | C1 | No source change; definitions and theorem signature remain identical through re-export. |
| `Sheaf.Paper.CondensedQcqsPushforwardContinuity` | unclaimed | No source change; definitions and theorem signature remain identical through re-export. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | unclaimed | No source change; definitions and theorem signature remain identical through re-export. |
| `TargetsCheck` | unclaimed | No source change; definitions and theorem signature remain identical through re-export. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | No source change; definitions and theorem signature remain identical through re-export. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | A2 | No source change; definitions and theorem signature remain identical through re-export. |

## Status

landed 20261015T154201-L-160991 2026-10-15 (merge of deliver/D3/Sheaf.Paper.SiteHypercoverFiniteExtension)
