## Worker report

The module `Sheaf.AlgebraicGeometry.RegularPointBlowupDomination` states
`AlgebraicGeometry.exists_regular_point_blowup_domination`, with a single postponed
proof. Its docstring reproduces all five steps of the accepted DAG proof, including
schematic density, properness of the open strict transform, principalization, and
the final universal lift. The statement is unchanged. No new definition is needed.

Hypothesis and conclusion correspondence:

- `X Y : Scheme.{u}` and `f : Y ⟶ X` are the schemes and morphism of the node.
  `[IsNoetherian X]` includes exactly local Noetherianity and quasi-compactness.
- `T : TopologicalSpace.Closeds X` represents the finite closed subset;
  `hT : (T : Set X).Finite` gives finiteness and `hclosed` requires each singleton
  in it to be closed. Bundling T as a closed subset adds no mathematical
  restriction: a finite union of the closed singletons is closed. Its bundled
  proof only provides the canonical open complement `T.compl`.
- `hregular` requires `IsRegularLocalRing (X.presheaf.stalk t)` at every point
  of T, and `hdim` requires `ringKrullDim (X.presheaf.stalk t) = 2` there.
  No global regularity, dimension, integrality, separation, or nonemptiness is assumed.
- `[IsProper f]` is properness, and `hiso : IsIso (f ∣_ T.compl)` says the
  base change to the complement of T is an isomorphism.
- The existential `A : OrdinaryBlowupTower X` supplies a natural number
  `A.length`, its `length + 1` intermediate schemes, their transition maps,
  initial identification with X, center ideals, and blowup identifications over
  each preceding level. `transition_id` and `transition_comp` make all long
  transition maps the composites of the adjacent blowup maps.
- `h : A.level (Fin.last A.length) ⟶ Y` is the requested morphism and
  `h ≫ f = A.toBase (Fin.last A.length)` is exactly its factorization identity.
- For each `i : Fin A.length`, the existential `p` and `hp` give a single
  closed point of the preceding level. The center equality with
  `Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩` imposes precisely the reduced
  singleton scheme structure. `A.toBase i.castSucc p ∈ (T : Set X)` puts its
  image in T. There are no extra clauses on the intermediate schemes.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`,
  `IsNoetherian` (extends the former and `CompactSpace`).
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`; its node's
  unchanged ring clause is Mathlib's `IsRegularLocalRing` from
  `Mathlib.RingTheory.RegularLocalRing.Defs`. The latter is the clause used here.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`: `OrdinaryBlowupTower`,
  `OrdinaryBlowupTower.toBase`. The already landed owning definition node
  `def-trf-ordinary-resolution-rule` is added to stmt_deps as permitted by §5.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.IdealSheafData.vanishingIdeal`.
  Its docstring explicitly identifies the reduced induced closed subscheme.

Recorded proof dependencies have their available modules imported: admissible
blowups, ideal comap, scheme-theoretic image, strict transform, open immersions,
proper base change/composition and closed immersions, Noetherian opens and
quasi-separatedness, and the blowup universal property. The principalization
node and the elimination node have no Lean records in this snapshot; their
proof roles are included in the docstring, without introducing a duplicate or
adding assumptions standing in for their statements.

Edge cases checked against resolve.tex Tag 0AHI:

- Empty T: all point hypotheses are vacuous and `hiso` is the global isomorphism;
  take length zero and its inverse as h. `Fin 0` makes the center clause empty.
- Empty X: T is empty and the same zero-step argument applies (Y is empty too).
- A globally isomorphic f may use length zero even for nonempty T.
- A scheme may be singular or have other dimensions away from T: no binder
  excludes it. Y need not be integral or regular, and no dimension condition
  is imposed on its components over T.
- Universes: all schemes have arbitrary shared universe u, with no restriction
  on residue characteristics or countability. This is the existing tower API's
  ordinary scheme size convention.

Searches made (full service results retained in searches.jsonl):

- LeanFinder: "A proper morphism isomorphic outside finitely many regular dimension
  two closed points is dominated by a finite sequence of point blowups": eight
  hits on properness and normalization; none states the item.
- Loogle: "AlgebraicGeometry.IsProper, IsRegularLocalRing": zero hits.
- Mathlib grep via msearch: "blowup|blowUp|Blowup" in AlgebraicGeometry:
  zero hits.
- LeanSearch: "A proper modification of a Noetherian scheme supported at finitely
  many regular surface points is dominated by successive point blowups": eight
  hits on Noetherian schemes and properness; none states the item.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for point-blowup/domination
  terminology, the item id, and the proposed theorem name: no existing theorem
  states the item. Found the reusable `OrdinaryBlowupTower`, and neighboring
  surface-rational-map and proper-birational theorems with stronger/different
  hypotheses and conclusions; neither is an exact match. The only current
  literal use of the item id is a proof-plan citation in the surface rational
  map theorem. Also checked `dag/lean_names_upstream.json` for the proposed name.
- Read the full recorded ordinary tower and toBase definitions and their owning
  node, the full recorded statement-dependency signatures/docstrings, and
  resolve.tex Tag 0AHI directly. No statement correction or dispute is needed.

Validation: scompile.py compiled both sandbox and library module successfully,
with no errors or unexpected warnings. Both auto-implicit options are disabled.

## Second reading by NO

The dispatcher explicitly prohibits starting other agents; this section records
a separate self-review pass, not a claim of independent review. The maintainer's
independent review remains pending.

Reopened the node and the final module side by side. Checked every binder:
Noetherian X is not replaced by a globally regular surface; T is finite and its
individual points are closed; regularity and local dimension two occur only at
T; properness and the complement isomorphism are both present. Checked the full
ordinary tower definition: it imposes no rational-input or regular-resolution
condition on an arbitrary tower over X, and the length can be zero. Its initial
isomorphism expresses X_0 = X up to identification and its transition laws make
`toBase` the required composite. Checked the final conjunct: the vanishing ideal
of a singleton makes the center reduced, and the image condition is measured by
the partial composite to X. The equation has Lean's diagrammatic composition
order h then f. The return contains exactly the requested tower and factorization,
with no global surface hypotheses or extra conclusions. No mismatch found and
no statement edits were necessary.
