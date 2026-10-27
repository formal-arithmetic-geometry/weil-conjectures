## Worker report

The module `Sheaf.AlgebraicGeometry.HProjectivePermanence` states
`AlgebraicGeometry.isHProjective_of_comp_of_isSeparated`, with one whole-proof `sorry`.
It introduces no definitions and proves nothing. The node changes only in `lean`.
Its former recorded module `Sheaf.DeligneLaumon.HProjectivePermanence` was deleted;
`scompile.py --source Sheaf.DeligneLaumon.HProjectivePermanence` confirms that its source
is unavailable. The source searches found no surviving declaration with this statement.

Clause-by-clause correspondence:

- Schemes and morphisms `f : Z → T`, `g : T → B` are the explicit binders
  `{Z T B : Scheme.{u}} (f : Z ⟶ T) (g : T ⟶ B)`.
- Separatedness of `g`, meaning its diagonal is a closed immersion, is `[IsSeparated g]`.
  The actual Mathlib class definition was read: its field is
  `IsClosedImmersion (pullback.diagonal g)`.
- The nonnegative integer dimension is `(n : ℕ)`. Its homogeneous coordinate set is
  `ULift.{u} (Fin (n + 1))`, a universe lift of exactly `{0, …, n}`.
- The chosen closed immersion over `B` is
  `(i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); B)) (hi : IsClosedImmersion i)`.
- Being over `B` with composite `g ∘ f` is precisely
  `hif : i ≫ (ℙ(ULift.{u} (Fin (n + 1)); B) ↘ B) = f ≫ g`.
  These witness binders express the projectivity hypothesis in the node's specified
  finite-embedding convention, preserving the given dimension; an abstract
  `IsHProjective (f ≫ g)` binder would forget which dimension was given.
- The conclusion existentially supplies
  `j : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)` with `IsClosedImmersion j` and
  `j ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T) = f`.
  Thus the same `n` occurs in the conclusion and its structural projection is exactly `f`.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, with
  `AlgebraicGeometry.IsSeparated` supplied by its import of
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective`. Its field explicitly gives a finite coordinate type,
  a closed immersion and the structural factorization. Here the statement spells out
  the prescribed witness to retain the stronger same-dimension information of the node.
  Its imported canonical `AlgebraicGeometry.ProjectiveSpace`, notation `ℙ`, and projection
  `↘` are used directly, with no private copy.
- Proof dependencies are imported: `IsSeparated.instIsClosedImmersionMapDescScheme`
  in `Mathlib.AlgebraicGeometry.Morphisms.Separated`; `pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.lift` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  `IsClosedImmersion.isStableUnderBaseChange`, `IsClosedImmersion.comp` and
  `IsClosedImmersion` in `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`;
  `ProjectiveSpace.isPullback_map` in `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`.
  Their full signatures and surrounding source were read. The theorem docstring follows
  the node's four-step graph, base-change, composition and projective-space identification
  proof. Already publicly imported proof modules need no second public exposure.

Source checked: local `literature/stacks-project/morphisms.tex`,
`lemma-projective-permanence` (Tag 0C4Q), statement and complete proof, and
`lemma-H-projective-base-change` (Tag 01WF), statement and complete proof. The graph proof
specializes to the given free coordinate module, whose rank does not change on pullback.

Edge cases checked before writing: `n = 0` has one coordinate and projective space equal
to the base up to canonical isomorphism; the claim is then closed-immersion cancellation
against a separated morphism. Empty `Z` embeds as the empty closed subscheme; empty bases
force the appropriate sources empty. Identity `f` or `g`, nonreduced schemes and arbitrary
characteristic cause no change to the graph proof. No Noetherian, quasi-compact, flat,
finite-type or nonempty hypothesis is added. The coordinate type is lifted into the
scheme universe, without changing its cardinality; `u` and all variables are explicit.

Searches (2026-10-24; raw tool results are also in `searches.jsonl`):

- `msearch.py ... leanfinder`: “If X to S embeds as a closed subscheme of projective space
  of dimension n and Y to S is separated, X to Y embeds into projective space of the same
  dimension n over Y”. Eight hits: closed-immersion cancellation, the graph closed
  immersion, pullback map closed immersion and Proj separatedness; no same-n theorem.
- `msearch.py ... leansearch`: “A composite of scheme morphisms is H-projective and the
  second morphism is separated, so the first embeds into projective space of the same
  dimension”. Eight hits including `IsClosedImmersion.of_comp`,
  `IsProper.of_comp_of_isSeparated`, integral/finite/affine cancellation and separatedness;
  none asserts projective-space embeddings.
- `msearch.py ... loogle 'AlgebraicGeometry.IsHProjective, AlgebraicGeometry.IsSeparated'`:
  zero hits, with unknown identifier `AlgebraicGeometry.IsHProjective` in Mathlib.
- `msearch.py ... grep 'IsHProjective|projective.*of_comp|projective.*permanence'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `isHProjective_of_comp_of_isSeparated`, `HProjective.*of_comp`,
  `isHProjective.*comp`, `projective.*permanence`, `IsHProjective.of`, and the item id:
  no equivalent statement survives. Other projectivity results concern special blowups,
  field refinements or unrelated constructions. Read the canonical `IsHProjective`
  declaration and projective-space implementation instead of duplicating either.
- `rg` of `coord/repair-notes` for the item id: no repair note.

No statement correction, new node, dependency replacement, or statement dispute is needed.

## Second reading by Q147

Self-review with the node and new Lean module open; the maintainer performs the independent
delivery review, and this worker did not start another agent. Rechecked the two morphism
directions, the diagonal definition of separatedness, the witness `i`, `hi`, `hif`, and both
conclusion conjuncts against the node. The same `n + 1` coordinate count appears over both
bases. `ULift` is a universe adjustment, not an additional coordinate. No clause is missing
or hypothesis added, and no semantic change was needed. The deleted module is replaced at
the prescribed topic path while preserving its theorem's mathematical signature.
