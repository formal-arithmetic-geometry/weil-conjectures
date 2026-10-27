## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedFibreSubsetFiniteTypeModel` states
`AlgebraicGeometry.Scheme.Hom.exists_reduced_closed_fiber_model`, with its proof
left as `sorry`. There are no new definitions, dependency repairs, or statement
changes. The node is unchanged except for its `lean` record.

Source checked directly: `literature/stacks-project/more-morphisms.tex`, the
paragraph immediately preceding `lemma-cover-generic-fibre-neighbourhood`
(Tag 054Y, lines 6642–6655), and the proof of
`lemma-irreducible-components-in-neighbourhood` (Tag 0554, lines 7402–7435).
The first explicitly allows any point and any closed fibre subset, takes its
closure and the reduced induced structure, and identifies its original fibre
set-theoretically. The latter uses these models for generic components.

Clause-by-clause translation (write `D` for
`closure ((f.fiberι y) '' A)` in this report; no extra Lean definition):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Schemes X and Y, morphism f | `{X Y : Scheme.{u}} (f : X ⟶ Y)` |
| f of finite type | `[LocallyOfFiniteType f] [QuasiCompact f]` |
| y any point of Y | `(y : Y)` |
| A a closed subset of the scheme-theoretic fibre | `(A : Set (f.fiber y)) (hA : IsClosed A)` |
| Canonical projections p_t | `f.fiberι t` |
| D is the closure of the image of A in X | `closure ((f.fiberι y) '' A)` throughout |
| There exist a scheme Z and morphism j into X | `∃ (Z : Scheme.{u}) (j : Z ⟶ X), ...` |
| Z reduced | `IsReduced Z` |
| j a closed immersion | `IsClosedImmersion j` |
| Image of j equals D | `Set.range j = closure ((f.fiberι y) '' A)` |
| h = f composed with j is finite type | `LocallyOfFiniteType (j ≫ f) ∧ QuasiCompact (j ≫ f)` |
| Every base point t, not just y | `∀ t : Y, ...` |
| The canonical map j_t on scheme fibres | `fiberMap (a := j ≫ f) (b := f) j rfl (Y.fromSpecResidueField t)` |
| j_t homeomorphic onto the closed subspace p_t⁻¹(D) | `Topology.IsClosedEmbedding` of that canonical map, together with its `Set.range` equal to `(f.fiberι t) ⁻¹' closure ((f.fiberι y) '' A)` |
| In particular p_y⁻¹(D) = A | Final conjunct `(f.fiberι y) ⁻¹' closure ((f.fiberι y) '' A) = A` |
| j_y identifies the underlying fibre with A | The universal closed-embedding/range clause specialized to `y`, followed by the final equality |
| No reducedness of scheme fibres asserted | `IsReduced` occurs only on `Z`, never on `(j ≫ f).fiber t` |
| A may be empty; no irreducibility, Noetherianity, separatedness, or flatness assumptions | No nonemptiness or other class binders are present |

A closed embedding is precisely a homeomorphism onto its closed range. Thus the
embedding-plus-range formulation includes both the asserted homeomorphism and
closedness of the specified subspace, with the canonical map fixed in both
conjuncts. No arbitrary map or arbitrary homeomorphism substitutes for j_t.
The upstream `fiberMap` is defined by `pullback.map`; its source and target here
are definitionally `(j ≫ f).fiber t` and `f.fiber t`.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, including its full affine-open signature.
  Finite type is its conjunction with quasi-compactness, as recorded by the node.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`, `locallyOfFiniteType_comp` (in FiniteType),
  and `quasiCompact_comp` supply the composition proof interface.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `fiber_fac`, and `fiberHomeo`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding plus stalk surjectivity).
- `WeilConjectures.Mathlib.AlgebraicGeometry.Fiber`:
  `AlgebraicGeometry.Scheme.Hom.fiberMap`, the existing canonical base-change map.
  Its complete definition and docstring were read; no helper is defined again.
- Proof import `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, especially its
  reducedness, closed immersion, and exact-image conjuncts. The full signature
  and nine-step proof docstring were read.
- Proof imports `Mathlib.AlgebraicGeometry.ZariskisMainTheorem` and
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  `IsClosedImmersion.iff_isProper_and_mono` and the proper-composition instance,
  the recorded Mathlib matches for `lem-weil-pbc-closed-immersion-proper`.
  The node's alternative already-proved upstream theorems
  `IsProper.of_isClosedImmersion` and `IsProper.isClosedImmersion_comp` were
  also read; no dependency restatement is needed.

All statement dependency nodes' statements and Lean/mathlib records were read.
The Mathlib proof leaves supply their interfaces without needing Lean records.
The proof docstring follows all four node proof steps and names their nodes.

Edge cases checked mathematically before writing:

- Empty A: D is empty; the empty reduced scheme with its closed immersion is
  the model. Every fibre map is the empty embedding with empty range. No
  `Nonempty` or irreducibility condition excludes this case.
- Empty X or empty fibre at y: again A must be empty and the same model works.
  Empty Y has no y, so the quantified statement has no instance to satisfy.
- A equal to the whole fibre: closure is taken in X, not in the fibre; the
  intersection with the original fibre remains the whole fibre.
- Arbitrary nonclosed y: the proof uses the subspace topology on f⁻¹({y}),
  not closedness of {y} in Y. No closed-point assumption is added.
- Other fibres may be empty or nonreduced. For example, a reduced affine line
  mapping to an affine line by t = x² has a nonreduced scheme fibre over zero;
  choosing A to be its whole generic fibre makes D the whole source. The
  statement correctly asserts only topological fibre identifications.
- Schemes and the existential model share the explicit arbitrary universe u;
  the reduced closed subscheme construction stays in that universe. No test
  object quantifier can become vacuous through an independently smaller universe.

Searches performed with the prescribed msearch wrapper (2026-10-24):

- LeanFinder query: “For a finite type scheme morphism the closure of a closed
  subset of a fibre has a reduced closed subscheme model with that fibre”.
  Eight hits: Jacobson/finite fibres, `map_vanishingIdeal`, immersion and residue
  field results. These supply ingredients, not the complete statement.
- Loogle query: `"fiber", "closure"`. Zero hits.
- Mathlib grep query:
  `(fiber|fibre).*(closure|reduced)|(closure|reduced).*(fiber|fibre)` in
  `AlgebraicGeometry`. Four hits, all in Geometrically/Reduced, about reduced
  fibres rather than the reduced closure model. No exact match.
- LeanSearch query: “The closure of a closed subset of a scheme fibre has a
  reduced closed immersion model of finite type with that same fibre”. Eight
  hits, all closed-immersion/finite-type/finite-morphism ingredients; no match.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `exists_reduced_closed_fiber_model` found
  no declaration. Direct grep for the exact item id in WeilConjectures found
  no declaration. Concept searches found component-specific closure results
  (`FlatFibreComponentClosureDimension`, `FlatAssociatedEquidimensional`),
  not this arbitrary closed-subset assertion. The search for `fiberMap` found
  and reused the upstream canonical map. No notion is copied.

Validation: `scompile.py Q07 lem-trf-closed-generic-subset-finite-type-model`
compiled the delivered module in sandbox and library modes in 1.5 seconds each,
with no errors or warnings. Only the requested theorem has `sorry` as its proof.
No statement dispute or node fault was found.

## Second reading by Q07

The author reread the node and the completed module side by side after the
successful compile. This is an author check; the dispatcher's no-subagent rule
leaves the independent delivery review to the maintainer.

The two finite-type hypotheses are both present; neither is imposed on X or Y
as an object. `A` belongs to `f.fiber y`, while its image closure is explicitly
in X. The existential supplies the reduced model and the closed immersion;
`j ≫ f` is the order representing f composed with j. Every occurrence of the
fibre map fixes its source base morphism to `j ≫ f`, target base morphism to f,
and base-change morphism to `Y.fromSpecResidueField t`. Thus `rfl` certifies
exactly the commuting triangle and does not add a hypothesis.

The `∀ t` clause gives the same canonical map a closed embedding and the
specified range; this is equivalent to the node's homeomorphism onto the
closed inverse-image subspace. The final conjunct supplies the original-fibre
equality, and specializing the preceding clause gives its stated consequence
for j_y. There are no reduced-fibre, generic-point, nonempty, irreducibility,
Noetherian, separatedness, or flatness binders. All variables and the sole
universe are explicitly bound. No mismatch requiring a change was found.
