## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective` states
`AlgebraicGeometry.isHProjective_of_isProjectiveBundle`, with its proof wholly `sorry`.
It states Stacks Morphisms Lemma 087S(1), exactly as the DAG node does.
No definitions, additional nodes, dependency repairs, or statement corrections are needed.
There is no statement dispute.

Hypothesis and conclusion correspondence:

- The schemes V and S are `{V S : Scheme.{u}}`, and the named morphism is
  `(g : V ⟶ S)`. The universe `u` is explicitly bound and unrestricted.
- Projectivity in the EGA/ILO projective-bundle sense is
  `(hg : IsProjectiveBundle g)`. This is the recorded dependency definition, not
  the upstream `IsProjective` class. Its actual data is a finite type quasi-coherent
  module E on S, a closed immersion into the canonical relative Proj of Sym(E),
  and the equality of its composite with g. It does not demand local freeness.
- “S admits an ample invertible sheaf” is the single existence hypothesis
  `(hS : ∃ (L : S.Modules) (hL : L.IsInvertible), @Scheme.Modules.IsAmple S L hL)`.
  It chooses no extra structure and imposes no condition on V. The explicit `@`
  supplies the existential invertibility proof to the recorded absolute ampleness
  definition. That definition includes quasi-compactness and affine nonvanishing
  neighborhoods from positive tensor powers. No separate Noetherian, reduced,
  nonempty, affine, or separated hypothesis is imposed.
- The complete conclusion is `IsHProjective g`, the dependency's finite-projective-
  space convention. Its finite coordinate type formulation is the recorded
  equivalent of an embedding into P^N_S for N nonnegative.

Dependency declarations read in full and used:

- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`,
  `AlgebraicGeometry.IsProjectiveBundle` (definition, full body and docstring).
- `WeilConjectures.AlgebraicGeometry.Ample`,
  `AlgebraicGeometry.Scheme.Modules.IsAmple` (definition, full body and docstring).
  The current source was read using `scompile.py --source`, since the older
  slopmaster2 reference checkout has no file at this module path.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective` (class, its full field and docstring), also read
  with `scompile.py --source`. It quantifies over finite coordinate types.
- Proof-only import `Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition`,
  `AlgebraicGeometry.IsHProjective.comp`, with its full signature and proof plan.
- Proof-only import `WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration`,
  `AlgebraicGeometry.Scheme.Modules.exists_finite_generatingSections_tensorPow_of_isAmple`,
  with its full signature and docstring, read with `scompile.py --source`.

The two proof-only nodes `lem-trf-relative-proj-invertible-twist` and
`lem-trf-projective-bundle-global-generated-h-projective` have no Lean record in
this snapshot, so have no module to import. Their statements are only needed by
stage 3, not to state this implication. They remain in the unchanged proof plan
and are explicitly named in the theorem's step-by-step proof docstring.

Source check: read `literature/stacks-project/morphisms.tex`, the entire lemma
`lemma-projective-over-quasi-projective-is-H-projective` and its proof. Clause (1)
assumes precisely an ample invertible sheaf on the base and projectivity of the
morphism. The proof twists the finite type quasi-coherent module to finite global
generation, identifies its projective bundle by 02NC, embeds into finite projective
space, and composes with the original closed immersion. All four DAG steps appear
in the theorem docstring.

Edge cases checked before writing:

- The empty scheme is allowed for V or S; there is no nonemptiness binder. Over an
  empty base the source is empty, and the conclusion still permits its embedding.
- The zero finite type quasi-coherent module and an empty generating family give
  an empty projective bundle, also allowed; no positive rank is required.
- Dimension zero in the H-projective conclusion is allowed. A closed immersion
  factors through P^0 over its target, as used in the last proof step.
- The ample twist bound is an integer, but choosing a natural number above it
  suffices, including when the bound is nonpositive. No exponent restriction is
  added to the theorem statement.
- No characteristic, connectedness, field, or Noetherian restriction occurs in the
  source; none occurs in the Lean. Absolute ampleness already supplies the
  quasi-compactness used in the proof, so it is not added as a separate assumption.

Searches for an existing exact statement:

- `msearch.py ... leanfinder` query “A projective morphism in the projective bundle
  sense over a scheme admitting an ample invertible sheaf is H-projective”: eight
  hits, concerning Proj properness and related construction facts, no match.
- `msearch.py ... leansearch` query “A projective morphism over a scheme with an
  ample invertible module is H-projective”: eight hits (proper morphisms, affine
  morphisms, module projectivity, Proj facts), no match.
- `msearch.py ... loogle` query
  `AlgebraicGeometry.IsHProjective, AlgebraicGeometry.IsProjectiveBundle`: zero hits,
  unknown identifier `AlgebraicGeometry.IsHProjective` in the search index.
- `msearch.py ... grep` query
  `IsHProjective|IsProjectiveBundle|isHProjective.*[Aa]mple`, subdirectory
  `AlgebraicGeometry`: zero Mathlib hits.
- Direct `rg` of the upstream reference `WeilConjectures`, side `lean/Sheaf`, and
  current published `lean/WeilConjectures`, for `IsProjectiveBundle`, ample/projective
  combinations and the item id found the dependency definition and the consumer
  proof-plan mention in `RelativeMarkedNodalReduction`, but no theorem stating
  this implication. Related ample-to-immersion statements concern other hypotheses.
- Direct `rg` across Mathlib and both source roots for the proposed name
  `isHProjective_of_isProjectiveBundle` found no collision. Search of
  `dag/lean_names_upstream.json` for ample/projective-bundle names found no match.

The Lean 4 skill was used for source/signature inspection; the task-specific
compilation and delivery wrappers supersede its generic build workflow.

Validation: `scompile.py Q146 lem-trf-projective-bundle-to-h-projective` compiled
this delivered file in both sandbox and library-path modes (5.1 s and 2.8 s),
with no errors or warnings. Auto-implicit variables are explicitly disabled.
The node copy changes only `lean`, with the exact multiline signature from the
file and the UTC date supplied by `date -u +%F` (2026-10-17).

## Second reading by Q146

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
