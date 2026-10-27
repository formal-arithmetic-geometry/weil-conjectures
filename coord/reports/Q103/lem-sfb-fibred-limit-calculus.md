## Worker report

This stage-2 delivery states `CategoryTheory.fibred_limit_calculus` in
`Sheaf.CategoryTheory.FibredLimitCalculus`, with `sorry` as its only proof. The
accepted stage-1 split, statement, dependencies, and proof are preserved. The
inherited BLOCKED ending concerned stage-1 reopening, which is expressly not a
stage-2 restriction (coord/brief-stage2.md §0). The current node had no Lean record
and there is no released repair note for this item.

Hypotheses and clauses, matched against the node and the source:

- The size convention is rendered by the explicitly declared universes
  `u v₁ w₁ v₂ w₂`; source and target total categories have independent object and
  morphism universes. The scheme base is `{S : AlgebraicGeometry.Scheme.{u}}`.
- The two categories over Sch/S are
  `C : BasedCategory.{v₁, w₁} (Over S)` and
  `D : BasedCategory.{v₂, w₂} (Over S)`. Their category structures and projections
  are the Mathlib fields of `BasedCategory`, not private copies.
- `F : BasedFunctor C D` includes its underlying functor `F.toFunctor` and the
  equation `F.toFunctor ⋙ D.p = C.p`. This is exactly a functor over the base.
- `hC : IsFibredInGroupoids C` and `hD : IsFibredInGroupoids D` use the recorded
  predicate: fibre lifts exist, and every arrow has the strong cartesian universal
  property, including uniqueness.
- Ordinary fibre products in C are `HasPullbacks C.obj`. Mathlib defines this as
  limits of all `WalkingCospan` diagrams in the TOTAL category C.obj; the limit
  cone universal property is precisely pairs of arrows with equal composites.
- Preservation by F is
  `PreservesLimitsOfShape WalkingCospan F.toFunctor`, which says that every limit
  cone of every cospan, not just a selected pullback, is taken to a limit cone.
- The algebraic-stack clause is conditional:
  `IsAlgebraicModuliStack C → HasEqualizers C.obj`. It imposes no algebraicity
  requirement on D and no separatedness or finiteness requirement on either
  category. The recorded stack predicate uses etale descent, algebraic-space
  diagonal, and a smooth surjective scheme atlas.
- The final conditional is
  `HasEqualizers C.obj → F.toFunctor.Faithful →
  PreservesLimitsOfShape WalkingParallelPair F.toFunctor`.
  Mathlib's `Faithful.map_injective` is injectivity on each Hom set. Limits of
  `WalkingParallelPair` are exactly the ordinary equalizers defined in the node,
  with the equalizing equation and existence and uniqueness of factorization.
  No restriction is imposed that the parallel arrows have the same base map.

The conjunction groups exactly these four conclusions. The last two hypotheses
are implications inside their respective clauses, so they do not restrict the
unconditional pullback claims. No new definition, dependency repair, or statement
correction is needed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  the recorded `def-pc-scheme` interface. Read their full structure signatures and
  source docstrings in Scheme.lean.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, the relevant declaration recorded for
  `def-sfb-stable-pointed-moduli-groupoids`. Read the definition and docstring at
  lines 367–375. It is `p.IsFibered` together with strong cartesianness of every
  arrow. Its `BasedCategory`/`BasedFunctor` interfaces were read in Mathlib's
  FiberedCategory/BasedCategory.lean, including the full commuting equation.
  The node also contains stable-curve and level-structure vocabulary, which this
  item does not use and therefore does not restate.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, the recorded algebraic-stack definition;
  read the entire module, including its atlas predicates and docstrings.
- `def-weil-size-convention` is the existing convention-only record, with no Lean
  object or import to recreate.
- Mathlib's `HasPullbacks`, `HasEqualizers`, `PreservesLimitsOfShape`,
  `PreservesLimit`, and `Functor.Faithful` were read in their defining modules.
- The stated proof dependency `def-pc-fibre-product` is Mathlib's `pullback`, with
  its signature and the source scheme-pullback instance read. The proof-only
  import `Mathlib.AlgebraicGeometry.Pullbacks` retains this dependency. The other
  two proof-only nodes, `lem-sfb-cartesian-lift-pullback-square` and
  `lem-sfb-algebraic-stack-total-equalizers`, currently have no Lean record; there
  is no corresponding module to import. They are only proof prerequisites, not
  missing notions in the present statement. The module docstring gives all six
  accepted proof steps and names these prerequisites.

Source and edge cases:

Read stacks-sheaves.tex lemma-fibre-products (Tag 06WY), including its proof, and
lemma-fibre-products-morphism (Tag 06WZ), including its proof. The node combines
06WY (1), (3) with 06WZ (1), (2), exactly as this conjunction does. Read the current
blueprint direct-images proof (3), the inherited route of this supporting lemma.
The empty scheme is permitted as S and as an object of Over S; no inhabitance is
assumed for C or D. Pullbacks and equalizers have nonempty finite diagram shapes,
so an empty total category causes no spurious terminal-object requirement. The
case of identity parallel arrows is included, as are arrows with distinct base
maps. Nontrivial fibre automorphisms are permitted: neither category is assumed
to be a discrete groupoid. Without faithfulness a nontrivial BG mapping to the
point need not preserve the equalizer of two distinct automorphisms, so the final
faithfulness condition must stay, as it does here. Unequal universe levels for C
and D remain allowed. No requirement of products or terminal objects was added.

Searches actually run for this delivery:

- msearch.py LeanFinder: "A functor over schemes between categories fibred in
  groupoids preserves pullbacks and faithful functors preserve equalizers".
  Eight hits: the pre-Galois fibre-functor preservation theorem and preservation
  of scheme/open-immersion pullbacks by forgetful functors. None states the CFG
  theorem or the algebraic-stack equalizer clause.
- msearch.py Loogle: `"IsFibredInGroupoids", "PreservesLimitsOfShape"`.
  Successful search, zero hits.
- msearch.py grep: `equalizer|equaliser|HasPullbacks|PreservesLimit` in
  `CategoryTheory/FiberedCategory`. Successful search, zero hits.
- msearch.py LeanSearch: "Categories fibred in groupoids over schemes have
  pullbacks and faithful functors over schemes preserve equalizers".
  Eight hits, principally the existence of pullbacks in Scheme and properness
  of their projections, plus the faithful subobject pullback functor. None
  supplies the total-category statement.
- Direct rg of `IsFibredInGroupoids|fibred.*[Ll]imit|fibred.*[Pp]ullback|fibred.*[Ee]qualizer`
  in both WeilConjectures and Sheaf: the definition and consumers of the CFG
  predicate, but no statement of this lemma. Direct node-id search in
  WeilConjectures: no hits. Searches for the proposed declaration name in
  Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json: no hits.
- Direct reads/searches of the Mathlib pullback, equalizer, preservation and
  faithfulness definitions confirmed that these notions should be reused.

No STATEMENT-DISPUTED issue remains. Only the item's `lean` field is changed.

Validation: the delivered file is compiled separately through scompile.py; the
prescribed deliver2.py dry run and final delivery perform the server preflight
and repeat the per-file compile. Results are recorded below after those runs.

Validation completed: scompile.py passed with no errors or warnings, checking both
sandbox mode (7.0 seconds) and the final module path (5.8 seconds). The deliver2.py
`--no-push` run printed OK: commit 203d87e9780 passes preflight and compiles.
A separate JSON comparison confirms that `lean` is the only changed node field;
the recorded signature matches the file verbatim. The only proof is `by sorry`.

## Second reading by Q103

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
