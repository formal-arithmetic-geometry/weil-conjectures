## Worker report

The module `Sheaf.AlgebraicGeometry.NormalizedSurfaceGraphExceptionalInjection` states
`AlgebraicGeometry.normalized_surface_graph_exceptional_injection`. Its only theorem has
proof `sorry`; it introduces no definitions and proves nothing. The node's natural statement,
dependencies, and proof plan are unchanged. I read Stacks `resolve.tex`, Tag 0BBT, lines
1060–1140, including the definition of BadCurves, the normalized graph, and its injection.
The reduced dominating component is essential: normalizing the whole fibre product can
retain vertical components. No statement dispute or correction is needed.

Hypothesis and construction correspondence:

- `X Y X' : Scheme.{u}` with the three `IsIntegral` instances are the normal integral
  surfaces' underlying integral schemes. Normality is `hXnormal`, `hYnormal`, and
  `hX'normal`, namely domain and integrally closed at every stalk. For a scheme these
  local rings give the node's normal-ring condition, with no assumption of regularity.
- The three `IsNoetherian` instances mean locally Noetherian and quasi-compact, rather
  than just Noetherian coordinate rings on an arbitrarily large noncompact scheme.
- `hXexcellent`, `hYexcellent`, `hX'excellent` test the recorded `IsExcellent` on every
  affine open. `hXdim`, `hYdim`, `hX'dim` give topological dimension exactly two.
- `f`, `g` and `IsProper f`, `IsProper g` are precisely the two proper morphisms.
  `hfη`, `hgη` specify the images of the generic points; `hfK`, `hgK` assert that their
  actual generic stalk maps `functionFieldMap` are isomorphisms. These are induced maps,
  not unrelated isomorphisms of abstract fields. One may take `K = X.functionField`.
- `pullback f g` is the fibre product. `t` and `ht` specify its point over the generic
  point of X. Since both generic fibres are Spec K, their fibre product is Spec K;
  hence this is precisely the point whose closure the node names. The scheme annotation
  on this pullback prevents Lean from selecting the category of types.
- `W`, `i`, `IsClosedImmersion i`, `IsReduced W`, and
  `hW : Set.range i = closure {t}` specify exactly the reduced closed subscheme on that
  closure, up to its unique isomorphism over the fibre product. No choice of an arbitrary
  component or arbitrary map is allowed. In particular `IsIntegral W` is a conclusion,
  not a hypothesis. After that conjunct, universal quantification over its proof lets
  the remainder refer to the canonical function-field normalization without a hidden let.
- `Z`, `ν`, `e : Z ≅ W.normalization`, and `e.hom ≫ W.fromNormalization = ν` merely name
  an arbitrary representative of the specified normalization and its structural map.
  The equalities `ν ≫ i ≫ pullback.fst f g = p` and its second-projection analogue
  force the actual two projections. They are presentation equations, not additional
  geometric hypotheses. The universal formulation includes the canonical normalization
  itself with the identity isomorphism.

Conclusion correspondence, clause by clause:

- `IsFinite ν` asserts normalization is finite. `IsIntegral Z`, `IsNoetherian Z`, the
  stalkwise normality conjunction, affine-open excellence, and `topologicalKrullDim Z = 2`
  give all the asserted surface properties. `IsProper p` and `IsProper f'` give properness.
- The following `∀ [IsIntegral Z]` uses the integrality already asserted, rather than
  assuming it to obtain the preceding conjunct. Existential generic-point equalities
  `hpη`, `hf'η` and `IsIso (p.functionFieldMap hpη)`,
  `IsIso (f'.functionFieldMap hf'η)` assert both induced function-field isomorphisms.
- `B` and `B'` are bound sets with explicit defining equalities: closed irreducible
  subsets of dimension one with singleton image. `IsIrreducible` includes nonemptiness.
  Each such subset carries exactly its reduced induced closed-scheme structure, which
  is integral. Conversely every curve in the node is represented by one such subset.
  This representation avoids counting isomorphic presentations as different subschemes.
  These equations introduce no alternative notion or arbitrary exceptional-curve family.
- `∀ C' ∈ B', p '' C' ∈ B` is the reduced-image membership assertion. The reduced image
  has the same underlying subset `p '' C'`. `Set.InjOn (fun C' ↦ p '' C') B'` is exactly
  the asserted injection, including equality of reduced closed subschemes.
- For every curve and every generic point `η'`, `IsGenericPoint (p η') (p '' C')` identifies
  its image generic point. `∃ U : Y.Opens, p η' ∈ U ∧ IsIso (p ∣_ U)` asserts an
  isomorphism on an open neighbourhood of that point, rather than just a stalk isomorphism.
  `IsIso (p.stalkMap η')` records the actual structural local-ring identification.
- The equality of the two `Set.range` expressions compares the canonical local-ring
  embeddings into `Z.functionField`. The Y-stalk embeds into Y's function field and then
  through the actual `p.functionFieldMap hpη`; the Z-stalk embeds directly. Thus these
  are equal subrings in the same K, not merely abstractly isomorphic local rings.
- `∃ x', f' '' C' = {x'} ∧ f '' (p '' C') = {g x'}` names the two contraction points
  with `x = g x'`. The following two `IsClosed` clauses give their closedness.
  `(g.residueFieldMap x').hom.Finite` asserts the required finite extension through the
  canonical residue-field map, without a let or an independent algebra structure.

Dependency declarations used (source signatures and docstrings read):

- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`;
  the same module supplies `IsReduced` for the reduced closed component.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed` and `IsDomain`, in the local-ring form used throughout this project.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`;
  `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsNoetherian`, supplies its
  scheme-level locally-Noetherian and compact formulation.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`, including
  quasi-excellence and universal catenarity, tested on every affine coordinate ring.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-sc-function-field`: imported `Sheaf.AlgebraicGeometry.FunctionField`; its docstring
  explicitly uses Mathlib `Scheme.functionField` for arbitrary integral schemes, as here.
  The canonical map is the published upstream `Scheme.Hom.functionFieldMap` in
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`, read through `scompile.py --source`
  because the older local source checkout lacks that module. It transports the generic
  stalk by the specified equality and then applies the actual stalk map.
  Mathlib's `stalkFunctionFieldAlgebra` gives both local-ring embeddings.
- `def-sc-normalization`: `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`,
  `Scheme.normalization` and `Scheme.fromNormalization`: normalization in the actual
  function field, with finiteness separate.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`, `genericPoint`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.residueField`
  and `Scheme.Hom.residueFieldMap`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `pullback`, `pullback.fst`, `pullback.snd`; the scheme pullback instance is imported
  through `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`.

Proof imports include the recorded `normal_modification_codimension_one`,
`closedPoint_iff_residueField_trdeg_zero_and_finite`, and `proper_basic` modules, plus
Mathlib's finite-dimensional-domain criterion. Proper base change/composition, closed
immersion properness, scheme sobriety, and the affine tensor-product model are available
from the imported Mathlib modules. `lem-per-normal-surface-exceptional-curves` has no Lean
record yet; its eight-step uses are retained in the docstring and no unstated proof module
is imported or replaced by a copied theorem.

Edge cases checked before finalizing: `g = id` gives the identity correspondence on curves;
`f = id` gives an empty source and target exceptional-curve family; `p = id` gives equal
local-ring ranges. Blowing up a point outside the original contraction set creates no
exceptional curve for `f'` mapping to an exceptional point for `p`. Empty B or B' are
included by membership and `Set.InjOn` with no nonempty assumptions. Curves are nonempty
by `IsIrreducible`; zero-dimensional closed subsets and nonreduced thickenings are excluded
exactly as in the source. Empty surfaces are already excluded by integrality and dimension
two. All characteristics and arbitrary residue fields are allowed, without smoothness,
regularity, algebraic closure, or finite generation over a ground field. All schemes and
their points use the same explicitly bound universe u; no independent smaller test universe
is introduced. All variables are explicitly bound with `autoImplicit false`.

Searches actually run:

- `msearch.py`, LeanFinder: “A normalized dominating graph of two proper birational normal
  surface morphisms induces an injection on exceptional curves”: eight hits for relative
  normalization (`instIsDominantToNormalization`, `normalizationDesc`, normalization-cover
  maps and their composition identities); none states this result.
- `msearch.py`, Loogle: `Scheme.Hom.functionFieldMap, Scheme.closure, Scheme.normalization`:
  zero hits, with diagnostic “unknown identifier 'Scheme.Hom.functionFieldMap'”. The
  upstream function-field map was subsequently found in the published module, not Mathlib.
- `msearch.py`, grep: `exceptionalCurve|BadCurves|dominatingComponent`: zero Mathlib hits.
- Direct `rg` over the project and upstream for `BadCurves`, `badCurves`, `contractedCurves`,
  `ContractedCurve`, dominating graph/component, and `normal_surface` found related surface
  results but no injection theorem or competing exceptional-curve definition. Direct
  node-id search of upstream found no declaration. The upstream-name index was checked
  for function-field, normalized-graph, and exceptional-curve names.
- Direct Mathlib/upstream searches for reduced closed subschemes, vanishing ideals,
  normalization, generic stalk maps, and residue-field maps located the APIs cited above.
  A final search for the proposed declaration/module name found no collision.

Validation: `scompile.py NC lem-per-normalized-surface-graph-exceptional-injection` checked
this file alone both as a sandbox module and under its final library module name, cleanly
in 3.9 seconds each. The initial pullback point annotation was corrected to specify the
category of schemes; no mathematical statement was changed. There are no lines over
100 characters, no unbound universes, and no warnings. Delivery preflight follows.

Delivery validation: `deliver2.py NC lem-per-normalized-surface-graph-exceptional-injection
--no-push` returned `OK (dry run)`: the packet passes server preflight and per-file
compilation. Only the module, the item's node record, and this report are staged.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
