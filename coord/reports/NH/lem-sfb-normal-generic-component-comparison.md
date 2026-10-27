## Worker report

The module `Sheaf.AlgebraicGeometry.NormalGenericComponentComparison` states
`AlgebraicGeometry.normal_generic_component_comparison`, with one whole-proof `sorry`.
It introduces no definitions and changes only the item's `lean` record. All eight
statement dependencies have usable recorded declarations. No new nodes, dependency
repairs, statement corrections, or disputed statements are needed.

The source read was `literature/stacks-project/topology.tex`, Tag 0906,
`lemma-spectral-pi0`, together with every proof step of the node. Tag 0906 itself
only asserts profiniteness of the spectral component quotient; the final stronger
criterion is the recorded project lemma below. I also read the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3). The helper is the
node's agent expansion, not a statement appearing in that paragraph verbatim.

Hypotheses and objects, clause by clause:

- The nonempty integral scheme is `{X : Scheme.{u}} [IsIntegral X]`.
  `IsIntegral.nonempty` already supplies nonemptiness; no redundant binder is added.
- Its generic point is Mathlib's `genericPoint X`. The recorded
  `genericPoint_spec X` says `IsGenericPoint (genericPoint X) Set.univ`.
  Scheme sobriety gives existence and its T0 property gives uniqueness, so this
  canonical representative does not restrict the generic point in the node.
- Its function field is `X.functionField`, definitionally
  `X.presheaf.stalk (genericPoint X)`, as specified by the integral-scheme clause
  of def-sc-function-field. The imported upstream module explicitly directs this
  clause to Mathlib's definition, not its component-product definition.
- The generic inclusion `j` is exactly `X.fromSpecStalk (genericPoint X)`, of
  type `Spec X.functionField ⟶ X`. This is the existing canonical stalk morphism,
  rather than an arbitrary morphism whose source happens to be a field spectrum.
- The affine scheme and arbitrary morphism are `{U : Scheme.{u}} [IsAffine U]`
  and `(u : U ⟶ X)`. There is no flatness, normality, etaleness, finite-type,
  or quasi-separatedness assumption on X or on the morphism.
- `U_η` is the chosen categorical fibre product
  `pullback u (X.fromSpecStalk (genericPoint X))`; its projection `i` is
  `pullback.fst u (X.fromSpecStalk (genericPoint X))`.
- The family of affine open subschemes is `(B : Set U.Opens)` together with
  `hBaffine : ∀ W ∈ B, IsAffineOpen W`. Using a set of opens forgets only
  repeated indexing, which none of the hypotheses or conclusions uses.
- The precise open-basis condition is `hBbasis`: for every open O and point
  x in O there exists W in B containing x with `W ≤ O`.
- For each W in B the space `W_η = i⁻¹(W)` is the subtype underlying the
  open `i ⁻¹ᵁ W`. This is canonically the underlying space of the open subscheme
  `W ×_X Spec k`. The map `i_W` is the existing `Set.restrictPreimage` of i.
  The source and target have exactly their subspace topologies; no topology or
  map is supplied by an extra hypothesis.
- `hBclopen` is `Function.Bijective` on that restricted inverse-image function
  from `Clopens W` to `Clopens (i ⁻¹ᵁ W)`. The constructor supplies the actual
  set inverse image with its clopenness proof from
  `C.isClopen.preimage i.continuous.restrictPreimage`.
  `Clopens` means both open and closed, including in these subspaces.

Conclusions, in the order of the conjunction:

1. `IsAffineHom (X.fromSpecStalk (genericPoint X))` says j is affine.
2. `IsAffineHom (pullback.fst ...)` says i is affine.
3. `IsAffine (pullback ...)` says the generic fibre is affine.
4. `SpectralSpace U` and `SpectralSpace (pullback ... : Scheme.{u})`
   assert precisely the two spectral-space clauses.
5. `Function.Bijective (fun C : Clopens U ↦ ⟨i ⁻¹' (C : Set U), ...⟩)`
   is the global clopen inverse-image bijection.
6. `IsHomeomorph i.continuous.connectedComponentsMap` refers to the actual
   canonical induced component map. `IsHomeomorph` includes continuity,
   openness and bijectivity, hence the inverse is continuous.
7. The final function equality is exactly
   `i.continuous.connectedComponentsMap ∘ ConnectedComponents.mk =
   ConnectedComponents.mk ∘ i`. The explicit source and target annotations
   identify the two quotient maps with the correct spaces.
   Mathlib's `ConnectedComponents` quotients by equality of connected components
   and carries the quotient topology. No arbitrary homeomorphism is substituted.

Dependency declarations read and used:

- def-pc-integral-scheme: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`, including its docstring and both fields.
- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`; affineness/open subschemes use `IsAffine` and `IsAffineOpen`
  from `Mathlib.AlgebraicGeometry.AffineScheme`.
- def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, with `Spec.map` read as well.
- def-pc-fibre-product:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
  The required scheme pullbacks are supplied by the affine-morphism imports.
- def-weil-spectral-space: `Mathlib.Topology.Spectral.Basic`, `SpectralSpace`.
- def-sc-generic-point: `Mathlib.Topology.Sober`, `IsGenericPoint`,
  `genericPoint`, `genericPoint_spec`.
- def-sc-function-field: the recorded module
  `WeilConjectures.AlgebraicGeometry.FunctionField` publicly imports
  `Mathlib.AlgebraicGeometry.FunctionField`; its integral-scheme clause uses
  `Scheme.functionField`, exactly as that recorded module's docstring prescribes.
  `Scheme.functionFieldOfComponents` is for the other clause of that dependency.
- pqf-def-affine-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom`, whose field tests preimages of every affine open.
- Proof-dependency interfaces read: `isAffineHom_isStableUnderBaseChange` and
  `isAffine_of_isAffineHom` in the affine-morphism module;
  `Scheme.compactSpace_of_isAffine` in the affine-scheme module;
  `quasiSeparatedSpace_of_isAffine` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`; the spectral class and
  scheme topology instances; and
  `isHomeomorph_connectedComponentsMap_of_bijective_clopen_preimage` in
  `Sheaf.Topology.SpectralSpace.ClopenComponentHomeomorphism`.
  The latter is a plain proof import. Its full docstring and signature were read.
  The module's theorem docstring carries all six proof steps of this item.

Edge cases checked before writing:

- Empty U is allowed. No `Nonempty U` binder or nonempty basis occurs. With
  `B = ∅`, the basis condition is vacuous exactly when U is empty, and the
  pullback is empty. Both clopen types then have their single empty clopen,
  and the component map is the homeomorphism between empty quotients.
- A nonempty W with empty generic preimage cannot meet `hBclopen`: its empty
  and full clopens have the same image. The theorem does not silently assume
  dominance or that every W has a generic-fibre point.
- Empty basis members are harmless. The basis need not be closed under
  intersections, and no affineness of intersections appears in the statement.
- X itself is nonempty because it is integral. No stronger normality hypothesis
  is inferred from the item's title. The field case `X = Spec k` is included.
- No hypothesis requires X quasi-separated. Only the conclusion about U and
  its generic fibre is spectral, using their affineness.
- The universe `u` is explicitly bound. All schemes lie in the usual common
  scheme universe; larger original universes can be put in a common maximum.
  There are no independent test-object universes, auto-bound variables, `let`
  binders, local notation, local instances, or new choices of mathematical data.

Searches actually run on 2026-10-24:

- msearch.py, leanfinder: “For an affine scheme over an integral scheme, clopen
  inverse image bijections on an affine open basis give a homeomorphism on
  connected component spaces of the generic fibre”. Eight hits, including
  `Scheme.Hom.fiberHomeo`, `PrimeSpectrum.preimageHomeomorphFiber`, and
  `Scheme.SpecToEquivOfField`; none states this basis descent theorem.
- msearch.py, loogle: `"ConnectedComponents", "Clopens"`: zero hits.
- msearch.py, grep:
  `(generic|functionField).*(ConnectedComponents|Clopen)|(ConnectedComponents|Clopen).*(generic|functionField)`:
  zero Mathlib hits.
- msearch.py, leansearch: “Clopen inverse image bijections on an open basis
  give a global clopen bijection and a homeomorphism of connected components
  for affine generic fibres”. Eight hits, including `IsClopen.preimage`,
  `Topology.IsQuotientMap.isClopen_preimage`, `Clopens.toOpens`, and
  `affineOpensRestrict_symm_apply_coe`; none is the theorem.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` with the above generic /
  functionField / clopen / component pattern and the exact node id found no
  existing statement of this item. Broader generic/component/basis searches
  found the spectral-clopen criterion and other generic-component results,
  none with this node's hypotheses and all its conclusions. Searching
  `dag/lean_names_upstream.json` found no `normal_generic_component_comparison`.
- Direct rg/read of Mathlib and both source roots for `fromSpecStalk`,
  `functionField`, `restrictPreimage`, `Clopens`, and `connectedComponentsMap`
  located the canonical constructions used here; no private copies were written.

Validation: scompile.py NH lem-sfb-normal-generic-component-comparison compiled
this exact module successfully in sandbox and library-module mode, with no
errors or unexpected warnings. Initial elaboration diagnostics required explicit
`: Scheme.{u}` annotations where a categorical pullback is coerced to a space;
these annotations resolve its category without imposing any extra hypothesis.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
