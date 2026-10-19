## Worker report

The module `Sheaf.CategoryTheory.ConeMonoRightAnodyne` states
`SSet.rightAnodyneExtensions_rightCone_map`, with its sole theorem proof `sorry`.
It constructs the join, its action on maps, and the right cone from existing Mathlib
Kan-extension and ordinal-concatenation constructions. No theorem is proved, no
definition contains `sorry`, and no other existing DAG node is restated.

Source checked: [Kerodon Lemma the project server, Tag 0196](https://kerodon.net/tag/0196), first
assertion. Its proof reduces a weakly saturated class to boundary inclusions and identifies
their cones with the final horns. The theorem docstring contains that full proof plan.
An archival copy of this Kerodon source is still WANTED; the cited online text was read.

Hypothesis and clause correspondence:

- Simplicial sets `A,B`: `{A B : SSet.{u}}`, with arbitrary explicitly declared universe `u`.
- Simplicial map `u : A → B`: `(f : A ⟶ B)`.
- Injective in every simplicial degree:
  `(hf : ∀ (n : SimplexCategoryᵒᵖ), Function.Injective (f.app n))`.
  Every simplex-category object is included; no Kan or quasicategory condition is imposed.
- The stated join and its operators: `SSet.joinFunctor`. First,
  `joinAugmentationFunctor` is right Kan extension along
  `AugmentedSimplexCategory.inclusion.op`. At the empty ordinal the indexing category is
  empty, so it gives the terminal type. At a nonempty ordinal the inclusion is fully
  faithful and its right extension recovers the given simplicial set. Then take the
  external product of these augmented presheaves and left Kan extend along
  `tensor AugmentedSimplexCategoryᵒᵖ`; finally restrict along the same inclusion.
  This tensor is the opposite of Mathlib's ordinal concatenation, with the left block
  first. It is not the degreewise product tensor on simplicial sets.
  To see the degreewise formula, index the pointwise left extension at `[r]` by maps
  `[r] → [a] ⋆ [b]`, allowing either target block to be empty. Each such map determines
  a unique cut of `[r]` by inverse images of the two blocks. Within each cut component,
  the identity map from that cut's ordinal concatenation is terminal: the restrictions
  to the two blocks give its unique incoming morphism in the opposite indexing category.
  Thus its colimit is the coproduct over cuts of the two restricted simplex types.
  The two extreme cuts give `X_r` and `Y_r`; all remaining cuts give `X_a × Y_b` with
  `a+b+1=r`. Precomposition restricts these same ordered blocks, giving exactly the
  simplicial operators in the node.
- `X` as the cone base and the added vertex: these are the extreme pure-left and
  pure-right summands of `joinFunctor.obj (X, Δ[0])`. No arbitrary map or cone datum
  is supplied as an assumption.
- `X^{triangleright} = X ⋆ Δ[0]`: `SSet.rightConeFunctor` is `Prod.sectL SSet Δ[0]`
  followed by `joinFunctor`.
- The induced map `f ⋆ id_{Δ[0]}`: `rightConeFunctor.map f`, since `Prod.sectL.map`
  is exactly the pair `(f, 𝟙 Δ[0])`.
- Right anodyneness: conclusion
  `rightAnodyneExtensions (rightConeFunctor.map f)`. This is the existing smallest
  morphism property containing isomorphisms and right horns and closed under pushouts,
  transfinite compositions and retracts; it is not the all-horn Kan-anodyne property.
  In its generator binder `i : Fin (n+1)` with `0 < i`, one has `0 < i ≤ n`, which
  also forces `n ≥ 1`, so its convention is precisely the node's.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, the recorded module for
  `def-cbc-enhanced-diagrams-cones` (main declaration `SSet.Enhanced.coneCategory`),
  supplies the node's Mathlib simplicial conventions. The theorem uses the primitive
  `SSet`, `SSet.stdSimplex` and `SSet.horn` provided by this module's public imports;
  their source definitions and docstrings were inspected.
- `Sheaf.CategoryTheory.RightAnodyne`, `SSet.rightAnodyneExtensions`, recorded by
  the already landed `def-coef-infinity-right-anodyne`. This dependency is added to
  the item's `stmt_deps`, as authorized for landed notions, instead of duplicating it.
- Mathlib `AugmentedSimplexCategory.inclusion` and its ordinal-concatenation tensor
  (`AugmentedSimplexCategory.tensorObj`, `tensorHom`), `Functor.ran`, `Functor.lan`,
  `externalProductBifunctor`, `Functor.whiskeringLeft`, and `Prod.sectL` provide real
  construction data and their functoriality. Their signatures and relevant source
  documentation were read. Kan extensions are determined by their universal properties;
  this uses no unspecified existence witness and no postponed property theorem.

The three join/cone helpers belong to the notions explicitly introduced by this item
and are listed in `lean.declarations`, each with a source and blueprint docstring.
No new independent definition node or dependency module is needed.

Edge cases checked mathematically before writing:

- Empty `A`: its cone is the point, and the theorem includes its inclusion into `B`'s cone.
  The degree-minus-one singleton ensures the added point is retained even for empty `A`.
- Empty `A=B`: the induced map on their point cones is an isomorphism, hence right anodyne.
- `f` an identity or isomorphism: functoriality gives the corresponding identity or
  isomorphism of cones, contained in the specified class.
- The boundary inclusion in dimension zero: its cone is the last horn of `Δ[1]`,
  with positive index `1`, so no dimension-zero horn or nonemptiness is assumed.
- Arbitrary universe `u`, arbitrary simplicial sets, and arbitrary degreewise injections
  are retained; there is no finiteness, connectedness or fibrancy restriction.

Searches made (the wrapper also records the service results in `searches.jsonl`):

- `msearch.py leanfinder`, "For a degreewise injective map of simplicial sets the map of
  right cones is right anodyne": eight hits, chiefly `SSet.modelCategoryQuillen.I`,
  `.J`, and their boundary/horn lemmas. These concern the all-horn Quillen class,
  not this right-cone statement.
- `msearch.py loogle`, `"horn", "anodyne"`: two hits,
  `SSet.anodyneExtensions.horn_ι` and `SSet.innerAnodyneExtensions.horn_ι`;
  neither states the cone-monomorphism result.
- `msearch.py grep`, `right.?anodyne|rightAnodyne|join.*anodyne|anodyne.*join`,
  restricted to `AlgebraicTopology`: no hits.
- `msearch.py leansearch`, "join of simplicial sets ordered concatenation augmented
  simplicial sets": eight hits on `SSet.Augmented`, augmentation and augmented simplices;
  no simplicial join construction.
- `msearch.py leanfinder`, "simplicial join bifunctor using ordinal concatenation and
  augmented simplicial sets": eight hits including
  `AugmentedSimplexCategory.tensorObj`, `tensorHomOf`, `inl'` and `inr'`.
  Their source was read and their ordinal concatenation is used here.
- `msearch.py loogle`, `DayConvolution, tensorObj`: no hits (unknown short identifier
  `DayConvolution`). Direct source search found the general Day-convolution and
  Kan-extension API; it provides construction tools, not the requested theorem.
- `msearch.py grep`, `joinFunctor|rightConeFunctor|def.*[Jj]oin|` followed by
  `rightAnodyneExtensions_rightCone_map`, in `AlgebraicTopology`: one unrelated
  "adjoints" docstring, no definition or theorem match.
- Direct `rg` of Mathlib, upstream `WeilConjectures`, the upstream declaration index,
  and project `lean/Sheaf` for right-anodyne, join and cone names: only the project's
  existing right-anodyne definition and consumer theorem/docstrings were relevant.
  Exact searches for the four new declaration names found none.
- Direct upstream search for this node id found no declaration. DAG definition searches
  found the landed right-anodyne node and no existing join definition node;
  `tools/blueprint_refs.py search 'simplicial join'` returned zero blueprint matches.

No statement correction or statement dispute is needed. The source agrees with every
clause of the node. The node's other fields are preserved.

Validation: `scompile.py Q26 lem-coef-infinity-cone-mono-right-anodyne` compiled this
module successfully under both its sandbox and library module names, without warnings.
Delivery check: `deliver2.py Q26 lem-coef-infinity-cone-mono-right-anodyne --no-push`
runs the maintainer's preflight and per-file compile. The independent second reader
will supply the second-reading section and perform the actual delivery.

## Second reading by Q26

I independently opened the sandbox node, the complete Lean module, the two statement
dependency records and their modules, and the boundary-cell proof dependency and its
Mathlib source. There is no maintenance repair note for this item. The source is
Kerodon, not Stacks: I read [Lemma the project server](https://kerodon.net/tag/0196),
[Construction the project server and its surrounding conventions](https://kerodon.net/tag/016K),
[Example the project server](https://kerodon.net/tag/0179),
[Variant the project server](https://kerodon.net/tag/014U), and
[Proposition the project server](https://kerodon.net/tag/0077).
The lemma assumes only a simplicial monomorphism, with no implicit quasicategory,
Kan, nonemptiness, or finiteness hypothesis. Its first assertion is exactly this node.

Here is my object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. Simplicial sets, standard simplices and horns use the conventions of
   `def-cbc-enhanced-diagrams-cones`: the public import of its recorded
   `Sheaf.CategoryTheory.EnhancedDiagramsCones` supplies Mathlib's `SSet`, `stdSimplex`
   and `horn`. I opened `StdSimplex.lean` and `Horn.lean`: `stdSimplex` is
   `uliftYoneda`, and horn membership says the simplex misses a vertex other than
   the specified index. This is the node's meaning. PASS.
2. For arbitrary simplicial sets `X,Y`, introduce their join with pure `X` and `Y`
   terms and mixed terms `X a × Y b` for `a+b+1=r`: `joinAugmentationFunctor`
   augments by a terminal type at the empty ordinal, and `joinFunctor` takes the
   external product followed by left Kan extension along ordinal concatenation and
   restriction to nonempty ordinals. I read `Functor.ran`, `Functor.lan`,
   `externalProductBifunctor`, and the augmented-simplex tensor definitions. At `[r]`
   the left-extension indexing objects are maps `[r] → [a] ⋆ [b]`. Each determines
   the cut given by the inverse image of the first block. Within a fixed cut the
   object consisting of that cut and its identity concatenation is terminal: the
   unique arrow to it is given, in the opposite category, by the restrictions of
   the original map to the two blocks. Colimits therefore give exactly the
   coproduct over cuts, with the empty blocks contributing the two pure terms.
   This identifies the construction with the node's join. PASS.
3. Simplicial operators restrict ordered `X`-vertices followed by `Y`-vertices:
   `AugmentedSimplexCategory.tensorHomOf` sends the first block by the first map
   and the second by the second, using `Fin.castAdd` and `Fin.natAdd` respectively.
   I checked `monoidalCategoryOp` in `Monoidal/Opposite.lean`: its tensor object is
   `op (unop X ⊗ unop Y)`, so taking the category opposite preserves block order.
   Precomposition pulls the cut back and applies the two restricted operators,
   exactly as in the source Construction the project server. PASS.
4. The right cone is `X ⋆ Δ[0]`, with base `X` and a new final vertex:
   `rightConeFunctor := Prod.sectL SSet Δ[0] ⋙ joinFunctor`. The pure-left cut is
   the base and the pure-right cut is the point. The preceding order check places
   that point last. These are canonical summands, not additional chosen data. PASS.
5. Right anodyne means the smallest class containing isomorphisms and horns with
   `n≥1` and `0<i≤n`, closed under pushouts, transfinite compositions and retracts:
   the imported, already landed `SSet.rightAnodyneExtensions` is the `sInf` of
   exactly such morphism properties. Its generator binder `i : Fin (n+1)` with
   `0 < i` gives `i≤n` and excludes `n=0`. It uses the correct right-horn class,
   with transfinite compositions in the simplicial-set size universe. PASS.
6. For every simplicial map `u:A→B`: the theorem has `{A B : SSet.{u}}`
   and `(f : A ⟶ B)`. Its universe `u` is explicitly declared and arbitrary.
   There are no extra instances on `A`, `B`, or `f`. PASS.
7. Injectivity in every simplicial degree: `(hf : ∀ (n : SimplexCategoryᵒᵖ),
   Function.Injective (f.app n))`. This quantifies over every nonnegative degree
   and adds no augmentation-degree assumption. PASS.
8. The induced map is precisely `u ⋆ id` and is right anodyne:
   `rightAnodyneExtensions (rightConeFunctor.map f)`. I opened `Prod.sectL`:
   its map is `f ×ₘ 𝟙 Δ[0]`, so this is the required functorial map, with no
   arbitrary replacement and no extra conjunct in the conclusion. PASS.

Edge cases: the mixed-index set is empty in degree zero, leaving exactly the two
vertex summands. Either empty factor of the join retains the other factor; in
particular the empty simplicial set has a one-point right cone. Empty `A`, empty
`A=B`, identities, isomorphisms, and empty sets of attached cells are included.
For the zero-dimensional boundary the coned inclusion is the final vertex
`Λ[1,1] → Δ[1]`, whose positive index is an allowed right horn. No degree-zero
horn filler or inhabitedness is required. All constructions work in arbitrary
`Type u`; different initially chosen sizes can be placed in one common universe.
Zero objects of additive categories, schemes, and characteristic play no role here.

Independent searches, using different formulations from the first reader:

- `msearch.py leanfinder`: "Ordinal sum convolution of augmented simplicial
  presheaves models their ordered join and the cone of an inclusion is a right
  horn extension" returned eight hits: horn colimit descriptions, strict-Segal
  right Kan extensions, and the all-horn Quillen generator. None is this statement
  or a simplicial join definition.
- `msearch.py loogle`: `"SSet", "cone"` returned six ordinary categorical
  cocone declarations for nondegenerate-simplex colimits, not simplicial cones.
- `msearch.py grep`: `ordinal.*sum|simplicial.*join|right.*cone|rightAnodyne`,
  in `AlgebraicTopology`, returned five hits; only the augmented-simplex tensor's
  ordinal-sum docstring was relevant. Its actual construction was read and reused.
- `msearch.py leansearch`: "The join of simplicial presheaves is Day convolution
  for ordinal sum; adjoining a final vertex sends monomorphisms to right anodyne
  inclusions" returned eight generic Day-convolution declarations. I opened
  `Monoidal/DayConvolution.lean`: this is the general left-extension interface,
  not a specialized singleton-augmentation join or the right-cone theorem.
- Direct `rg` over Mathlib's algebraic topology, upstream `WeilConjectures`, and
  project `lean/Sheaf` for join/cone/right-anodyne names and conceptual variants
  found the existing right-anodyne predicate and consumer docstrings, with no
  duplicate join or theorem. Direct DAG/upstream-name-index searches for
  `simplicial join` and all four delivered declaration names found no competing
  definition node or declaration.

Mismatches found and repaired: the theorem docstring gave only a short saturation
argument rather than the node's complete four-step proof. I expanded it to record
the single-cell refinement, its universal-property justification and endpoint map,
the explicit cone formula and its compatibility with operators, preservation of
pushouts and nonzero limits, the final-horn calculation including `n=0`, and the
final composite identification. The already stated boundary-cell dependency
`SSet.relativeCellComplexOfMono` also lacked its required proof-only import;
I added `import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`.

No mathematical mismatch was found, so the theorem signature and construction
data are unchanged. There is no statement correction, new node, or dependency
module to audit. The node copy differs from the base only in `lean` and the
already supplied `stmt_deps` addition for the landed right-anodyne definition.
`lean.statement` is verbatim equal to the theorem signature; every universe and
variable is bound. Each of the four declarations has a source/blueprint docstring,
all lines have at most 100 characters, the sole theorem proof is `sorry`, and
the three definitions contain only real functor constructions.

Second-reader validation: the prescribed `scompile.py Q26
lem-coef-infinity-cone-mono-right-anodyne
lean/Sheaf/CategoryTheory/ConeMonoRightAnodyne.lean` passed under both the sandbox
and library module names, with no warnings (16.8 s and 29.6 s respectively).
