## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedDirectImageDirectSums` states
`AlgebraicGeometry.derivedDirectImageDirectSums`, with `sorry` as its entire proof.
There are no new definitions, dependency modules, statement corrections, or disputed
statements. The node copy changes only `lean`.

The mathematical source was read at https://stacks.math.columbia.edu/tag/08DZ
(Stacks, Lemma 36.4.5); the local literature checkout is absent. Its statement and
comparison map agree with this node. The proof node
`lem-pc-derived-direct-image-preserves-direct-sums` states this same result but has
no Lean record or module on the supplied base, so it cannot yet be recorded as an
existing declaration.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`. Morphism f: `(f : X ⟶ Y)`.
- Quasi-compact: `[QuasiCompact f]`, the Mathlib condition on inverse images of
  compact opens. Quasi-separated: `[QuasiSeparated f]`, the Mathlib condition
  that the relative diagonal is quasi-compact. Neither is a condition on an
  identity morphism or an unnecessary hypothesis that the schemes themselves
  are quasi-compact.
- The unbounded derived categories use the shared sheaf-of-modules carriers
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)` and the analogous Y carrier.
  The two explicit `HasDerivedCategory` binders specify the localization models;
  `wX` and `wY` are independent and explicitly declared.
- Every set-indexed family: `(I : Type u)` and
  `(E : I → schemeDerivedQCohCategory X)`. This uses the project's established
  index-universe convention for direct sums of module sheaves. There is no
  finiteness, nonemptiness, countability, or boundedness requirement. Increasing
  the scheme/module universe also allows larger sets.
- Objects in D_QCoh: each `E i` belongs to the dependency's full subcategory,
  whose defining property is quasi-coherence of every integer-degree cohomology
  sheaf. Its underlying ambient derived object is `(E i).obj`.
- The source direct sum is `A.pt`, with `A : Cofan (fun i ↦ (E i).obj)` and
  `IsColimit A`. The target direct sum is `B.pt`, with
  `B : Cofan (fun i ↦ (schemeDerivedDirectImage f).obj (E i).obj)` and
  `hB : IsColimit B`. These cocones and universal properties are existential
  parts of the conclusion, not additional mathematical assumptions. Direct sums
  are taken in D(O_X) and D(O_Y); for quasi-coherent families these are the same
  objects as the sums in the full quasi-coherent subcategories, as explained in
  the existing `DerivedQCohDirectSums` module.
- Derived direct image: `(schemeDerivedDirectImage f).obj` and `.map`, exactly
  the recorded dependency's K-injective-derived ringed-space pushforward.
- The canonical map is
  `hB.desc (Cofan.mk ((schemeDerivedDirectImage f).obj A.pt)
    (fun i ↦ (schemeDerivedDirectImage f).map (A.ι.app (Discrete.mk i))))`.
  On the i-th injection it is the derived direct image of the injection into A.
  This is precisely the universal-property description of Mathlib's
  `sigmaComparison`, without requiring extra `HasCoproduct` hypotheses or any
  local instance/notation in the statement.
- Isomorphism: `IsIso` of that exact canonical map. Although the coproduct
  cocones are existentially chosen, uniqueness of coproducts transports this
  canonical map to any other choices by isomorphisms. Thus this says the
  comparison is invertible, independent of choices, rather than that two
  objects are abstractly isomorphic. Including coproduct existence unpacks the
  sums already present in the node; it does not impose another hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (`def-pc-scheme`, a Mathlib leaf).
- `Sheaf.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`,
  `AlgebraicGeometry.schemeDerivedQCohProperty`, and
  `AlgebraicGeometry.schemeDerivedQCohCategory` (`def-pc-derived-category`).
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage` (`def-pc-derived-direct-image`).
  This abbreviates `RingedSpace.derivedModuleDirectImage` of
  `f.toLRSHom.toShHom`, not an arbitrary functor or underived pushforward.
- Mathlib's `Cofan.mk` and `IsColimit.desc` render coproducts and their canonical
  comparison; the generic `sigmaComparison` declaration and docstring were
  read to check the direction and component maps.

Edge cases checked before drafting: the empty index type is allowed and gives
zero-to-zero comparison; singleton families give the identity comparison under
canonical identifications; zero derived objects and empty schemes are allowed;
identity morphisms satisfy the qcqs hypotheses; arbitrary unbounded complexes
are included since no cohomological bounds appear. Non-quasi-compact or
non-quasi-separated morphisms are excluded by the actual hypotheses, as in the
source. No extra separatedness, Noetherian, properness, or finite-type hypothesis
was introduced.

Searches for an existing declaration:

- `msearch.py ... leanfinder "derived direct image of quasi-coherent complexes
  preserves arbitrary direct sums"`: eight hits concerning generic derived
  functors of exact functors, no scheme-level preservation theorem.
- `msearch.py ... loogle "CategoryTheory.Limits.coproductComparison"`: no hits,
  unknown identifier. Corrected API query
  `"CategoryTheory.Limits.sigmaComparison"`: eleven hits, including the generic
  canonical map and its preservation/IsIso equivalence, no geometric theorem.
- `msearch.py ... grep 'derived.*direct.*image|pushforward.*direct sums'
  AlgebraicGeometry`: no Mathlib hits.
- `rg` on source `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, for the item id and derived-direct-image sum
  names: no matching existing statement. Project hits refer to ambient sums,
  quasi-coherent sums, the Mayer--Vietoris and tensor framework, and docstrings
  citing the still-unstated proof dependency.
- Read the DAG duplicate `lem-pc-derived-direct-image-preserves-direct-sums`:
  no `lean` record on the supplied base; hence no existing declaration to reuse.

Server validation: `scompile.py V1 lem-pc-derived-direct-image-direct-sums` compiled the module in 2.1 seconds with no warnings or errors. Every variable and universe is explicitly bound. Only the named theorem uses `sorry`; no data definitions are introduced. The dry run `deliver2.py V1 lem-pc-derived-direct-image-direct-sums --no-push` printed `OK (dry run)` after preflight and server compilation.

## Earlier second reading (a previous round; superseded)

I independently opened the node and module. The binders `{X Y}`, `f`, `[QuasiCompact f]`, and `[QuasiSeparated f]` render the qcqs morphism clause. The explicit derived-category carriers and `E : I → schemeDerivedQCohCategory X` render the family clause. The existential coproduct cocones `A` and `B` and their `IsColimit` witnesses render the source and target direct sums; `hB.desc` applied to the derived-image maps is the canonical comparison map, and `IsIso` renders that it is an isomorphism. The empty and singleton index cases remain allowed. No extra finiteness, properness, or boundedness hypothesis appears.

## Second reading by V1

I opened the item node, its proposed module, all three statement dependency nodes
and their recorded source modules. I also opened the now-landed
`Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums` declaration.
The final delivery records that existing declaration and supplies no Lean module.
The Worker report above describes the earlier proposed module; its claim that
no existing declaration was available is superseded by this reading.

Source checked independently: [Stacks Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
and [perfect.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex),
chapter conventions, section `section-total-direct-image`, and
`lemma-quasi-coherence-pushforward-direct-sums`. The local Stacks checkout is absent.
There is no standing field, characteristic, Noetherian, separatedness, or target
quasi-compactness hypothesis. Target quasi-compactness is a local proof reduction.

The node's complete object/hypothesis/conclusion list, matched to the final Lean:

- Schemes X and Y: `{X Y : Scheme.{u₁}}`. Mathlib `Scheme` is a locally
  affine locally ringed space, and `Scheme.Hom` is a locally ringed-space
  morphism. These are precisely the dependency's objects. Verdict: matches.
- Morphism f: `(f : X ⟶ Y)`. Verdict: matches, no restriction to affine schemes.
- Quasi-compact f: `[QuasiCompact f]`; quasi-separated f: `[QuasiSeparated f]`.
  Both apply to f itself; neither asserts an identity-morphism property or
  global compactness of X/Y. Verdict: matches both source hypotheses.
- Unbounded derived categories: the two `HasDerivedCategory.{w₁/w₂}` binders
  use `SheafOfModules.{u₁} (moduleRings X/Y.toRingedSpace)`. These specify
  localization models, not boundedness or geometric hypotheses.
  Verdict: matches the recorded `schemeDerivedCategory` dependency.
- Every set-indexed family: `∀ (I : Type u₁) (E : I → schemeDerivedQCohCategory X)`.
  The dependency defines this full subcategory by quasi-coherence of
  `(DerivedCategory.homologyFunctor ... n).obj K` for every `n : ℤ`.
  `(E i).obj` is its ambient derived object. Verdict: matches, all families.
- Derived image: `schemeDerivedDirectImage f`, whose definition is the shared
  ringed-space `derivedModuleDirectImage` for `f.toLRSHom.toShHom`, itself
  `(moduleDirectImage g).rightDerivedFunctor`, computed by K-injective
  resolutions. Verdict: exactly Rf_*, not underived pushforward.
- Direct sums and canonical comparison isomorphism:
  `PreservesColimit (Discrete.functor (fun i => (E i).obj))
  (schemeDerivedDirectImage f)`. I read Mathlib `PreservesColimit`,
  `sigmaComparison`, `PreservesCoproduct.of_iso_comparison`,
  `PreservesCoproduct.inv_hom`, and its IsIso instance in
  `Limits/Preserves/Shapes/Products.lean`. Preservation says every coproduct
  cocone maps to a coproduct cocone, equivalently the canonical map
  `Sigma.desc (fun i => (schemeDerivedDirectImage f).map (Sigma.ι _ i))`
  from the sum of the images to the image of the sum is invertible.
  This identifies the actual comparison, not just an abstract isomorphism.
  Ambient coproduct existence is supplied by `derivedAmbientDirectSums`;
  its source and `derivedQCohDirectSums` explain why ambient sums of these
  families are the quasi-coherent sums. Thus preservation is not vacuous.
  Verdict: matches the entire conclusion, independently of coproduct choices.

Edge cases: empty I is allowed (initial/zero coproduct), as are singleton and
infinite families, zero complexes, empty schemes, all integer cohomological
positions including degree zero, and every characteristic. No lower or upper
cohomological bound appears. `I : Type u₁` follows the established module-sheaf
coproduct size convention; the theorem is polymorphic in u₁ and in independent
localization morphism universes w₁/w₂. There are no implicit unbound parameters.

Independent searches used different words from the first worker:
`msearch.py ... leanfinder "quasi coherent derived pushforward commutes with coproducts"`
returned eight underived sheaf-pushforward identities, not this theorem;
`msearch.py ... loogle "CategoryTheory.Limits.PreservesColimit"` returned
12 generic preservation declarations; `msearch.py ... grep
"pushforward.*coproduct|derived.*direct.*sum" AlgebraicGeometry` returned zero.
Direct rg searches for coproduct/direct-sum preservation and the two theorem
names across upstream WeilConjectures, Mathlib, project lean/Sheaf and
`dag/lean_names_upstream.json` found the landed project theorem above, generic
Mathlib comparison machinery, and unrelated underived upstream coproducts.
I read the matching project theorem's full signature and docstring, rather
than relying on its name. Its proof is entirely sorry and its docstring carries
the three source proof steps. No hollow definition or private notion is added.

Mismatch found: H4, the proposed module duplicates a theorem now on the base.
Repair: remove the proposed module; change only the item's lean record to
`existing: true`, module `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums`,
declaration `AlgebraicGeometry.derivedDirectImagePreservesDirectSums`, and its
verbatim recorded signature. The node's mathematical statement is unchanged.
There are no new definition nodes, dependency modules, or statement corrections
requiring additional readings. For an existing project declaration the contract
requires no new file or compilation; the dry-run preflight validates the record.

Validation: deliver2.py --no-push printed OK (dry run); the existing-project
record passed preflight. No delivery modules remain to compile.
