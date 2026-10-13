## What changed

Reduced `RingTensorCohomology.derivedTensor_first_localization_models` to the
characterized first-factor localization isomorphism and its compatibility properties.
The original signature and public imports are unchanged. Two private proof imports
supply the comparison and naturality statements; their common dependency supplies
an actual construction of the unit and induced cohomology map.

`FirstLocalizationMap` constructs `firstLocalizationUnit` from the extension/restriction
adjunction and restriction-of-scalars transitivity. It constructs
`firstLocalizationCohomologyMap` by applying the given derived functor and its unique
counit-compatible model comparison. `IsFirstLocalizationMap` fixes a D-linear map
on every scalar-extension generator. Its `ext` theorem proves uniqueness, so the
pointwise choice in the main proof selects determined data, not an arbitrary witness.

The main proof chooses the characterized pointwise isomorphisms and applies the
comparison-square and naturality results. This is a decomposition, not a claim of
a sorry-free localization theorem.

## Proved and sorry left

Closed the original hole in
`RingTensorCohomology.derivedTensor_first_localization_models`
(node `lem-pc-derived-tensor-first-localization-models`).

New holes:

- `RingTensorCohomology.exists_firstLocalization_iso`
  (`lem-pc-first-localization-map`): invertibility of the characterized map.
- `RingTensorCohomology.firstLocalization_comparison`
  (`lem-pc-first-localization-comparison`): compatibility with the localized comparison.

Proved `RingTensorCohomology.firstLocalization_naturality`
(`lem-pc-first-localization-naturality`) from the explicit unit, derived-functor
uniqueness and tensor generator extensionality. Its private helper
`firstLocalizationUnit_naturality` is also proved. The explicit unit, induced map,
and `IsFirstLocalizationMap.ext` contain no sorry.

Thus one original hole is closed and two strictly smaller holes are added; this
is a decomposition with net minus one closed hole, not a complete proof of
localization. Naturality is fully proved rather than split off with a new hole.

## No longer needed

No original imports are removed: all three provide types or abbreviations in the
unchanged signature. No module is claimed removed from the targets' import closure.

Every old direct proof dependency is replaced in the item's node by the three
new reduction nodes:

- `lem-pc-balanced-derived-tensor-model`: moved to the isomorphism-existence node.
- `lem-pc-kflat-extension-of-scalars`: no longer needed by this route; its module
  `Sheaf.Algebra.Homology.KFlatModuleBaseChange` is not used by this argument.
- `lem-weil-pbc-localization-module-exact`: moved to the existence node.
- `lem-weil-pbc-localization-tensor-product`: moved to the existence node.
- `lem-weil-pbc-localization-flat`: moved to the existence node.
- `lem-pc-derived-tensor-action-naturality`: moved to the existence node.
- `def-pc-base-derived-tensor-cohomology-model`: used by all three new nodes and
  retained as a public signature import, rather than a direct proof step.

The new route resolves B over R and localizes the A-action; it does not resolve
Q over A. Only the K-flat scalar-extension step is eliminated from the planned
transitive proof route. The other nodes above remain needed below the reduction.

## Where the brief, the DAG or earlier work was wrong

The original DAG's A-resolution and K-flat scalar-extension step is unnecessary:
a K-flat R-resolution of B computes tensoring with any Q and supports localization
of the first-factor action directly. The interface of the balanced-model theorem
alone does not provide the arbitrary-model localization isomorphism or its
comparison square, so the missing transport and localization steps are stated
explicitly rather than attributed to that theorem's conclusion.

The literature files named by the nodes are absent on this machine. I read the
public Stacks sources at https://stacks.math.columbia.edu/tag/0DJ8 and
https://stacks.math.columbia.edu/tag/06Y6. LeanFinder found Tor and exact-functor
cohomology declarations, Loogle found scalar-extension and derived uniqueness
interfaces, and the recorded grep searches found no arbitrary-model localization
theorem. LeanSearch returned an internal server error and is recorded unavailable.

The unit `sk-thm-picard-semicon` has empty realized statement and step lists. This
reduction retains its affine localization route and does not bypass a realized unit.

Edge cases checked mathematically: identity localization gives model transport;
localization at a set containing zero forces Aq and D to be zero; zero complexes
and zero coefficient rings give zero modules. Naturality uses no cancellation of
the comparison map, which need not be invertible, and no flatness of D.

## New nodes

`lem-pc-first-localization-map` records the explicit canonical map, its uniqueness,
and the still-open existence of its D-linear isomorphism after localization.
The generator characterization determines the isomorphism on the equality used
by the main proof.

`lem-pc-first-localization-comparison` isolates naturality of the universal counit
and adjunction transpose with respect to the first-factor unit and the specified
termwise tensor identification. It asserts no invertibility or naturality in Q.

`lem-pc-first-localization-naturality` records functoriality of the characterized
maps for precisely the counit and cohomology equations in the original theorem.
It uses no localization hypothesis. No signatures or definitions of existing
modules are changed, and there are no forced adaptations or change records.

## Second reading by H4

1. Interface: PASS. Compared every delivered module with the repository. The only
   existing module changes two private imports and the proof body. The original
   declaration signature is byte-identical, including all section assumptions;
   its docstring, definitions and public imports are unchanged. The other three
   modules are new. There are no interface changes or forced adaptations.
2. Proof: inspected all four files. The unit is constructed from the adjunction
   and restriction transitivity, and the cohomology map from a uniquely determined
   derived-functor comparison. `IsFirstLocalizationMap.ext` proves equality of
   every characterized D-linear map, so pointwise choice determines data up to
   precisely the equality used downstream. The only textual holes are the two
   named public theorems listed above; no definition contains a hole and no
   prohibited declaration or kernel-bypass mechanism occurs. The naturality
   argument uses counit uniqueness, the unit square, cohomology isomorphisms and
   scalar-extension generators. Compilation and axiom results are recorded below.
3. Split statements: PASS. Existence/invertibility, comparison compatibility and
   the proved naturality statement are strictly separate parts of the original
   conclusion, rather than a renamed copy. Each open statement has a source,
   complete proof docstring and node. Checked identity localization, S containing
   zero, zero complexes, zero coefficient rings, and identity/zero chain maps.
   Comparison needs no localization and never assumes its maps invertible;
   the existence argument uses exact localization before extension to arbitrary D.
   Independently searched via LeanFinder for exact scalar extension and homology,
   via Loogle for derived-functor/complex-map interfaces, and via grep for
   `preservesFiniteLimits_extendScalars_of_flat|mapHomologyIso|extendScalarsComp`.
   The results are generic exactness/associativity tools, not either open theorem.
   Read `BaseDerivedTensorLocalizedNaturality` and
   `BaseDerivedTensorModelQuasiIsoOrdinaryComparison`: both keep one coefficient
   algebra and their extra invertibility/derived-category hypotheses prevent an
   immediate application to this cross-algebra unit. No hole closes in a short
   direct application. Read the Stacks sources
   [0DJ8](https://stacks.math.columbia.edu/tag/0DJ8) and
   [06Y6](https://stacks.math.columbia.edu/tag/06Y6) independently.
4. Route/pruning: PASS after report correction. The proof first uses categorical
   uniqueness and tensor-generator extensionality; remaining localization and
   comparison transport are explicitly split. Public imports supply signature
   types/abbreviations; private imports supply the two used proof results. All old
   direct proof dependencies are now enumerated under No longer needed, with
   relocated dependencies distinguished from the eliminated K-flat extension
   step. No module is claimed pruned from the targets' closure. The unit's
   `realized.statement` and `realized.steps` lists are empty; the affine
   localization route is retained and no realized step is bypassed.
5. Nodes: PASS after corrections. The item's three steps and dependency union
   match its three applications. The new nodes match the explicit unit/map,
   invertibility, comparison and naturality arguments. Their new-node metadata,
   sources, searches and Lean records were inspected. Corrected comparison and
   naturality `stmt_deps` to include the node defining their map characterization;
   recorded all three new Lean signatures verbatim rather than collapsed onto
   one line. Existing node statement/statement dependencies are unchanged.

Changes by the second reader: corrected node statement dependencies and verbatim
signature records, completed the old-dependency accounting in the report, and
added this independent review. No Lean proof, statement, definition or import
was changed; no additional hole was added or closed.

Compilation: PASS. `lcompile.py --all` compiled all four modules in import order
with exit code 0 and no errors or warnings. The first scratch axiom check was
started while the set compilation had temporarily removed its first output;
it failed only on that missing sandbox artifact and was rerun after completion.

Axiom check: PASS. A scratch module printed axioms for the explicit unit, the
cohomology map, the characterization predicate and its extensionality theorem,
the two open theorems, the proved naturality theorem and the original theorem.
The constructions, extensionality and naturality use only `propext`,
`Classical.choice` and `Quot.sound`. The two open theorems and the original
reduction also use `sorryAx`, exactly as reported; no other axiom occurs.
