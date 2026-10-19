## Worker report

The delivery states `AlgebraicGeometry.ProEtale.torsorComparisonGlue` in
`Sheaf.AlgebraicGeometry.TorsorComparisonGlue`. Its only postponed proof is the named
item theorem, with `sorry` as the entire proof. The theorem docstring includes all eight
proof steps of the node, including their source places and dependency identifiers.
The item's natural-language statement and proof have not changed. Its `stmt_deps` gains
`def-pe-comparison-torsor`, which supplies the missing pro-etale nonabelian torsor interface.
There are no dependency-record repairs and no statement correction.

The statement was read against the current blueprint file
`main-20261015/blueprint/sec-proetale-coefficients/sk-lem-pe-torsor-comparison/`
`sk-lem-pe-torsor-comparison-glue.md` and Stacks `proetale.tex`,
`lemma-compare-cohomology-nonabelian` (Tag 099X). The torsor definition was checked against
`sites-cohomology.tex`, `definition-torsor` (Tag 03AH).

Every hypothesis and conclusion is represented as follows:

| Node text | Lean |
| --- | --- |
| A scheme X | `(X : Scheme.{u})`, without affineness, quasi-compactness, quasi-separatedness, finiteness, or base-field assumptions. |
| A sheaf of groups G₀ on X_et | `(G₀ : Sheaf X.smallEtaleTopology GrpCat.{u + 1})`; `GrpCat` permits noncommutative groups. |
| A ν*G₀-torsor T on X_proet | `(T : ComparisonTorsor G₀)`. Its sheaf is on `Scheme.ProEt.topology X`. Its action is a natural sheaf morphism from `(comparisonSets X).obj (groupSets G₀) ⊗ T.sheaf`; its unit/multiplication laws use the canonical inverse images of the actual operations of G₀. Its `bijective_act` and `nonemptySieve_mem` fields express simple transitivity and local nonemptiness. |
| There is a G₀-torsor T₀ on X_et | `∃ (T₀ : CategoryTheory.Sheaf.NonabelianTorsor.{u, u + 1, u + 1} X G₀) ...`, using the dependency's existing etale torsor structure. |
| An isomorphism of torsors ν*T₀ ≅ T | `(α : ComparisonTorsor.ModelIso T₀ T)` provides the sheaf isomorphism `(comparisonSets X).obj T₀.sheaf ≅ T.sheaf` and the equivariance equation `comparisonTorsorAction T₀ ≫ α.iso.hom = (𝟙 _ ⊗ₘ α.iso.hom) ≫ T.action`. |
| Unique up to unique isomorphism | For every other `(T₀', α')`, `∃! e : T₀.sheaf ≅ T₀'.sheaf` with both the etale-action equivariance equation and `(comparisonSets X).map e.hom ≫ α'.iso.hom = α.iso.hom`. The uniqueness refers to the model together with its specified comparison, exactly as proof step 7 specifies. It does not assert that an unpointed torsor has no automorphisms. |
| T is classical | The separate conjunct `IsClassical T.sheaf` uses exactly the recorded continuity-map predicate, with all its affine presentations. It is not replaced by essential-image membership. |
| T has a trivializing etale covering | `∃ (I : Type (u + 1)) (U : I → X.Etale), ...`. Objects of `X.Etale` are actual etale morphisms to X. The clause `∀ x : X, ∃ (i : I) (y : (U i).left), (U i).hom y = x` is joint surjectivity. Each `U i`, viewed by the actual inclusion `Scheme.toProEt X`, has a `ComparisonTorsor.Trivialization`. |

A trivialization here contains bijections on every `V → U`, their naturality under
further restriction, and equivariance with the actual multiplication on ν*G₀. It therefore
says precisely that the slice restriction is isomorphic to the group sheaf with left
translation; it specifies the isomorphism, rather than only asking for an unrelated map.
The covering is a covering of X itself, with arbitrary set indexing, not just local
covers of already selected affine pieces.

The common larger section universe is `u + 1`, as in the recorded comparison adjunction,
classicality predicate, and site's size convention. The scheme/site object universe and
site morphism universe retain their original values; no equality between them is imposed.
All universes and variables are explicitly declared, and `autoImplicit` is false.

Dependency declarations used:

- `def-weil-pbc-site-comparison-morphism`: its current recorded module is
  `Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison`, read in full and publicly
  imported by the helper. That module publicly imports the original-site interface.
  This item concerns the original sites, so it uses the retained canonical
  `Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X) (Type (u + 1)) ...`
  and `AlgebraicGeometry.Scheme.preservesFiniteLimits_proEtaleSiteComparison`, whose
  original source module `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` was also read.
  The coefficient-sized `AsSmall` models are available but unnecessary here.
- `def-constructible-torsor`: `Sheaf.CategoryTheory.Sites.ConstructibleTorsor`,
  `CategoryTheory.Sheaf.NonabelianTorsor`, used literally for the etale model. Its full
  structure and `Trivialization`/`IsTrivialOver` signatures and docstrings were read.
- `det-pe-classical-definition-continuity-map`:
  `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`,
  `AlgebraicGeometry.ProEtale.IsClassical`. The full source, including the affine
  presentation and continuity map used by this predicate, was read.
- `def-pe-comparison-torsor`: this delivery's helper module, described below.

Available proof dependencies are imported without `public`: the etale-over site
localization, weakly-etale localization, slice-site localization, comparison-unit theorem,
site sheaf gluing, and site-covering axioms modules. The affine comparison and
classical-sheaves-image nodes have no recorded Lean declaration in the inspected DAG;
they are future proof prerequisites, not additional hypotheses in this statement.
The already public imports also supply the Mathlib etale site and set-sheaf definitions.

Edge cases checked before finalizing the statement:

- Empty scheme: the covering index type may be empty and joint surjectivity is then
  vacuous. The site sheaf axiom handles the empty covering and its unique empty-object
  section; no `Nonempty X` or `Nonempty I` is imposed.
- Nonaffine, non-quasi-compact and non-quasi-separated schemes are admitted. The cover
  index is arbitrary, and nothing requires affine overlaps or a finite affine cover.
- Empty sections over an individual nonempty object are admitted: `bijective_act` is
  quantified over an existing section and imposes nothing where no section exists.
  `nonemptySieve_mem` gives exactly local nonemptiness, not global nonemptiness.
- The trivial group is admitted. Noncommutative and nonconstant sheaves of groups are
  admitted; neither an abelian-group structure nor constructibility is assumed.
- A trivial torsor may have nontrivial equivariant automorphisms. Pair-compatible
  uniqueness includes `α` and `α'`, which excludes the otherwise false interpretation.
- Trivialization is on every object of the slice, including further pro-etale objects;
  it is not restricted to the etale test objects or to the selected section alone.

Searches for the item and the helper were performed with `msearch.py`, direct `rg`,
`grep -rn` for the blueprint identifier, a definition-node census, and
`tools/blueprint_refs.py search`. Full machine-recorded remote search results are in
`searches.jsonl`; the new node copies the queries and hit names into `mathlib_searches`.

- LeanFinder, “Every torsor under the inverse image of an etale group sheaf on the
  proetale site descends uniquely to an etale torsor”: eight hits, all etale-site or
  etale-morphism definitions/instances; no comparison theorem.
- Loogle, `"Torsor", "Sheaf"`: zero hits.
- Mathlib grep, `torsor|Torsor|proetale` in `CategoryTheory/Sites`: zero hits.
- LeanSearch, “torsor for a sheaf of noncommutative groups on a site and inverse image”:
  eight hits including smooth commutative-group sheaves, `OneCochain.instInv`, and
  sheaf-pushforward comparison identities; none defines the required torsor.
- LeanFinder, “nonabelian sheaf torsor on a site under a pulled back group action”:
  eight hits, including `PresheafOfGroups.H1`, `OneCocycle`, `OneCochain`, slice
  pullback, and module pullback; none defines the pro-etale torsor or its action.
- Mathlib grep, `NonabelianTorsor|ComparisonTorsor|structure Torsor`: zero hits.
- Direct project searches find only the existing etale `NonabelianTorsor`, ordinary
  additive `Sheaf.Torsor`, and a scheme Galois-cover base-change helper with a similar
  name. The additive torsor source was read and requires `AddCommGrpCat`; it cannot
  express the node's possibly noncommutative group. The upstream blueprint-id grep
  finds no existing item declaration.
- Blueprint search “torsor” gives 32 nodes; the definition-node census finds finite,
  abelian, Gm, and etale nonabelian torsors, and torsor representations/presentations.
  None supplies the missing comparison torsor on the pro-etale site. Searches for all
  twelve newly declared names found no existing collision.

Both delivered modules compiled separately, in dependency order, through the prescribed
`scompile.py` wrapper with the 60-second per-file limit. The completed combined check
reported no errors and no warnings; the helper compiled in approximately 2.4–2.8 seconds
and the item in approximately 1.9–2.1 seconds. No global build was run. Definition data
is fully constructed, and no helper theorem or extra postponed proof was introduced.

No statement dispute was found.

## New nodes

`def-pe-comparison-torsor` defines the missing notion of a nonabelian torsor under the
canonical comparison inverse image of an etale group sheaf, its canonical pulled-back
action on an existing etale torsor, its equivariant model isomorphisms, and its slice
trivializations. Its source is Stacks Tag 03AH, applied to the group inverse image of
Tag 00YV and to the comparison of Tag 099X. The node is in the item's chapter/unit,
with `blueprint.from.node = det-pe-torsor-comparison-glue` and `via = []`; the item cites
it in `stmt_deps`.

The module `Sheaf.AlgebraicGeometry.ProEtaleComparisonTorsor` contains twelve recorded
declarations. `groupSets` is just the existing forgetful sheaf functor, and
`comparisonSets` is just an abbreviation for the recorded inverse image; these do not
choose new sheaves or new functors. `groupMultiplication` and `groupIdentity` are real
sectionwise natural transformations built from G₀'s operations. `comparisonProduct`
uses Mathlib's canonical product-comparison isomorphism and the existing left-exactness
theorem. `comparisonMultiplication` and `comparisonIdentity` use the inverse product
and terminal comparisons followed by the actual images of those operations.
`ComparisonTorsor` records the precise action laws, simple transitivity and covering
local sections. `etaleTorsorAction` turns the existing dependency's sectionwise action
into its sheaf morphism, using its existing restriction-compatibility proof.
`comparisonTorsorAction` applies inverse image to that morphism and precomposes with
the inverse product comparison. `ComparisonTorsor.ModelIso` and
`ComparisonTorsor.Trivialization` express the equivariant isomorphisms needed in the
item. Every declaration has a source/blueprint docstring; none uses `sorry`.

The new definition does not duplicate the etale model: that remains exactly
`CategoryTheory.Sheaf.NonabelianTorsor`. It fills the pro-etale/noncommutative interface
that neither that specialization nor the generic abelian torsor supplies. The searches
and the distinction from existing nodes/declarations are recorded above and in the
new node's `mathlib_searches`.

## Second reading by Q34

I independently opened the item node, its blueprint source, both delivered modules,
the new definition node, and all three original statement-dependency records and
their declarations. I read Stacks `proetale.tex`,
`lemma-compare-cohomology-nonabelian` (099X), including its affine reduction, and
`sites-cohomology.tex`, `definition-torsor` (03AH), including its conventions for
noncommutative groups, morphisms, and trivial torsors. Neither source imposes a
Noetherian, finiteness, separation, base-field, or characteristic hypothesis. I also
read `sites.tex`, `proposition-functoriality-algebraic-structures-topoi` (00YV) and
its preceding construction of inverse-image operations via finite products.

The complete object/hypothesis/conclusion list, matched against the actual Lean, is:

| Node component | Lean rendering and verdict |
| --- | --- |
| Arbitrary scheme X | `(X : Scheme.{u})`. Correct; no additional scheme-property instance. |
| Group sheaf G₀ on the small étale site | `(G₀ : Sheaf X.smallEtaleTopology GrpCat.{u + 1})`. Correct; groups need not be abelian, constant, finite, or constructible. |
| The canonical ν*G₀ | `comparisonSets X` abbreviates the existing `sheafPullbackConstruction.sheafPullback (Scheme.toProEt X) ...`. `groupSets G₀` is the forgetful sheaf functor; `comparisonMultiplication` and `comparisonIdentity` transport the actual operations. Correct; no arbitrary replacement group or comparison map. |
| A ν*G₀-torsor T on the small pro-étale site | `(T : ComparisonTorsor G₀)`. Its `sheaf`, natural `action`, `one_act`, `mul_act`, `bijective_act`, and `nonemptySieve_mem` give precisely the source definition. Correct. |
| Existence of an étale G₀-torsor T₀ | `∃ (T₀ : CategoryTheory.Sheaf.NonabelianTorsor.{u, u + 1, u + 1} X G₀) ...`. Correct; literally the dependency's structure, not a private substitute or additive specialization. |
| An isomorphism of torsors ν*T₀ ≅ T | The existential `α : ComparisonTorsor.ModelIso T₀ T` contains `iso` and `equivariant`. `comparisonTorsorAction T₀` is the image of `etaleTorsorAction T₀`, preceded by the inverse product comparison. Correct, including action and arrow direction. |
| Unique up to unique isomorphism | For every competing `T₀'` and specified `α'`, `∃! e : T₀.sheaf ≅ T₀'.sheaf` satisfies both étale equivariance and `(comparisonSets X).map e.hom ≫ α'.iso.hom = α.iso.hom`. Correct: uniqueness concerns the pair with its specified comparison, as node proof step 7 requires; it does not falsely eliminate automorphisms of an unpointed torsor. |
| T is classical | The separate conjunct `IsClassical T.sheaf` is exactly the recorded continuity-map predicate. Correct; it quantifies over every `AffinePresentation`, not just essential-image witnesses. |
| T has a trivializing étale covering | `∃ (I : Type (u + 1)) (U : I → X.Etale)`, joint surjectivity `∀ x, ∃ i y, (U i).hom y = x`, and `∀ i, Nonempty (ComparisonTorsor.Trivialization T ((Scheme.toProEt X).obj (U i)))`. Correct; it is a covering of X, and each trivialization is natural and equivariant on all pro-étale slice objects. |

I checked dependency signatures rather than just names.
`ConstructibleTorsor.lean` defines precisely the general nonabelian étale torsor
used above. `ClassicalContinuityMap.lean` defines `IsClassical` by bijectivity of
the canonical colimit-to-section map for all affine presentations. The current
comparison record points to `ProEtaleSmallModelComparison.lean`; I read that module
and the retained `ProEtaleSiteComparison.lean`. Its public imports preserve the
original-site canonical set adjunction and left exactness, so using the original
sites here requires no dependency repair. I also read the exact local framework
`Comparison/Defs.lean`, the pro-étale basic module and Mathlib's pro-étale site
definition. The framework's abelian-coefficient comparison alone would not serve
set-valued nonabelian torsors; the helper correctly uses the retained set interface.

The new node `def-pe-comparison-torsor` passes a separate source reading. Its twelve
recorded declarations implement the specified operations, torsor, pulled-back action,
model isomorphism, and slice trivialization. `groupMultiplication` and `groupIdentity`
use sectionwise group operations; their restriction compatibility follows from group
homomorphisms. Mathlib's `CartesianMonoidalCategory.prodComparisonIso` and
`preservesTerminalIso` supply the canonical comparisons; I checked their signatures
and the cartesian structure on sheaves. Bijectivity after fixing a section is exactly
simple transitivity, including the empty-section case. The existing
`Sheaf.nonemptySieve` consists of arrows whose domains have a section, so membership
in the topology is precisely local nonemptiness. Slice trivializations retain the
map `V → U`, with naturality covering every slice arrow. No definition chooses data
from an undetermined existence theorem; there is no helper theorem with an unrecorded
postponed proof. The new node's chapter/unit, ancestor/via, creation, search,
dependency, empty proof and audit fields satisfy §5. The item cites it.

Edge cases: the empty scheme permits an empty covering index, and neither theorem
nor helper imposes `Nonempty X` or `Nonempty I`. Empty section sets are allowed:
`bijective_act` quantifies over an existing section, while covering-sieve membership
supplies local sections. The trivial group and noncommutative/nonconstant groups
are included. Set-indexed covers in the common larger site universe are unrestricted;
there is no quasi-compactness, quasi-separatedness, or affine-overlap hypothesis.
Site objects remain in universe `u + 1` and morphisms in `u`; section values and cover
indices use the common larger universe `u + 1`. No site-universe equality is imposed.
There is no n, coefficient ring, or characteristic parameter to restrict. Every
variable and universe is bound under `autoImplicit false`.

Independent searches used different descriptions from the worker's:

- `msearch.py ... leanfinder "Descent of principal homogeneous spaces from the weakly etale to the etale topology via inverse image"`: eight hits, all étale sites, pretopologies, forgetful functors, category instances and étaleness lemmas; no matching theorem or torsor structure.
- `msearch.py ... loogle '"Torsor", "pullback"'`: zero hits.
- Direct `rg` for `principal.homogeneous`, `nonabelian`, torsor declarations and `GrpCat` actions in Mathlib's site directories, complete upstream `WeilConjectures`, project `lean/Sheaf`, and exact local pro-étale framework: only the existing nonabelian étale structure and additive/general or finite/representable torsors. I opened upstream `CategoryTheory.Sheaf.Torsor`: it requires `AddCommGrpCat` and cannot represent the present noncommutative group. Scheme-torsor pullback and finite-torsor helpers do not state this comparison.
- A complete definition-node census using torsor/principal-homogeneous terminology found the known finite, abelian, Gm, étale, and presentation notions, not the new comparison torsor. Searching all twelve helper names and the item name in Mathlib, upstream and `lean/Sheaf` found no collision or exact existing match.

No mathematical mismatch was found, so both Lean modules and the node's mathematical
statement/proof remain as written. The only repair is metadata: `lean.statement` had
the correct signature with whitespace flattened. I replaced it with the exact
multiline substring from `theorem torsorComparisonGlue` to before `:=`, checking
that its whitespace-normalized content was identical. There is no statement
correction, dispute or dependency module, so no correction-citer audit applies.
Module/statement docstrings carry the required source and blueprint identifiers;
the theorem docstring reproduces all eight proof steps. There is exactly one theorem,
whose entire proof is `sorry`; definition implementation proofs establish the real
data's naturality. Both modules compiled through the prescribed
`scompile.py Q34 det-pe-torsor-comparison-glue <helper> <item>` invocation, separately
in dependency order, without errors or warnings (approximately 2.4 and 1.8 seconds
for the final library-location checks). No live source edits or global build occurred.
