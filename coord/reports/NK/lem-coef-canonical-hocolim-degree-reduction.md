## Worker report

The new module `Sheaf.CategoryTheory.CanonicalHocolimDegreeReduction` states
`HomotopicalAlgebra.CanonicalHocolim.degree_reduction`, with a sorry proof. Its other
declarations construct precisely this node's indexing categories, value diagrams,
canonical inclusions, comparison arrows, and augmentations. No statement correction
or new DAG node is needed. The source is Dugger, *Combinatorial Model Categories Have
Presentations*, Proposition 4.6 and Section 8 (Proposition 8.2 and Lemma 8.1), printed
pp. 186, 193--196. The PDF was opened and the proposition and Section 8 read online.
The resolved stage-1 repair note was also read: its instruction is to keep this
statement unchanged, which this delivery does.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The containing universes are explicit `u v w u' v'`. `M : Type u` with
  `Category.{v} M`, `ModelCategory M`, `HasLimits M`, and `HasColimits M` is the
  complete and cocomplete model category. `hM : CombinatorialModelCategory M` uses
  the existing locally presentable/small-generated/functorial-factorization interface.
  `D : Type v` with `SmallCategory D` puts the index and its homs in the same
  containing universe as the model category's homs. The comma objects and homs
  consequently fit in `v`; no equality of object and morphism universes is imposed.
- `A : D ⥤ SimplexCategory ⥤ M` is exactly a functor to cosimplicial objects.
  This expands Mathlib's abbreviation `CosimplicialObject M`; it avoids its
  separate category-instance transparency in comma constructions. It changes no data.
- `hReedy` says `Reedy.leftClass (monomorphisms SimplexCategory) (cofibrations M)
  (initial.to (A.obj d))` for every `d`. This is the recorded Reedy-cofibrancy
  characterization for the standard positive simplex subcategory. `hResolution`
  says every structure map of every `A.obj d` is a weak equivalence.
- `resolutionAugmentation` has actual components `B.map (SimplexCategory.const n
  ⦋0⦌ 0)` and the constant degree-zero target. Uniqueness of maps to `[0]` gives
  naturality. `degree A 0` is the node's gamma.
- `X : M` is arbitrary: there is no fibrancy, cofibrancy, or nonemptiness hypothesis.
- `DegreeIndex A X n = CostructuredArrow (degree A n) X` has objects `(d,u)`;
  the comma triangle says `(A.map a).app n ≫ u' = u`.
- `degreeValue A X n` is its projection to `D` followed by `degree A 0`, so all
  `V_n` take degree-zero values, including when `n` is positive.
- `collapseInclusion` uses `A_d([n] → [0]) ≫ u` and leaves `a` unchanged.
  `collapseValueIso` is the identity-component identification of its restricted
  degree-zero value diagram with `V_0`.
- `TotalIndex A X = CostructuredArrow (Functor.uncurry.obj A) X`. Its base is
  `D × SimplexCategory`. Mathlib uncurrying maps `(a,alpha)` to
  `(A.map a).app n ≫ (A.obj e).map alpha`, so its comma triangle is exactly
  the node's displayed condition. `totalValue` projects and evaluates this functor,
  giving `T(d,[n],u)=A_d^n`.
- `zeroBase` and `zeroInclusion` insert `[0]`, keep `u`, and insert the identity
  simplex arrow on morphisms. `zeroValueIso` identifies the restriction with `V_0`.
- The supplied `R n` and `RK` are functorial projective cofibrant replacements.
  Their `hocolim` functors are the recorded ordinary colimit after replacement.
  These parameters specify choices used to compute hocolimits, rather than impose
  additional conditions on `M`, `A`, or `X`. Their existence is the dependency's
  named `projectiveHocolimReplacement_exists` theorem; no data are chosen from it.
- `L` with `L.IsLocalization (weakEquivalences M)` is any ordinary homotopy-category
  model. `degreeComparison` and `totalComparison` apply the existing
  `hocolimReindex` to the actual inclusions, using only the identity-component
  restriction isomorphisms. No arbitrary comparison morphism is substituted.
- `hn : ∀ n : ℕ, IsIso (degreeComparison ... n ...)` renders exactly the
  degree-by-degree assumption, including `n=0`.
- The first conclusion is `IsIso (totalComparison ...)`.
- The second conclusion supplies an actual `f` between the specified hocolimit
  objects, with `L.map f = totalComparison ...`, `weakEquivalences M f`, and
  the strict equality `f ≫ augmentation RK (totalCocone A X) =
  augmentation (R 0) (degreeCocone A X 0)`.
- `totalCocone` has component `u` itself. `degreeCocone` has component
  `A_d(last vertex [0] → [n]) ≫ u`. `augmentation` composes the colimit of the
  replacement augmentation with the ordinary cocone desc. The last conclusion
  asserts the augmentation triangle for every `degreeComparison` in the ordinary
  localization. Together with the strict total triangle, these are the node's
  augmentation clauses. The auxiliary W from the proof is never given a spurious
  strict augmentation to X.

Dependencies used and read:

- `Sheaf.CategoryTheory.CompleteAlgebroid`,
  `SSet.Enhanced.Algebroid.completeCategory`: imported for the fixed containing
  universe conventions, not for extra algebroid data or assumptions.
- `Sheaf.CategoryTheory.ReedyModelStructure`,
  `HomotopicalAlgebra.Reedy.leftClass`, `relativeLatching`, and
  `simplex_reedy_structure`: the existing standard Reedy/cofibrant terminology.
- `Sheaf.CategoryTheory.HocolimReindexingZigzags`,
  `HomotopicalAlgebra.ProjectiveHocolimReplacement`, its `hocolim`,
  `hocolimReindex`, and `hocolim_reindexing_zigzags`: existing replacement and
  canonical comparison interfaces. The dependency repair is described below.
- `Sheaf.CategoryTheory.ModelColimitLocalizationComparison`,
  `HomotopicalAlgebra.CombinatorialModelCategory`: the existing combinatorial
  hypothesis, also a stated proof dependency.
- Non-public imports cover the stated proof dependencies
  `CartesianGrothendieckColimitFormula`, `InfinityMappingComposition`,
  `PointwiseEquivalences`, `InfinitySplitAugmentationColimit`,
  `ModelColimitLocalizationComparison`, and `ModelLocalizationDetectsWeakEquivalences`.
  The nodes `lem-coef-hocolim-value-diagram-naturality` and
  `lem-coef-colimit-cocone-transport-equivalence` have no recorded Lean module on
  the read base, so no import is invented for them. They remain cited explicitly
  in the proof docstring. They are proof-only prerequisites, not missing notions
  in the theorem statement.
- Mathlib `CostructuredArrow`, its `proj`, `homMk`, and `w`,
  `Functor.uncurry`, `Functor.toCostructuredArrow`, `SimplexCategory.const`,
  and ordinary colimit maps/cocones provide the actual categorical constructions.

Edge cases checked before and during writing:

- For empty D, both comma indexing constructions are empty, the hypotheses on A
  are vacuous, and the assertion compares homotopy-initial objects. No artificial
  Nonempty condition is introduced.
- At n=0 the collapse and last vertex are the unique endomorphism of `[0]`, hence
  identities. The degree comparison is the identity class; the augmentation agrees
  with the evaluation augmentation after `A.map_id`.
- For positive n, `degreeValue` still evaluates degree zero. The total comma
  equation was checked against the exact order of uncurrying's two maps.
- Constant resolutions, initial or terminal X, and nonfibrant X are all allowed.
  If a degree comma category happens to be empty, its colimit still exists.
- The strict total augmentation uses the original T cocone; replacing T by W in
  the proof does not incorrectly demand that W have a strict cocone to X.
- Actual representative existence uses cofibrancy of the source diagram and a
  projective trivial fibration of the target replacement; it never assumes
  fibrancy of X or of a hocolimit object.

Searches for an existing statement (all through the prescribed search wrapper):

- LeanFinder: `Degree zero comparison canonical homotopy colimit cosimplicial
  resolutions`. Eight hits concern cofibrant-object homotopy-category resolution
  maps and injective resolutions; none states this degree-zero reduction.
- Loogle: `"CosimplicialObject", "colimit"`. Four hits give ordinary colimit
  instances for (truncated) cosimplicial objects, not canonical hocolim comparisons.
- Mathlib grep: `cosimplicial.*colimit|colimit.*cosimplicial|canonical.*hocolim`
  in `AlgebraicTopology`. Four hits are ordinary cosimplicial colimit instances.
- LeanSearch: `A canonical homotopy colimit over cosimplicial generators is computed
  by degree zero if every cosimplicial degree comparison is a weak equivalence`.
  Eight hits give ordinary cosimplicial limits/colimits, subcomplex colimits and
  homological colimit results; no matching theorem.
- `rg` of upstream `WeilConjectures` and `lean/Sheaf` for
  `canonical.*hocolim|hocolim.*degree|cosimplicial.*resolution|CosimplicialResolution`
  found no exact statement. The landed Dugger presentation module mentions this
  node in its proof, and the framed-horn module supplies an augmented resolution
  structure, not this theorem. The exact node-id search in upstream returned no hit.
- Full candidate-name search of Mathlib, upstream and side sources for
  `degree_reduction|collapseInclusion|degreeComparison|totalComparison|CanonicalHocolim`
  found no collision in the selected namespace. Other `totalComparison` hits are
  in unrelated tensor and simplicial-Grothendieck namespaces.
- `dag/lean_names_upstream.json` has no matching canonical-hocolim declaration.

No STATEMENT-DISPUTED flag is warranted. The node statement and all existing fields
except its Lean record are preserved. All definitions have actual data. The sole
new postponed theorem is the item's own `degree_reduction`; the dependency's
existing postponed theorems remain matched with their original node and docstrings.

## Dependency modules

`lem-coef-hocolim-reindexing-zigzags`: the recorded
`ProjectiveHocolimReplacement` supplied a cofibrant replacement diagram and a
weak-equivalence augmentation, but omitted the fibration property of that
augmentation. Its own existence proof constructs the augmentation by factoring
initial-to-diagram as a cofibration followed by a **trivial fibration**. The
consumer's last proof step needs exactly this property to lift the source
cofibrant diagram and obtain an actual comparison over X. An arbitrary weak
augmentation would not provide that strict lifting problem.

Under §1(B), the delivered copy of the dependency module adds the field
`augmentation_fibration : ∀ V i, fibrations M ((augmentation.app V).app i)`
and clarifies the structure docstring. With the retained
`augmentation_weakEquivalence` and objectwise projective fibration equality,
this states precisely the standard replacement construction already specified
in the node and its proof. The construction and signatures of `hocolim`,
`hocolimReindex`, and all original theorems are preserved. The dependency JSON
changes only `lean`, with its required explanatory `lean.note`.

Consumer validation: the new theorem accepts only the repaired recorded
replacement type, constructs both canonical comparison classes using the
retained roof API, and states the actual weak-equivalence/strict-over-X conclusion.
Both delivered files are compiled separately in dependency order through
`scompile.py`, including their library module paths. A source search of the read
side library found no external record literals constructing the old replacement
structure that would need the new proof field supplied.

## Second reading by NK

Independent maintainer second reading of immutable delivery
`3a88128d68b22d3bebccc0fefb0cd536ba401ea9`, performed on 2026-10-17.
This section records the independent review requested by the launcher; it does not
claim that a second NK worker reviewed the delivery before submission.

I read the packet, check-brief2.md, the item and all three statement-dependency
nodes, both delivered modules in full, the worker report, and the exact dependency
interfaces in the read-only NK clone. I reopened Dugger's PDF, Proposition 4.6
(printed p. 186), Section 8 including Lemma 8.1, Proposition 8.2 and the proof on
printed pp. 193--196, and Appendix A.3--A.5. The source distinguishes the degree-n
index category from its degree-zero value diagram; the delivery preserves that
distinction. Proposition 4.6 does not require fibrancy of X.

Clause checks, all satisfactory:

- `M`, its model structure, limits and colimits, and `hM` give the complete,
  cocomplete combinatorial model category. `CombinatorialModelCategory` is the
  existing dependency structure, including both functorial factorizations.
  `hReedy` uses the recorded relative-latching `Reedy.leftClass` with the positive
  simplex maps; `simplex_reedy_structure` identifies those with injections.
  `hResolution` quantifies over every cosimplicial structure map.
- `A` is the given family, and `degree A 0` is gamma. `X` is arbitrary.
  `resolutionAugmentation` uses the unique collapses to degree zero.
- `DegreeIndex` reuses Mathlib's `CostructuredArrow`: its triangle is exactly
  A(a) followed by u' equals u. `degreeValue` projects to D and evaluates degree
  zero for every n. `collapseInclusion` precomposes with the collapse, preserving
  the underlying D-arrow. `collapseValueIso` has identity components.
- `TotalIndex` is the costructured arrow of Mathlib's uncurrying. I checked
  `Functor.uncurry`: its arrow is A(a) in source degree followed by A_e(alpha),
  giving precisely the required total-index triangle. `totalValue` evaluates at
  the actual degree; `zeroInclusion` and `zeroValueIso` give the required inclusion.
- `R` and `RK` specify projective replacements, and `L` specifies an arbitrary
  ordinary localization. These specify models for the constructions, not new
  restrictions on A or X. Both comparison definitions use `hocolimReindex` and
  the identity-component restriction isomorphisms, not arbitrary maps.
- `hn` covers every natural degree including zero. The first conclusion makes
  the specified total comparison invertible. The second supplies an actual weak
  equivalence representing that same comparison and commuting strictly over X.
  The third gives every degree-comparison augmentation triangle in localization.
  `totalCocone` is the original u-cocone; `degreeCocone` uses the last vertex.
  Collapse composed with that vertex is the identity on [0]. No false strict
  augmentation of the auxiliary W is used.

I checked the six proof steps against their cited statements. The collapse
transformation T to W is objectwise weakly equivalent and identity on degree zero.
The contravariant fiber transitions give exactly the Cartesian total category K;
W sends transport arrows to identities. The localization and Cartesian colimit
interfaces supply the coherent fiber diagram and its total comparison. The
constant split augmentation and cocone-transport result supply the outer colimit
without presupposing its existence. Finally, projective cofibrancy lifts through
the restricted trivial fibration, giving the representative strictly over X;
localization detection needs no endpoint fibrancy. The value-diagram naturality
node is proof-only, and its needed square is also already present in the delivered
`hocolim_reindexing_calculus`; there is no missing statement-level construction.

The accompanying section 1(B) dependency repair is sound. The original interface
omitted the fibration property required for the last lift. Adding
`augmentation_fibration` records the standard trivial-fibration replacement of
its existing existence proof. All other replacement data, canonical roofs and
zigzag conclusions remain intact, and the dependency's `lean.note` explains the
repair. No replacement is selected from a bare Nonempty assertion.

Edge cases checked: empty D and empty comma categories, n=0, constant resolutions,
initial or terminal X, and nonfibrant X. There is no Nonempty or endpoint
cofibrancy/fibrancy assumption. Independent universes u and v are retained; D and
its comma categories are small in the containing hom universe v, as required by
the recorded projective interface. No equality of model-object and hom universes
is imposed. The node allows enlarging the containing universes.

Independent rg searches in Mathlib's AlgebraicTopology tree, upstream
WeilConjectures, the side CategoryTheory modules and the upstream-name index found
no existing degree-reduction theorem. The framed-horn resolution structure is
an augmented resolution interface, not this comparison theorem; this delivery
reuses the existing Reedy predicate rather than introducing a duplicate resolution
structure. Mathlib CostructuredArrow and uncurrying are reused directly.

Both delivered lean.statement strings occur verbatim as the exact theorem
signatures, and the declaration lists cover the owning declarations (17 and 8).
All declarations have source/blueprint docstrings, with the six-step proof in the
item theorem docstring. All theorem proofs are sorry; definition fields contain
real constructions and their elementary coherence proofs. There are no hollow
definitions, axioms, extra hypotheses, overlong lines, or pro-etale substitutions.
No statement correction or citer audit is required.

Compiler reproduction:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py NK lem-coef-canonical-hocolim-degree-reduction snapshot/lean/Sheaf/CategoryTheory/HocolimReindexingZigzags.lean snapshot/lean/Sheaf/CategoryTheory/CanonicalHocolimDegreeReduction.lean`

Exit status 0. The wrapper compiled the repaired dependency in its private overlay
(2.0 seconds), preliminary dependency (2.1), dependency sandbox (1.9), dependency
library path (2.2), consumer sandbox (2.2), and consumer library path (2.2), with no
reported errors or warnings. The installed wrapper currently dispatches the
private-overlay work to the server, so this is server-confirmed wrapper evidence,
not a claim of a separate local compiler run. No direct SSH command or global
build was run, and no clone, live Lean file, or delivery branch was edited.

Finding and correction: H11, the submitted second-reading section was only a
notice that no reading had occurred. This complete replacement report preserves
the Worker report and Dependency modules sections and replaces that notice with
this actual independent reading and compiler evidence. No Lean or JSON change
is needed. Verdict: FIX (report only); substance accepted.
