## Worker report

The module `lean/Sheaf/CategoryTheory/RelativeCoconeParameters.lean` states
`SSet.Enhanced.relative_cocone_parameters` with proof `sorry`. It uses the fixed
universe `u`, simplicial sets `C`, `D`, `B`, and `K`, quasicategory instances for
`C` and `D`, an inner fibration `U : C ⟶ D`, the degreewise tensor `B ⊗ K`, and
the recorded right join cone and inclusion.

The first conjunct renders the existence statement from Kerodon 02XG. Its
hypotheses are: arbitrary maps `a : B ⊗ K ⟶ C` and
`h : B ⊗ rightJoinCone K ⟶ D`; the strict base equation
`a ≫ U = (𝟙 B ⊗ₘ rightJoinConeInclusion K) ≫ h`; and a family
`cb : B _⦋0⦌ → rightJoinCone K ⟶ C` such that, for every vertex `b`,
`IsRelativeColimitDiagram U (cb b)`, the restriction equation
`rightJoinConeInclusion K ≫ cb b = MonoidalClosed.curry a ≫ evaluation B C b`,
and the base equation `cb b ≫ U = MonoidalClosed.curry h ≫ evaluation B D b`.
Its conclusion is an actual `c : B ⊗ rightJoinCone K ⟶ C` satisfying the
restriction equation, the vertex-by-vertex equality
`MonoidalClosed.curry c ≫ evaluation B C b = cb b`, and `c ≫ U = h`.

The second conjunct renders Kerodon 02XK with empty simplicial subset: for an
arbitrary `c : B ⊗ rightJoinCone K ⟶ C`, if every vertex restriction
`MonoidalClosed.curry c ≫ evaluation B C b` is a `U`-relative colimit, then the
transpose `MonoidalClosed.curry c` is a relative colimit for postcomposition
`((ihom B).map U)`. No extra condition on `B` or `K` is introduced, and no
cocartesian structure or other colimit-existence assumption is added.

The statement dependencies and declarations used are:

- `def-cbc-enhanced-diagrams-cones`: `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  declarations `SSet.Enhanced.diagramVertex`, `evaluation`, `constantDiagrams`,
  and the internal-hom conventions used by the signature.
- `def-coef-infinity-fibrations`: `Sheaf.CategoryTheory.InfinityFibrations`,
  `SSet.InnerFibration` from the publicly imported Mathlib inner-fibration module,
  as prescribed by the dependency record (no replacement predicate).
- `def-coef-infinity-relative-cone`: `Sheaf.CategoryTheory.RelativeInfinityCone`,
  declarations `SSet.Enhanced.rightJoinCone`, `rightJoinConeInclusion`, and
  `IsRelativeColimitDiagram`.

The proof dependencies are imported as required by the node: the enhanced functor
cone calculus, isofibration exponentiation, right-pinch comparison, relative
initial boundary criterion, Kan homotopy-pullback invariance, Kan pullback path
comparison, and Mathlib's simplicial skeleton and inner pushout-product modules.
The theorem docstring records the node's ten proof steps: functor-category
quasicategories and the corner inner fibration; mapping-space path comparison;
identification with relative initiality; skeletal extension from the vertices; and
the transposed functor-category relative-colimit argument.

Edge cases checked: `B` and `K` may be empty, disconnected, non-quasicategorical,
or non-weakly-contractible; the family of vertices is then quantified by
`B _⦋0⦌` (vacuously when there are none). No nonemptiness, cocartesian, or
additional colimit hypothesis is present. The `K = ∅` case is permitted by the
join-cone definitions, and the second conjunct allows every simplicial map `c`.

Searches for an existing declaration were made before retaining this module:

- `msearch.py ... leanfinder`: “Pointwise relative colimit diagrams for an inner
  fibration extend over any simplicial parameter with all vertex cocones fixed”;
  eight unrelated results, including `SSet.horn.isColimit` and
  `SSet.Subcomplex.MulticoequalizerDiagram.isColimit`; none states this result.
- `msearch.py ... loogle`: `"InnerFibration", "colimit"`; no hits.
- `msearch.py ... grep`: `relative.?colimit|pointwise.*cocone` in `AlgebraicTopology`;
  no hits. Direct `rg` over `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no declaration of this item.
- The source pages were opened at [Kerodon 02XG](https://kerodon.net/tag/02XG),
  Corollary the project server, and [Kerodon 02XK](https://kerodon.net/tag/02XK),
  Proposition the project server. They match the two conjuncts clause by clause.

The file compiles cleanly with `scompile.py`; the only postponed proof is the
named theorem `relative_cocone_parameters` itself.

## Second reading by NI

I independently read the node, the complete delivered module, the three statement
dependency nodes and their recorded modules, and the source statements at
[Kerodon 02XG](https://kerodon.net/tag/02XG), Corollary the project server, equation
`relative-colimit-pointwise-existence`, and
[Kerodon 02XK](https://kerodon.net/tag/02XK), Proposition the project server with A empty.
These are Kerodon sources, not Stacks tags; the node already records the missing
archival copy. 02XG assumes only an inner fibration between infinity categories
and arbitrary simplicial sets B and K. 02XK allows an arbitrary functor; this
node deliberately combines its A-empty consequence with 02XG under the common
inner-fibration hypothesis. No further ambient hypothesis is needed.

My object, hypothesis and conclusion checklist, matched in order:

1. A fixed containing universe and quasicategories C and D: `universe u`,
   `{C D B K : SSet.{u}}`, `[Quasicategory C] [Quasicategory D]`. Exact. The
   source's common containing universe is retained; no finiteness or smallness
   instance on either target is added.
2. An inner fibration U: `(U : C ⟶ D) [InnerFibration U]`. Exact. I read
   `InfinityFibrations.lean`, which publicly imports Mathlib's actual
   `SSet.InnerFibration`. Mathlib `Quasicategory/InnerFibration.lean:31-75`
   defines this by lifting against precisely the inner horns, starting in
   dimension two. No isofibration, cartesian or cocartesian hypothesis appears.
3. Arbitrary small simplicial parameters B and K: the same SSet binders, with
   no Quasicategory, Kan, contractibility, nonemptiness or dimension instances.
   Exact. Products are `⊗`, the degreewise cartesian product: I checked
   `SimplicialSet/Monoidal.lean:38-64`, including the tensor-map formula.
4. The right join cone and its inclusion: `rightJoinCone K` and
   `rightJoinConeInclusion K`. Exact. I opened `RelativeInfinityCone.lean:44-59`:
   these reuse `orderedJoinFunctor.obj (K, Δ[0])` and `orderedJoinInl K Δ[0]`,
   with the new vertex last, as the dependency node specifies.
5. The maps a and h: `(∀ (a : B ⊗ K ⟶ C)
   (h : B ⊗ rightJoinCone K ⟶ D), ...)`. Exact and arbitrary.
6. The strict base compatibility: `a ≫ U =
   (𝟙 B ⊗ₘ rightJoinConeInclusion K) ≫ h`. Exact equality expressing
   Ua = h restricted to B times K; no replacement by an equivalence.
7. The specified cocones at all vertices: `∀ cb : B _⦋0⦌ →
   (rightJoinCone K ⟶ C)`. Exact: the family is supplied before the extension
   is chosen, rather than merely asserted to exist afterwards.
8. Each specified cocone is relative colimiting: the first conjunct
   `IsRelativeColimitDiagram U (cb b)` for every b. Exact. I read the full
   dependency definition in `RelativeInfinityCone.lean:104-117`: it quantifies
   over every comparison right join cone and tests the outgoing mapping-space
   square by its canonical constant-path comparison. It introduces no extra
   colimit-existence assumption.
9. Each specified cocone restricts to a at b: the second conjunct
   `rightJoinConeInclusion K ≫ cb b =
   MonoidalClosed.curry a ≫ evaluation B C b`. Exact. I checked
   `EnhancedDiagramsCones.lean`'s definition of `evaluation`, which precomposes
   by the actual point map representing b and then uses the unit isomorphism.
   Mathlib `Monoidal/Closed/Basic.lean:146-150` curries B tensor K into
   K to Fun(B,C), so the factor order is correct.
10. Each specified cocone lies over h at b: the third conjunct
    `cb b ≫ U = MonoidalClosed.curry h ≫ evaluation B D b`. Exact and strict.
11. The extension is an actual map: `∃ c : B ⊗ rightJoinCone K ⟶ C`.
    Exact; no arbitrary comparison arrow or uncharacterized chosen object.
12. Its restriction to B times K is a: the first conclusion conjunct
    `(𝟙 B ⊗ₘ rightJoinConeInclusion K) ≫ c = a`. Exact.
13. Its restriction at every vertex is the already specified cocone: the
    second conclusion conjunct `∀ b, MonoidalClosed.curry c ≫
    evaluation B C b = cb b`. Exact equalities, simultaneously for all b.
14. Its base map is exactly h: the final conclusion conjunct `c ≫ U = h`.
    Exact. The existential is inside the quantification over all initial data.
15. The moreover clause applies independently to every c: the outer second
    conjunct starts `∀ c : B ⊗ rightJoinCone K ⟶ C`. Its sole premise is
    `∀ b, IsRelativeColimitDiagram U
    (MonoidalClosed.curry c ≫ evaluation B C b)`. Exact: it is not restricted
    to the particular extension obtained in the first conjunct.
16. The transpose is colimiting relative to postcomposition U_B:
    `IsRelativeColimitDiagram ((ihom B).map U) (MonoidalClosed.curry c)`.
    Exact: its codomain is Fun(B,C), and `((ihom B).map U)` really is
    postcomposition. The functor-to-types internal hom in Mathlib
    `Monoidal/Closed/FunctorToTypes.lean` supplies this map. The required
    Quasicategory instances for Fun(B,C) and Fun(B,D) follow from the existing
    instances at `AnodyneExtensions/Inner/PushoutProduct.lean:137-154`, with
    no extra hypotheses on B. For A empty in 02XK, every vertex is tested
    already by its zero-simplex; the higher-simplex condition adds nothing.

Edge cases: if B is empty there are no vertex data, and the unique empty-domain
extension is allowed; Fun(B,C) and Fun(B,D) are terminal simplicial sets, so the
second clause is consistent. If K is empty, the right join cone is Δ[0] and the
statement becomes the parameterized relative-initial-object assertion. If B is
Δ[0], the equations recover the one specified cocone exactly. Disconnected B,
non-Kan B or K, and non-weakly-contractible B or K are all allowed. Empty C or D
are permitted quasicategories; the input map types enforce exactly the possible
empty-domain cases. In degree zero there is no extra inner-horn requirement.
There are no rings, schemes, characteristic hypotheses, or integer parameters
in this statement, so those other standard edge cases do not apply. All four
simplicial sets live in the node's fixed containing universe u; u is arbitrary,
and every variable is explicitly bound with `autoImplicit false`.

Independent searches (different phrasing from the first worker):

- `msearch.py NI lem-coef-infinity-relative-cocone-parameters leanfinder`
  with query `Extending prescribed colimit cones on vertices over a simplicial
  set relative to an inner fibration`: eight hits, headed by
  `SSet.horn.isColimit`, `SSet.modelCategoryQuillen.J`,
  `SSet.modelCategoryQuillen.horn_ι_mem_J`, and
  `SSet.Subcomplex.MulticoequalizerDiagram.isColimit`; none is this theorem.
- `msearch.py ... loogle '"IsRelativeColimitDiagram"'`: zero hits.
- `msearch.py ... grep
  'relative.{0,20}colimit|prescribed.{0,20}cone|vertex.{0,25}colimit'
  AlgebraicTopology`: zero hits. A direct rg with the same expression over
  Mathlib's AlgebraicTopology also found none.
- Direct rg over the upstream WeilConjectures tree, the project's lean/Sheaf
  tree, and `dag/lean_names_upstream.json` for relative cocones, relative
  colimits, pointwise colimits and the item's id found related constructions,
  but no duplicate theorem. I opened upstream
  `WeilConjectures/CategoryTheory/Pro/Basic.lean:67-82`:
  `RelativeColimitPresentation` is an ordinary categorical colimit presentation,
  not this relative quasicategorical predicate. I opened the complete signature
  of `SSet.Enhanced.parameter_cone_extension` in `ParameterConeExtension.lean`:
  it treats an absolute target E and relative universality only for restriction
  to a parameter subset; it has no arbitrary inner U and fixed base h. I also
  opened `RelativeConeInitialCorner.lean`: its theorem assumes
  `IsIsofibration p` and identifies relative cones with corner initiality; it
  neither supplies this extension nor has its weaker inner-fibration hypothesis.
  Reusing the existing primitive definitions is correct; dropping this new
  theorem in favor of any of these declarations would lose its statement.

No mismatch found and no Lean or node change was needed. There are no new
nodes, dependency repair modules, or statement_change in this delivery; I checked
that only the node's lean field differs from the shared base. Every proof import
matches a recorded proof dependency, including the Mathlib skeleton and
pushout-product leaves. The public pushout-product import also provides the
functor-quasicategory instances needed to elaborate the statement. The docstring
matches the node's ten proof steps in order, including the inner-fibration-only
corner argument and the separate transposed universality argument. The module
introduces one theorem with proof `sorry` and no definition or proved helper;
its module and declaration docstrings have the exact source and blueprint id.
The node's lean.statement is byte-for-byte the theorem signature before `:=`;
all lines meet the 100-character bound.

Validation: `scompile.py NI lem-coef-infinity-relative-cocone-parameters
<RelativeCoconeParameters.lean>` compiled both sandbox and library forms
successfully, in 1.5 s and 1.8 s, with no diagnostics.
