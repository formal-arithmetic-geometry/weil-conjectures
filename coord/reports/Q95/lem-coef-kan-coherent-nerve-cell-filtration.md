## Worker report

The single module `Sheaf.CategoryTheory.CoherentNerveCellFiltration` states
`SSet.exists_coherent_nerve_cell_filtration`. Its only proof is `by sorry`.
The node's natural-language statement and proof are unchanged. The only DAG edits are its
`lean` record and addition of the already-landed `lem-coef-simplicial-interval-lifting`
to `stmt_deps`, to cite the existing construction of `U` and its functor on maps.
There are no new nodes, new definitions, dependency modules, or statement corrections.
No STATEMENT-DISPUTED issue remains.

Clause-by-clause correspondence:

- Small simplicial sets, simplices and horns are Mathlib `SSet.{u}`, `Δ[n]`, and
  `(horn n i).toSSet` with inclusion `(horn n i).ι`, provided by
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. No nonemptiness or fibrancy hypothesis
  on the input is added.
- The subset-poset coherent simplices and their simplex-colimit extension are the
  existing `SSet.Pinched.coherentSimplex` and `SSet.Pinched.rigidification`, imported
  through `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`. I read the signatures,
  docstrings and definitions in `PinchedRigidificationResolution`: `coherentSimplex`
  uses Mathlib `SimplicialThickening (ULift (Fin (n+1)))` with image-of-subsets maps;
  `rigidification` is `stdSimplex.leftKanExtension coherentSimplex`. Thus the contextual
  definition of C[K] for arbitrary small K is already given, with no replacement.
- The category of simplicial categories is `CategoryTheory.CoherentNerve.SCat.{u}`,
  the bundled Mathlib `EnrichedCat` with arbitrary-object enriched functors as arrows.
- `U(X)` is `Bergner.bundle (Bergner.U X)`. Its two objects are `ULift Bool`, labelled
  false and true; its forward mapping object is exactly X, its reverse mapping object
  is the existing empty simplicial set, and its diagonal mapping objects are the
  tensor unit. The tensor unit is the constant one-point simplicial set, canonically
  isomorphic to Δ[0]; this is the identical terminal simplicial-set notion, not an
  extra datum or hypothesis. `uCompose` is projection in the identity cases and empty
  elimination in the others. `Bergner.uMap f` is f on the forward hom and identity
  on the other homs; `Bergner.bundleMap` makes it an arrow in SCat. These existing
  declarations are used directly, with no duplicate U construction or laws theorem.
- `n : ℕ`, `hn : 2 ≤ n`, `i : Fin (n+1)`, `hi : 0 < i.val`, and
  `hin : i.val < n` render every numerical hypothesis. The Fin binder supplies
  0 ≤ i ≤ n, and the two inequalities select exactly the inner horns.
- `N : ℕ` and `F : ComposableArrows SCat N` give a finite chain with N transitions
  and N+1 stages. `h₀` identifies its first stage with C[Λ_i^n], and `hN` identifies
  the last with C[Δ^n]. The equation for `F.hom` fixes its composite to
  `Pinched.rigidification.map (horn n i).ι`, with the necessary equality transports.
  The chain therefore factors the specified canonical inclusion, not an arbitrary
  map with the same endpoints.
- `e l : (F.obj l : Type u) ≃ Fin (n+1)` identifies each stage's object set with
  {0,...,n}. The first and last vertex equations fix these labels to the canonical
  vertex inclusion `Pinched.vertex`. They unpack the object-set convention rather
  than imposing extra structure on the mathematical statement. Equality transports
  only reconcile the abstract colimit object with the first/last stage.
- For each `l : Fin N` and object x, the displayed equation applying `e l.succ`
  and `e l.castSucc` says that the transition functor is the identity on those
  common vertex labels. Longer transitions are composites in the finite-chain functor.
- For every transition, `r : ℕ`, `m : Fin r → ℕ` and
  `j : ∀ t, Fin (m t+1)` specify an arbitrary finite family of horn inclusions.
  `∀ t, 1 ≤ m t` excludes dimension zero. The Fin binder for j allows both outer
  horns and every interior horn, exactly 0 ≤ j ≤ m.
- The top row is the actual categorical finite coproduct arrow
  `Limits.Sigma.map (fun t ↦ Bergner.bundleMap (Bergner.uMap (horn (m t) (j t)).ι))`.
  The existential p and q are its two attaching legs. `IsPushout` on this top arrow,
  p, q and the successive `F.map'` is the ordinary enriched-category pushout in SCat.
  No arbitrary map substitutes for the U-horn inclusion, and no horn filler or
  extension property substitutes for the pushout conclusion.

Dependencies read and used:

- `def-cbc-enhanced-diagrams-cones`: `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  using its Mathlib SSet/simplex/horn primitives; its recorded `SSet.Enhanced.coneCategory`
  signature and docstring were read as instructed, though cone categories are not
  needed by this particular statement.
- `def-coef-infinity-category-of-spaces`:
  `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`, with its recorded
  `CategoryTheory.Spaces.infinityCategory` and the published subset-poset
  `SSet.Pinched.coherentSimplex`, `rigidification`, and `vertex` interfaces from
  `Sheaf.CategoryTheory.PinchedRigidificationResolution`. I read the SCat and simplex
  model declarations in `CoherentNerveInfrastructure` and Mathlib `SimplicialNerve`.
- Added landed dependency `lem-coef-simplicial-interval-lifting`:
  `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`, `SSet.Bergner.U`, `uMap`,
  `bundle`, and `bundleMap`. Read their full definitions and docstrings, and the node's
  statement and recorded theorem signature. No additional conclusion of its theorem
  is made an assumption.
- Proof dependency `def-weil-pbc-category-colimit` is the Mathlib leaf:
  `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`,
  `Cocone`, `IsColimit`, and `colimit.desc`; read its record and the generated
  colimit API source. It is imported without `public` for the proof plan.
- Proof dependency `lem-coef-infinity-right-prism-boundary`:
  `Sheaf.CategoryTheory.RightPrismBoundary`,
  `SSet.exists_right_prism_boundary_filtration`, read in full and imported without
  `public`. The module docstring and theorem docstring carry the complete seven-step
  proof from the item, including the finite-base triangulation and enriched
  mapping-out composition checks.
- Mathlib `ComposableArrows`, `Limits.Sigma.map` and `IsPushout` supply the finite
  chain, coproduct arrow, and pushout universal property without copied definitions.

Edge cases checked:

- n=0 and n=1 have no inner index; the explicit n≥2 hypothesis is precisely the node's.
  At n=2, i=1, the endpoint hollow cube is Δ[1] with its composite endpoint already
  present. The base is Δ[0], its boundary is empty, and the prism input attaches one
  positive-dimensional horn. The statement permits this single-cell chain.
- N=0 and r=0 are allowed by the finite-chain and finite-family encodings. They are
  not artificially excluded; an empty attaching family gives the ordinary empty
  coproduct pushout. The theorem can choose the nonempty families required by the
  actual inner-horn inclusion.
- m=1 with j=0 or j=1 is allowed; m=0 is explicitly excluded at every actual attachment.
- A target enriched functor may identify the two endpoints. SCat has arbitrary
  object functions, so the pushout universal property includes this case.
- The input can lie in any universe u, including u=0. Stage object carriers lie in
  Type u and are equivalent to the finite vertex set; mapping simplicial sets lie
  in SSet.{u}. No equality of independent universes, local notation, local instance,
  hidden implicit variable, or nonemptiness assumption is introduced.

Searches for an existing statement (2026-10-17):

- `msearch.py ... leanfinder "coherent realization inner horn finite enriched horn cell filtration"`:
  eight results, namely ordinary horn fillers (`SSet.Quasicategory.hornFilling`,
  `hornFilling'`, `KanComplex.hornFilling`), horn definitions and their union formula,
  and `SSet.modelCategoryQuillen.horn_ι_mem_J`; none gives the enriched finite filtration.
- `msearch.py ... loogle "CategoryTheory.SimplicialThickening, SSet.horn"`: zero hits.
- `msearch.py ... grep "SimplicialThickening|coherent.*cell|enriched.*horn" AlgebraicTopology`:
  five hits in Mathlib `SimplicialNerve.lean`; this provides the simplex model but
  not the asserted filtration. Read that source's Path, composition and enrichment.
- `msearch.py ... leansearch "coherent nerve inner horn finite enriched cell filtration pushouts"`:
  eight hits including `CategoryTheory.SimplicialNerve`, `SSet.Quasicategory.mk`,
  `HomotopicalAlgebra.AttachCells.isPushout` and generic small-object attachments.
  None states the finite filtration for the particular coherent inner horn.
- `rg` over upstream `WeilConjectures` for coherent cells/cell filtrations and the item
  id found no matching theorem. `rg` over `dag/lean_names_upstream.json` found no
  matching theorem. `rg` over `lean/Sheaf` located the consumer
  `KanCoherentNerveQuasicategory` and, decisively, the existing U construction in
  `SimplicialIntervalLifting`, which this delivery reuses. It found no filtration theorem.

Sources checked online: [00LR](https://kerodon.net/tag/00LR),
[00LS](https://kerodon.net/tag/00LS), and [00LV](https://kerodon.net/tag/00LV).
These support the hollow-cube calculation and endpoint enriched extension argument;
the finite triangulation refinement is the explicitly agent-specified support lemma
and proof already recorded in this DAG node, not a claim of a verbatim Kerodon theorem.

Validation: the final module compiled cleanly with the prescribed `scompile.py`
wrapper, both as sandbox source and as its library module path (about two seconds
per compiler invocation). There is exactly one `sorry`, the item's theorem.
The required `deliver2.py --no-push` check is run after this report is written;
the fresh second reader supplies the independent second-reading section and delivers.

## Second reading by Q95

I independently read the node, its seven proof steps, the complete delivered Lean file,
and the recorded dependency nodes and their source declarations. No repair note exists
for this item. There is no `statement_change`, no new node, and no dependency module in
this packet. The only node deltas are `lean` and the already-landed U-construction node
added to `stmt_deps`. I found no mismatch requiring a Lean or mathematical-node change;
this reading adds this report section only.

My independent object/hypothesis/conclusion checklist, with verdicts:

1. Small simplicial sets, standard simplices, and horns: Mathlib `SSet.{u}`, `Δ[n]`,
   `horn n i`, and `(horn n i).ι`, exposed by the recorded
   `Sheaf.CategoryTheory.EnhancedDiagramsCones`. These are the weakly increasing-map
   simplex and union-of-all-but-one-faces horn in the node. PASS.
2. The subset-poset coherent simplex: `Pinched.coherentSimplex` in the published
   `PinchedRigidificationResolution` module, publicly imported by the recorded
   `InfinityCategoryOfSpaces`. I opened its definition and Mathlib
   `SimplicialThickening.Path`, its inclusion-order category, union composition, and
   `SimplicialThickening.functor`: the latter maps a subset to its image under the
   monotone vertex map. The `ULift (Fin (n+1))` labels do not change the poset. PASS.
3. The contextual construction C[K] for every small K: `Pinched.rigidification` is
   exactly `stdSimplex.leftKanExtension coherentSimplex`, the simplex-colimit extension.
   `Pinched.vertex` is the canonical vertex represented in that construction, not a
   selected arbitrary object. This contextual definition is supplied by the dependency;
   it is not a hypothesis about K and needs no extra K binder in this theorem. PASS.
4. Simplicial categories and all their enriched functors: `CoherentNerve.SCat.{u}` is
   `EnrichedCat.{u,u+1,u} SSet.{u}`; `sCatCategory` has `EnrichedFunctor SSet A B` as
   its Hom. I opened that instance. It allows arbitrary object functions, including
   identifying the two attaching endpoints. PASS.
5. The two-object U(X), including the map U(f): I opened `Bergner.Two`, `uHom`,
   `uCompose`, `uComp`, `uId`, `U`, `uMap`, `bundle`, and `bundleMap` in the recorded
   `SimplicialIntervalLifting`. Its labels are `ULift Bool`, its forward Hom is X,
   its reverse Hom is the constant empty simplicial set, and both diagonal Homs are
   the terminal tensor unit. The tensor unit is the one-point simplicial set, the
   canonical model of Delta^0. The forward map of `uMap f` is f and the remaining
   maps are identities. All data are genuine constructions. PASS.
6. Numerical hypotheses: `n : ℕ`, `i : Fin (n+1)`, `hn : 2 ≤ n`, `hi : 0 < i.val`,
   and `hin : i.val < n` express exactly n >= 2 and 0 < i < n. No Kan, nonemptiness,
   finite-presentation, or coefficient hypothesis is present. PASS.
7. A finite filtration of the specified inclusion: the existential N and
   `F : ComposableArrows SCat N` encode N successive arrows on N+1 stages.
   I checked `ComposableArrows = Fin (N+1) ⥤ SCat`, its `left`, `right`, `hom`, and
   `map'`. The endpoint equalities `h₀`, `hN` and the equation for `F.hom` fix the
   composite to `rigidification.map (horn n i).ι`. Equality transports have the
   correct direction. Thus this is a factorization of the canonical map. PASS.
8. Common object set {0,...,n}: `e l : (F.obj l : Type u) ≃ Fin (n+1)` supplies
   precisely the vertex labels at every stage. The first endpoint equation identifies
   `Pinched.vertex` of each horn vertex with its standard simplex label; the second
   does the same for every simplex vertex at the last stage. These specify the labels
   implicit in the node's common-object-set assertion and add no mathematical input.
   Literal endpoint equality in the bundled category is compatible with labelled
   intermediate stages: the existential chain may use the actual endpoint objects.
   PASS.
9. Identity transition object functions: for every `l : Fin N` and every object x,
   `e l.succ ((F.map' l.val (l.val+1)).obj x) = e l.castSucc x`. This is identity
   after the common labels. Functoriality makes all longer transitions identities
   on those labels too. PASS.
10. Finite coproduct of the prescribed positive-dimensional horn maps at each step:
    `r : ℕ`, `m : Fin r → ℕ`, `j : ∀ t, Fin (m t+1)`, and `∀ t, 1 ≤ m t` have
    exactly the required quantifiers and ranges, allowing both outer horns. The top
    arrow is `Limits.Sigma.map` applied to `bundleMap (uMap (horn ...).ι)`.
    I read `Sigma.map`, which is the ordinary coproduct of those very arrows. PASS.
11. Actual enriched pushouts: the existential p and q are the two attaching legs,
    and `IsPushout top p q (F.map' ...)` is in SCat, not just in simplicial sets or
    fixed-object functors. I opened `IsPushout`: it extends the commuting square and
    asserts that its pushout cocone is a colimit. The right and bottom legs have the
    required types and orientation. No lifting property replaces this clause. PASS.
12. Existential order: N, the chain, labels and endpoint identifications are chosen
    for each inner horn; for each transition its finite family and attaching maps
    are chosen afterward. These choices are exactly those of a finite filtration;
    the theorem imposes no uniform family or bound over all n or i. PASS.

Source check: I opened [00LR](https://kerodon.net/tag/00LR),
[00LS](https://kerodon.net/tag/00LS), [00LT](https://kerodon.net/tag/00LT),
[00LV](https://kerodon.net/tag/00LV), and [00TH](https://kerodon.net/tag/00TH).
These are Kerodon identifiers, not Stacks tags, as the node explicitly records.
00LR requires an inner horn and computes its vertex and mapping-object behavior;
00LS and 00LT justify extension by the endpoint mapping object. 00LV gives the
box-extension argument into a Kan target. The present filtration has no Kan target
hypothesis: it is the node's explicitly agent-specified finite refinement, obtained
from its finite base triangulation and 00TH, which applies in dimension zero as well.
The project uses increasing endpoint-containing subsets; I checked that convention
in Mathlib rather than copying Kerodon's decreasing-subset formula unchanged.

Proof-plan and dependency audit: the theorem docstring carries all seven node steps:
unique interval factorization; face/simplex colimit via free generators; the endpoint
support test; finite base-chain triangulation; the right-prism refinement; inherited
compositions of the intermediate enrichments; and the enriched mapping-out pushout,
including coincident endpoint images. I read the recorded right-prism theorem in
`Sheaf.CategoryTheory.RightPrismBoundary`: its positive-index horns, specified sigma
vertex formula, union equation, and `IsPushout` interface match step 5. The ordinary
colimit node records Mathlib `colimit`, `Cocone`, `IsColimit`, and `colimit.desc`.
Both proof-only imports are retained. There is no missing notion, private substitute,
or dependency-interface defect requiring a new node or module.

Edge cases: n=0 and n=1 are precisely outside the node's numerical hypotheses; n=2,
i=1 is included, with a zero-dimensional cube base and empty base boundary. The
right-prism input then attaches a one-dimensional horn, so the positive dimension
bound does not discard this case. N=0 is expressible and does not falsely witness a
nonidentity composite; the `F.hom` equation still applies. r=0 is an allowed empty
attaching family, while every actual member has m>=1; m=1 and both outer horn indices
are allowed. No nonempty mapping-object assumption excludes empty or zero mapping
sets. Schemes, rings, and characteristic are absent from this statement. Universe u
is arbitrary, including zero; objects and mapping simplices are small in that u,
while the category of all such objects lives in the ambient higher universe. No
independent universe was collapsed and no extra universe-size hypothesis was added.

Independent searches, 2026-10-17:

- `msearch.py ... leanfinder "The coherent realization of an inner horn factors as
  finitely many pushouts of two-object simplicial category horn attachments"`: eight
  hits, ordinary horn fillers, horn colimit presentations and the Kan-Quillen generator
  membership theorem. I read the returned types; none asserts this enriched filtration.
- `msearch.py ... loogle '"SimplicialThickening", "IsPushout"'`: zero hits.
- `msearch.py ... leansearch "finite cellular decomposition of the rigidification of
  an inner horn inclusion"`: eight ordinary horn/filler and generator-class hits;
  no finite enriched filtration.
- Independent `rg` searches over Mathlib AlgebraicTopology, upstream WeilConjectures,
  the project's CategoryTheory/AlgebraicTopology sources and `dag/lean_names_upstream.json`
  used `rigidification`, `horn.?cell`, `coherent.?nerve`, and `hollow.?cube`, then
  inspected filtration/cell/attachment hits. I also searched the exact declaration
  name. The published consumer `KanCoherentNerveQuasicategory` cites this node;
  related rigidification equivalence and Bergner cell-stability declarations do not
  state this finite decomposition. Mathlib `SimplicialNerve.lean` supplies the subset
  construction and lists locally Kan nerve fibrancy as future work. No existing
  statement can replace this module. The existing U construction is correctly reused.

H5/H6/H8/H9 checks: this file introduces no definition and has one theorem whose
entire proof is `by sorry`. Its module and declaration docstrings identify the source
and blueprint; the declaration has the complete seven-step proof plan. It has no
private/local definition, local notation, local instance, hidden `let`/`show` in the
signature, overlong line, or unbound variable/universe. The node's `lean.statement`
was checked programmatically to equal the file signature verbatim. The prescribed
`scompile.py Q95 lem-coef-kan-coherent-nerve-cell-filtration
lean/Sheaf/CategoryTheory/CoherentNerveCellFiltration.lean` completed cleanly for
both sandbox and library module (1.9 and 2.2 seconds). No Lean change was needed.
