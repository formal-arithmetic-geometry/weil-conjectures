## Worker report

This is a substantive repair of returned immutable head `268160cdf427`, covering H3(1)--(5),
H8 and H9. The current shared node was compared with the retained sandbox before editing:
only its `lean` record differed. The mathematical node statement is correct and unchanged;
its earlier Lean encoding was wrong. No statement correction or dependency restatement is
needed. The already landed `lem-coef-infinity-pinch-comparison` is added to `stmt_deps`
because its actual `arrowMappingSpace` definition is now used in the statement.

The module is `Sheaf.CategoryTheory.SimplicialCompositionSpine`. All auxiliary declarations
are listed in `lean.declarations` and belong to this node's multiarrow construction. They
have real data. The only postponed proof is `SSet.Enhanced.simplicial_composition_spine`.

The hypotheses and clauses are represented as follows.

- Simplicial sets, quasicategories, vertices, and the nonempty string length are
  `(Q : SSet.{u}) [Quasicategory Q]`, `(n : ℕ) (hn : 1 ≤ n)`, and
  `x : Fin (n + 1) → Q _⦋0⦌`. There is one explicitly declared arbitrary universe `u`;
  no size equality, finiteness, nonemptiness of `Q`, or other hypothesis is added.
- The entire vertex restriction is `multiarrowVertices Q n`, the product of the
  recorded `evaluation` maps to `Q`. The chosen constant tuple is
  `multiarrowVertexTuple Q n x : Δ[0] ⟶ ∏ᶜ fun _ : Fin (n+1) ↦ Q`.
  `multiarrowSpace` is their categorical pullback. Thus every slice `{i} × Δ[r]`
  is the constant simplex at `x i`, including all higher simplices of that slice.
  This is the fiber in Kerodon Notation the project server, not a full subcategory on vertices.
- `consecutiveArrowProduct` is the product of the existing unpinched
  `arrowMappingSpace Q (x i.castSucc) (x i.succ)`. These are precisely the node's
  two-vertex `H_Q` fibers (Kerodon Example the project server); right-pinched `mappingSpace`
  is not substituted for them.
- `multiarrowRestriction Q x a` is actual precomposition with `stdSimplex.map a`
  followed by the pullback lift. `multiarrowToArrow` uses the pullback projection
  to the existing arrow-space model. `multiarrowEdge` composes these two maps.
  `spineRestriction` is the `Pi.lift` of the consecutive-edge restrictions
  `SimplexCategory.mkOfSucc i`. The theorem states
  `SSet.modelCategoryQuillen.I.rlp (spineRestriction Q n x)` for this map itself.
  There is no existential arbitrary replacement for the restriction map.
- `I` is Mathlib's family of every boundary inclusion, indexed by all natural numbers.
  Its `rlp` therefore includes `∂Δ[0] → Δ[0]` and the zero-dimensional surjectivity
  condition. The relative-extension clause also uses the actual `SSet.boundary r`.
- `HasCoherentComposition` supplies a `SpineSectionFamily s` with
  `s n x ≫ spineRestriction Q n x = 𝟙 _` and the deformation homotopy from the
  identity to `spineRestriction Q n x ≫ s n x`, for every vertex string.
  `spineComposition Q s x y z` is definitionally `binaryArrowPair ≫ s 2 ![x,y,z]`
  followed by restriction along `δ 1`, exactly `d₁ ∘ s₂` in consecutive order.
- The full higher data are retained: all `multiarrowRestriction` maps, strict
  identity and composition equations for every ordinal map, and strict naturality
  under every simplicial map `F`. All multiarrow fibers are Kan. For every parameter
  `A`, dimension `r`, base family `v : A ⟶ consecutiveArrowProduct`, and compatible
  boundary `b : A ⊗ ∂Δ[r] ⟶ multiarrowSpace`, the proposition asserts an extension
  `c : A ⊗ Δ[r] ⟶ multiarrowSpace` with both its prescribed boundary and its base
  fixed. This is the relative choice-extension property from proof steps 3 and 5,
  in every dimension, rather than only a list of binary homotopies. For `A = Δ[0]`
  it includes nonempty, contractible choice fibers; all parameter spaces are retained.
- The identity family `e x` consists of actual points of `arrowMappingSpace Q x x`,
  with `arrowUnderlyingEdge Q x x (e x) = Q.σ 0 x`. Both unit homotopies are written
  as maps from the whole arrow space. The associativity homotopy has the full
  three-arrow product as domain and compares the two section-defined composites.
- `multiarrowMap` and `arrowSpaceMap` are actual postcomposition maps constructed
  by pullback lifts. Ordinal naturality is strict. Binary naturality is a homotopy
  between composition then `F` and `F × F` then target composition, for any target
  quasicategory and any independently chosen family of target sections. Its higher
  comparisons are the relative extensions in the target's multiarrow spaces.
- The inverse clause quantifies points `a : H_Q(x,y)_0` and `b : H_Q(y,x)_0`, then
  two actual 2-simplices. Its six hypotheses prescribe both short edges and the
  degenerate long edge of each inverse triangle. For every third vertex `z`, it
  asserts both composites of `spinePostcomposition a,b` are homotopic to their
  identities, and both composites of `spinePrecomposition a,b` likewise. The maps
  are tied to the given points and the same section family, not arbitrary inverses.
  The final clause conjugates these specified maps through any arrow/pinched
  comparison and homotopy inverse, giving both inverse homotopies in the
  right-pinched convention as well. The canonical such comparison is furnished by
  the recorded `right_pinch_comparison` theorem.

Dependency declarations read and used: `SSet.Enhanced.evaluation` and the existing
right-pinched `mappingSpace` from `Sheaf.CategoryTheory.EnhancedDiagramsCones`;
`SSet.Enhanced.arrowEndpoints`, `arrowMappingSpace`, and `arrowMappingSpaceInclusion`
from `Sheaf.CategoryTheory.RightPinchComparison`. The latter module also states the
canonical degreewise prism characterization and both inverse homotopies of
`SSet.Enhanced.right_pinch_comparison`. The full signatures and docstrings were read.
Mathlib supplies the existing internal hom, categorical pullbacks/products, standard
simplices, `SSet.Homotopy`, and `SSet.modelCategoryQuillen.I.rlp`.
The proof-dependency records were read: the spine-inner-anodyne node is not yet stated,
the pushout-product/lifting/boundary nodes are Mathlib leaves, and the homotopy-equivalence
and Kan function-space nodes have their recorded modules. No other DAG node is stated
in this delivery. The theorem docstring copies the seven-step proof plan with the nodes
used, including all relative extensions and four inverse composites.

Edge cases checked against the definitions and source: at `n = 0` the fiber is the point
and the product is empty; all ordinal maps, including constant maps and repetitions,
remain available. At `n = 1` the canonical restriction identifies the same arrow fiber.
In dimension zero the boundary is empty and relative filling gives existence of choices.
Empty `Q` gives no vertex tuples and makes no spurious nonemptiness assertion; empty
arrow fibers remain permitted. For the return's `Q = Δ[1]` example, the degenerate edge
at `x` is a point of `H(x,x)`, not `H(x,y)` for distinct endpoints, so it cannot enter the
new inverse clause at the wrong endpoints. Parameters `A` are arbitrary simplicial sets,
not assumed Kan, inhabited or finite.

Repair checklist:

1. H3(1): replaced the vertex-wise `fullSubcomplex` by the fixed-vertex pullback.
2. H3(2): replaced right-pinched product factors by the existing arrow fibers.
3. H3(3): defined the canonical restriction and stated `I.rlp` for it.
4. H3(4): replaced untyped equivalence-edge quantification by endpoint-typed points,
   both specified inverse triangles, every third vertex, and all four inverse homotopies.
5. H3(5): composition is defined by the binary spine section and the long edge;
   retained all ordinal restrictions and all-dimensional relative boundary fillers.
6. H8: every declaration has its source place and blueprint id; the theorem docstring
   gives all seven proof steps. The obsolete homotopy-equivalence helper was replaced
   by the two-specified-map predicate `AreSpineHomotopyInverses`, with its own source.
7. H9: removed both returned proof-plan-only imports. `RightPinchComparison` is now
   a public statement dependency used by the definitions. The other public import
   is Mathlib's boundary-lifting class. There are no proof-plan-only imports left.

Searches repeated in this repair:

- `msearch.py ... leanfinder "Fixed vertex fibers of simplex functor objects, canonical
  restriction to consecutive arrow spaces and coherent composition"`: eight hits,
  including `SSet.PtSimplex.MulStruct.map`, `SimplexCategory.mkOfSucc`, and standard
  simplex coordinate lemmas; no multiarrow composition theorem.
- `msearch.py ... loogle "MonoidalClosed.pre, SSet.spine"`: zero hits (the service
  reported the first identifier unknown). The actual `pre`, `pre_map`, and naturality
  signatures were then read directly from Mathlib's `Monoidal/Closed/Basic.lean`.
- `msearch.py ... grep "multiarrow|coherent.*composition|spineRestriction"
  AlgebraicTopology`: zero hits. Direct `rg` for the helper and theorem names in
  Mathlib, upstream `WeilConjectures`, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no duplicate declarations.
- Earlier retained search records (`searches.jsonl`) include LeanSearch, LeanFinder,
  Loogle and Mathlib grep: strict-Segal spine and ordinary nerve declarations do not
  give this quasicategorical theorem. The existing right-pinch model was reused.
- Source read online: https://kerodon.net/tag/01PF, specifically Notation the project server,
  Example the project server, Corollary the project server, Remark the project server, Construction the project server,
  Propositions the project server--12, and Notation the project server. These support the repaired
  fixed-vertex, section-based composition and full restriction-family interpretation.

Validation: the repaired module passed `scompile.py N2 lem-cbc-simplicial-composition-spine`
with no errors or warnings, both as sandbox and library module (2.4 s and 2.3 s).
The required final check is `deliver2.py N2 lem-cbc-simplicial-composition-spine --no-push`;
its successful OK result gates the worker's READY response. There is no
`STATEMENT-DISPUTED` flag: the defect was in the returned Lean, not in the node.

## Earlier second reading (a previous round; superseded)

The previous second reading approved the returned head and is superseded by the
maintainer's H3/H8/H9 return. It is withdrawn: in particular its assertions about the
full subcomplex, right-pinched product, and removed endpoint hypothesis were incorrect.
This worker repair awaits the independent second reader; this section records no new
independent approval.


## Second reading by N2

Independent second reading of the repaired sandbox, 2026-10-17. I opened the
sandbox node and the full module together, compared the node with the shared base,
and read the recorded dependency declarations rather than relying on their names.
The only node deltas are `lean` and the addition of the already landed
`lem-coef-infinity-pinch-comparison` to `stmt_deps`. The natural-language statement
and seven proof steps are unchanged, and there is no `statement_change` to audit.
There are no new nodes or dependency modules in this packet.

The source is Kerodon [01PF](https://kerodon.net/tag/01PF), read directly: Notation
the project server, Examples the project server--3, Corollaries the project server and the project server, Remark the project server,
Construction the project server, Propositions the project server--12, and Notation the project server. Its ambient
hypothesis is a quasicategory with the specified vertices; it adds no nonemptiness
hypothesis on individual arrow spaces or on the whole quasicategory. Its product
order in the binary composition display is reversed from consecutive-edge order;
`binaryArrowPair` consistently uses consecutive order, so the same composition is
represented. I also read the local Stacks `simplicial.tex` at
`lemma-trivial-kan` (08NM) and `lemma-trivial-kan-homotopy` (08NS), including their
proofs, for the relative extensions and section deformation used by this node.

Here is my object/hypothesis/conclusion checklist, extracted before comparing it
with the Lean. Each verdict concerns the repaired sandbox, not the withdrawn head.

1. **Objects and hypotheses:** a simplicial set `Q`, its quasicategory structure,
   an integer `n >= 1`, and an ordered string of `n+1` vertices. These are exactly
   `(Q : SSet.{u}) [Quasicategory Q] (n : ℕ) (hn : 1 ≤ n)` and
   `(x : Fin (n + 1) → Q _⦋0⦌)`. There are no other theorem hypotheses. PASS.
2. **Fixed-vertex multiarrow object:** the fiber of `Fun(Δ[n],Q)` over the constant
   diagram on the discrete vertices. `multiarrowVertices` is the product of the
   dependency's `evaluation` maps; `multiarrowVertexTuple` is the tuple of constant
   simplicial maps; `multiarrowSpace` is their pullback. Equality is imposed on
   whole parameter simplices at each vertex, not merely on their zero-simplices.
   The finite product models `Fun` out of the discrete vertex set. PASS.
3. **Consecutive arrow factors and canonical restriction:** the product is
   `consecutiveArrowProduct`, with factors the existing `arrowMappingSpace Q
   (x i.castSucc) (x i.succ)`. `multiarrowRestriction` actually precomposes with
   `stdSimplex.map a`; `multiarrowToArrow` maps the one-edge fiber to the recorded
   fixed-endpoint fiber using its pullback projections. `multiarrowEdge` and
   `Pi.lift` then define `spineRestriction`. I checked Mathlib's `mkOfSucc`: its
   endpoints are precisely `i.castSucc` and `i.succ`. No arbitrary restriction
   map is existentially substituted. PASS.
4. **Trivial Kan fibration and boundary convention:** the theorem asserts
   `SSet.modelCategoryQuillen.I.rlp (spineRestriction Q n x)`. I opened `I` and
   `MorphismProperty.rlp`: they quantify lifting against every boundary inclusion,
   indexed by all natural numbers. Mathlib's `boundary_eq_iSup` identifies this
   boundary with the union of all faces, and `boundary_zero` makes it empty at
   zero. Thus the degree-zero lifting requirement is present. PASS.
5. **Composition and identities from the same construction:** the existential
   family `s : SpineSectionFamily Q` satisfies `s n x ≫ spineRestriction ... = 𝟙 _`
   and an identity-to-section-composite cylinder homotopy for every string.
   `spineComposition` is literally `binaryArrowPair ≫ s 2 ![x,y,z]` followed by
   the long-edge restriction `δ 1`. The identity family has underlying edge
   `Q.σ 0 x`, and both unit homotopies have the whole arrow space as domain.
   The identities and composition are therefore tied to the specified face and
   degeneracy data. PASS.
6. **Associativity:** the next conjunct of `HasCoherentComposition` compares the
   two iterated `spineComposition` maps on the complete three-factor product,
   with `α_` accounting for parentheses. This retains all arrows as parameters,
   rather than just checking the assertion on points. PASS.
7. **Higher coherent homotopies:** all `multiarrowRestriction` maps are retained,
   including identity and composition equations for arbitrary ordinal maps.
   The Kan conjunct and the relative-extension conjunct quantify every `n,x,A,r`:
   a boundary map `b : A ⊗ boundary r ⟶ multiarrowSpace ...` over the fixed base
   `v` extends to `c : A ⊗ Δ[r] ⟶ multiarrowSpace ...`, with both boundary and base
   equations. This is exactly the interpretation specified in proof steps 3--5;
   it does not replace higher data with only binary homotopies. PASS.
8. **Naturality:** `multiarrowMap` and `arrowSpaceMap` are actual postcomposition
   maps. The ordinal-naturality conjunct quantifies every `F : Q ⟶ R` and ordinal
   map. Since the spine and long-edge maps are defined from those restrictions,
   their naturality follows as well. The binary-naturality conjunct compares the
   source section-defined composite with any independently chosen target section
   family satisfying its section equations. Higher comparisons are supplied by
   the same relative-extension property in the target quasicategory. PASS.
9. **Inverse edges and both operations:** `a` belongs to `H_Q(x,y)_0` and `b` to
   `H_Q(y,x)_0`. The six equations on `t,r : Q _⦋2⦌` prescribe the two short edges
   and the appropriate degenerate long edge of each inverse triangle. For every
   third vertex `z`, `AreSpineHomotopyInverses` supplies both composite-to-identity
   homotopies for the specified `spinePostcomposition` maps and both for the
   specified `spinePrecomposition` maps. These use the same `s` and the given
   points, so there is no unrelated inverse-map or endpoint assumption. PASS.
10. **Mapping-space convention:** the final conjunct transports these specified
    operations through any two-sided homotopy inverse pair `j,k` between the
    existing right-pinched spaces and arrow fibers. This is the explicit change
    of convention in proof step 7. The canonical pair exists by the already
    recorded `right_pinch_comparison`; the conclusion does not assume that pair
    as an extra theorem hypothesis. PASS.

Dependency audit: I read `EnhancedDiagramsCones.lean`, especially `evaluation`,
`IsEquivalenceEdge`, `mappingSpace` and `mappingSpaceMap`, and all of
`RightPinchComparison.lean`, including its prism formula and inverse homotopies.
Their signatures give exactly the notions used here. The arrow fiber is not the
right-pinched fiber; the repaired module correctly distinguishes them. I opened
Mathlib's `SSet.Homotopy` to check that each asserted homotopy is a cylinder map
on the full domain. I also read the recorded proof-dependency records, the source
signatures of `innerAnodyneExtensions_pushoutObjObjι'`, `rlp_monomorphisms`,
`exists_section_homotopy_equivalence` and `kan_mapping_homotopy_invariance`.
No dependency interface repair or missing helper is necessary. The two removed
proof-plan-only imports were explicitly part of the maintainer's H9 return; the
present public imports supply the definitions and boundary-lifting property used.

Edge cases: `n=0` is excluded only from the theorem's displayed fibration clause,
exactly as in the node; the multiarrow and section-family definitions still include
it. Its fixed-vertex fiber is isomorphic to the point and its consecutive-edge
product is the empty product. At `n=1` the two pullback presentations of the arrow
fiber are canonically identified by the displayed restriction. At `r=0` the empty
boundary retains existence of choices. Empty `Q` has no vertex tuples, making the
vertex-quantified assertions vacuous without asserting an object of `Q`. Empty
individual arrow spaces and empty parameters `A` are allowed. The failed old
`Q=Δ[1]` example cannot recur: a degenerate edge at `x` cannot be a point of the
fixed-endpoint space `H_Q(x,y)` for distinct `x,y`. Constant ordinal maps, repeated
vertices and all degeneracies remain included. `u` is arbitrary, all objects are
in the common ambient simplicial-set universe, and no universe equality or size
instance is added. Rings, characteristic, schemes and zero objects are inapplicable.

Independent searches, using wording different from the worker's repair searches:

- LeanFinder: "A quasicategory has contractible spaces of fillers for a composable
  string of arrows, with associative composition on fixed endpoint morphism
  spaces". Eight hits: `Quasicategory`, `QCat` bicategory structures, strict Segal
  quasicategories and nerve quasicategories; none states this multiarrow result.
- Loogle: `SSet.Homotopy, _ ⟶ _`. Eleven hits: the existing cylinder homotopy and
  its consequences, not the composition system. The existing homotopy is reused.
- LeanSearch: "For a quasicategory the fixed vertex fiber of its simplex mapping
  object maps by consecutive-edge restriction to a product of arrow fibers with
  the right lifting property against boundaries". Eight hits, including `I`,
  `J`, fibration characterizations and `Quasicategory`, but no composition theorem.
- Direct `rg` over Mathlib, upstream `WeilConjectures`, shared `lean/Sheaf`, and the
  upstream names inventory: `multiarrow`, `coherentComposition`,
  `composition_spine`, `fixed.?vertex`, `Segal.*fibration`, `spine.*[Ff]ibration`,
  and all new helper names. The fixed-vertex hits in `KanMappingRestriction` and
  `SourceAttachmentGluing` concern different slice/gluing data; I opened their
  definitions. Searches for a two-specified-map simplicial homotopy-inverse
  predicate found no existing replacement for `AreSpineHomotopyInverses`.

I independently checked each returned fault H3(1)--(5), H8 and H9 against the
repaired file. All are repaired as described above; I found no additional semantic
mismatch. Every helper has real constructed data and a source/blueprint docstring.
The one postponed theorem has all seven proof steps in its docstring, and its sole
proof is `sorry`. The node's `lean.statement` equals the file signature verbatim.
There is no file-local notation, private helper, unbound variable or universe, or
line exceeding 100 columns. The second reading changes only this report; it keeps
the correct module and node record intact.

Independent validation: `scompile.py N2 lem-cbc-simplicial-composition-spine
lean/Sheaf/CategoryTheory/SimplicialCompositionSpine.lean` passed cleanly, with no
warnings or errors, in 2.0 seconds for the sandbox and 2.2 seconds for the library
module. `deliver2.py N2 lem-cbc-simplicial-composition-spine --no-push` then
printed `OK (dry run)` for commit `2a17bfd777`: server preflight and compiles
passed, with nothing pushed. The final delivery uses the same prescribed wrapper.
