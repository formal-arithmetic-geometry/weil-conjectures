## Worker report

The module `Sheaf.AlgebraicGeometry.ProperSmoothConnectedFibreDimensionLoci` states
`AlgebraicGeometry.proper_smooth_connected_fibre_dimension_loci`, with `sorry` only.
The natural statement is unchanged. There are no new notions, dependency modules, or
statement corrections.

Hypotheses and clauses, in statement order:

- `X S : Scheme.{u}` and `f : X ⟶ S` introduce precisely the schemes and morphism.
- `[IsNoetherian S]` is the stated Noetherian base (locally Noetherian and quasi-compact).
- `[IsProper f]` and `[Smooth f]` are properness and smoothness.
- `d : ℕ` encodes an integer d ≥ 0 without excluding any nonnegative integer.
- `hconnected` says that each geometric fibre is `ConnectedSpace`. This class includes
  nonemptiness, so both geometric-fibre assumptions are present. The chosen closure is
  `AlgebraicClosure (S.residueField s)`, in the same universe as the schemes. A geometric
  fibre is exactly `pullback f` along `Spec.map` of the residue-field embedding followed
  by `S.fromSpecResidueField s`, as prescribed by def-weil-geometric-fibre.
- `hbound` bounds the `topologicalKrullDim` of those very geometric fibres by d in
  `WithBot ℕ∞`; it uses the topological dimension, not local-ring dimension.
- The existential `U : Fin (d + 1) → S.Opens` supplies precisely the indices 0 ≤ i ≤ d.
  The first equality identifies each underlying subset with points having geometric
  fibre dimension `i.val`; thus no unspecified partition is substituted for S_i.
- Membership in `S.Opens` makes each locus open. The second conjunct makes each locus
  closed. `Pairwise ... Disjoint` gives pairwise disjointness, and `iSup U = ⊤` is coverage.
- `(U i).toScheme` is its canonical open subscheme; `(U i).ι` is its inclusion. The
  base-changed morphism is exactly `pullback.snd f (U i).ι`. Its `IsProper` and `Smooth`
  conjuncts state both required properties of f_i.
- At every point s of this open scheme, `Nonempty (f_i.fiber s)` states nonempty fibres,
  and `GeometricallyConnected (f_i.fiberToSpecResidueField s)` states geometric
  connectedness of the ordinary fibre over its residue field. These imply that its
  geometric fibre is nonempty and connected. `Scheme.IsPureDimension i.val` is asserted
  of the geometric fibre obtained using the algebraic closure of this open scheme's
  residue field. Thus the asserted geometric-fibre purity concerns the correct base.
- The last conjunct is `(pullback.snd f (U 0).ι).IsQuasiFinite`, exactly the recorded
  Stacks finite-type and isolated-fibre-point notion for f_0.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `IsNoetherian`, `IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` (including separatedness,
  universal closedness and local finite type; universal closedness implies quasi-compact).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`; its relative-dimension
  declarations are proof inputs, with `Mathlib.AlgebraicGeometry.Morphisms.Etale` imported
  privately for lem-sbc-smooth-relative-dimension-permanence.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected`: `GeometricallyConnected`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, with
  `pullback.snd` as the base-change projection. `Sheaf.AlgebraicGeometry.BaseChangeConventions`
  is publicly imported as the recorded base-change convention module; the statement uses
  its documented scheme base-change expression rather than its module-pullback functor.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: the canonical open subscheme inclusion;
  `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberToSpecResidueField`.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`: `Scheme.Hom.IsQuasiFinite`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- Private proof imports: `Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`,
  `Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure`, and
  `WeilConjectures.Mathlib.Topology.KrullDimension`. Proper/smooth base change, open
  immersion composition, and open-fibre products are in the already imported Mathlib
  modules. The locally-constant-relative-dimension proof dependency has no recorded Lean
  declaration and hence no additional import yet. Every currently recorded proof
  dependency module is represented in the imports, directly or publicly transitively.
  The convention dependency fixes no declaration of its own.

Edge cases: S empty gives empty loci and vacuous fibre statements. With d = 0, `Fin 1`
contains the zero index and no others, so its sole locus covers S. A missing dimension
has an empty open locus; the restricted morphism has vacuous fibre conditions, and
quasi-finiteness on an empty zero locus is valid. An empty fibre over an actual base
point is excluded by `ConnectedSpace`, as the node requires. Dimension is valued in
`WithBot ℕ∞`, so neither the empty dimension nor infinite dimension is accidentally
coerced to zero; the bound and connectedness exclude them. No independent smaller
universe of test fields is introduced.

Searches for reuse (2026-10-15):

- `msearch.py ... leanfinder "proper smooth connected geometric fibres clopen dimension
  loci quasi finite zero locus"`: eight hits, including finite fibres, quasi-finite
  singleton clopenness and properness, but none states the dimension-locus partition.
- `msearch.py ... loogle "AlgebraicGeometry.SmoothOfRelativeDimension,
  AlgebraicGeometry.IsProper"`: zero hits.
- `msearch.py ... grep "dimension.*[Ll]oc|[Ll]oc.*dimension|SmoothOfRelativeDimension"
  AlgebraicGeometry`: ten hits, in Smooth and Etale, defining relative dimension and
  its dimension-zero equivalence; no match for the node.
- `rg` of `dimension.*[Ll]oc|[Ll]oc.*dimension|proper_smooth_connected` over both the
  upstream WeilConjectures and project's Sheaf sources found local-dimension and
  relative-dimension material, but no existing partition theorem. Exact item-id grep
  and exact proposed-name searches in Mathlib, upstream, Sheaf and dag/lean_names_upstream.json
  found no declaration. Existing pure-dimension and quasi-finite declarations were
  reused, with no copies of their predicates.

Source inspection: read morphisms.tex labels lemma-smooth-omega-finite-locally-free
(Tag 02G1), definition-smooth-relative-dimension (02G2), and
lemma-quasi-finite-at-point-characterize (01TH). The claimed consequence agrees with
these source inputs; no mathematical dispute or node fault was found.

Validation: all compilation is via scompile.py on the server, per-file, nice 19,
two threads, 60 seconds. An initial attempt using geometricFiberAt with an identity
Over object exposed a definitional-transparency instance failure; the final signature
uses the recorded explicit pullback expression for geometric fibres instead.


## Second reading by NG

Independently read the node, its statement dependencies and their actual Lean
signatures, the delivered module, and the source passages with the statement open.
The item is an agent-formulated consequence, not a literal Stacks lemma. The source
02G1 assumes only a smooth morphism of schemes; 02G2 identifies its constant rank
with equidimensional nonempty fibres. Source 01TH assumes locally finite type,
which properness supplies here. Read morphisms.tex at labels
lemma-smooth-omega-finite-locally-free, definition-smooth-relative-dimension,
lemma-base-change-relative-dimension-d and lemma-quasi-finite-at-point-characterize,
and varieties.tex at lemma-characterize-geometrically-connected and
lemma-algebraic-scheme-dim-0. No extra ambient field, characteristic, or
Noetherian-source hypothesis is implicit in these passages.

Object/hypothesis/conclusion checklist (node order):

1. Schemes X and S and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
   PASS: arbitrary schemes in the common scheme universe; no field base imposed.
2. Noetherian S: `[IsNoetherian S]`. PASS: opened Mathlib's class; it extends
   `IsLocallyNoetherian S` and `CompactSpace S`, the scheme-Noetherian convention,
   rather than imposing a stronger condition on X.
3. Proper and smooth f: `[IsProper f] [Smooth f]`. PASS: read the actual classes.
   Proper means separated, universally closed and locally finite type, with
   quasi-compactness supplied by universal closedness. Smooth is affine-locally
   smooth ring maps, the dependency's recorded Mathlib notion.
4. Integer d >= 0: `(d : ℕ)`. PASS: exactly the nonnegative integers.
5. Every geometric fibre nonempty and connected: `hconnected : ∀ s : S,
   ConnectedSpace ...`. PASS: `ConnectedSpace` explicitly extends nonemptiness.
   The displayed pullback is precisely the dependency def-weil-geometric-fibre's
   recorded expression: `Spec.map` of the residue-field embedding into its
   algebraic closure, then `S.fromSpecResidueField s`. This is not an unrelated
   use of the module-pullback declaration in BaseChangeConventions.
6. Geometric dimension <= d: `hbound` uses `topologicalKrullDim` of that same
   pullback, bounded in `WithBot ℕ∞`. PASS: opened the dimension definition;
   these are chains of irreducible closed subsets, not local-ring dimensions.
7. S_i defined for 0 <= i <= d as the points of geometric dimension i:
   `∃ U : Fin (d + 1) → S.Opens` and the first equality of sets, with `i.val`.
   PASS: the equality fixes each locus, so the existential does not substitute
   an arbitrary partition. The indices are exactly the stipulated finite range.
8. Disjoint, open, closed, covering: openness is the type `S.Opens`, closedness
   is `∀ i, IsClosed (U i : Set S)`, disjointness is `Pairwise ... Disjoint`,
   and coverage is `iSup U = ⊤`. PASS: all four clauses, with no finiteness of
   a larger index family assumed.
9. Canonical open subschemes and their base changes: `(U i).toScheme`, `(U i).ι`
   and `pullback.snd f (U i).ι`. PASS: these are the dependency's chosen scheme
   fibre products and their projections; no arbitrary isomorphic objects or
   unrelated maps are quantified. `IsProper` and `Smooth` assert both properties.
10. Nonempty geometrically connected fibres of pure dimension i: for every
    `s : (U i).toScheme`, `Nonempty (f_i.fiber s)` and
    `GeometricallyConnected (f_i.fiberToSpecResidueField s)`, followed by
    `Scheme.IsPureDimension i.val` on its displayed geometric fibre. PASS:
    opened `fiber` and `fiberToSpecResidueField` (the ordinary pullback and its
    residue-field projection), Mathlib's geometric-connectedness class, and
    PureDimension.lean. The latter quantifies over all irreducible components
    with their subspace Krull dimension. Geometric purity is equivalent here
    to ordinary-fibre purity: these fibres are finite type over their residue
    fields, and extension to the algebraic closure preserves component
    dimensions, as in the relative-dimension base-change source. Thus this
    formulation retains the node's full purity clause, with the nonemptiness
    of both ordinary and geometric fibres also retained.
11. Quasi-finite f_0: `(pullback.snd f (U 0).ι).IsQuasiFinite`. PASS: opened
    QuasiFiniteMorphism.lean; this is locally finite type AND quasi-compact AND
    isolation of every point in its scheme fibre, precisely pqf-def-quasifinite.
    It does not silently replace finite type by Mathlib's weaker local notion.

Edge cases: empty S gives empty loci, vacuous bounds and restricted-fibre clauses;
empty X over a nonempty S is excluded by hconnected as required. The empty scheme
is allowed when S is empty. For d = 0 the index is Fin 1 and U 0 is defined;
coverage forces its sole locus to be all S. An absent dimension gives an empty
locus, whose restricted family and quasi-finiteness assertions are valid.
Bottom and infinite dimension are distinguished from natural dimensions by
WithBot ℕ∞; nonemptiness and hbound exclude them. No characteristic or perfection
assumption is present. Universe u is explicitly bound throughout; the chosen
algebraic closures stay in u and there is no smaller independent test-field
universe. Fixed canonical algebraic closures do not restrict the mathematical
case, by the dependency's independence-of-choice convention.

Independent reuse searches (2026-10-15): msearch leanfinder, query
"proper smooth family connected fibers dimension strata open closed partition",
returned eight unrelated manifold partition results; msearch loogle,
`"fiber", "dimension"`, returned no hits. msearch grep `clopen|equidimensional`
in AlgebraicGeometry returned five hits, principally quasi-finite isolated
singletons, not this theorem. Direct rg with
`dimension.{0,30}(strat|loci|clopen)|clopen.{0,30}(dim|fib)` and the proposed full
name searched upstream WeilConjectures, project Sheaf, pinned Mathlib
AlgebraicGeometry and dag/lean_names_upstream.json. Opened the nearby
FlatFibreDimensionStrata and FlatFibreDimensionStrataCover statements: they give
source opens covering generic points, not clopen dimension loci on the base.
Opened PicardFiberRankClopen: it concerns ranks of a chosen finite locally free
module, not geometric fibre dimension or purity. No exact reusable theorem was
found. Existing geometric fibre, geometric connectedness, pure dimension and
quasi-finite notions are reused, with no private predicate or second definition.

There are no new nodes, dependency modules or statement corrections to review.
No mismatch was found; the Lean and node records remain unchanged. Checked the
six-step theorem docstring against all six node proof steps, its source and
blueprint references, and the proof dependency imports. Only the theorem's
whole proof is sorry; no data definition or extra proved claim is introduced.
The maximum line length is 89, all variables/universes are explicitly bound,
and lean.statement equals the file signature verbatim.

Validation: scompile.py NG lem-weil-pbc-proper-smooth-connected-fibre-dimension-loci
compiled the delivered module cleanly on the server (1.6 s, nice 19, two threads,
60 seconds per file); its private-overlay dependencies PureDimension and
GeometricallyConnectedAlgebraicClosure also compiled separately and cleanly.
