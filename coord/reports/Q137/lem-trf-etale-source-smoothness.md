## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource` states both clauses of
`lem-trf-etale-source-smoothness`, in two theorems with `sorry` proofs. It introduces no
new definition, changes no statement, and repairs no dependency record.

Source read: `literature/stacks-project/descent.tex`, Tag 036U,
`lemma-smooth-smooth-local-source`, statement and proof at lines 6928 onward. This states
smooth locality on the source; étale source maps are smooth. The pointwise argument is
the node's restriction-to-neighbourhood argument using the openness of flat locally
finitely presented maps (Tag 01UA, the docstring and instance
`UniversallyOpen.of_flat` at Mathlib `Morphisms/UniversallyOpen.lean:145–149`).
No repair note for this item was present in `coord/repair-notes/`.

Hypothesis and clause matching:

- Schemes and the original morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- An arbitrary indexed source family: `{I : Type v} (U : I → Scheme.{u})`
  and `(h : ∀ i : I, U i ⟶ X)`. The index universe is independent of the scheme
  universe; there is no cardinality or nonemptiness restriction.
- Every source map is étale: `[∀ i : I, Etale (h i)]`.
- Joint surjectivity on points, exactly as spelled out in the node:
  `hcover : ∀ x : X, ∃ (i : I) (y : U i), h i y = x`.
- The global conclusion is `Smooth f ↔ ∀ i : I, Smooth (h i ≫ f)` in
  `AlgebraicGeometry.smooth_iff_of_jointly_surjective_etale`.
  Category composition `h i ≫ f` is the node's `f ∘ h_i`.
- No separatedness, quasi-compactness, Noetherian, finite-type or finite-presentation
  assumption on `f`, `X` or `S` occurs in either theorem.
- For the pointwise assertion the independently bound morphism and point are
  `{U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S) [Etale h] (u : U)`.
  In `AlgebraicGeometry.smooth_at_iff_of_etale`, the left side
  `∃ V : X.Opens, h u ∈ V ∧ Smooth (V.ι ≫ f)` is smoothness on an open
  neighbourhood of `h u`. The right side
  `∃ W : U.Opens, u ∈ W ∧ Smooth (W.ι ≫ h ≫ f)` is smoothness of the
  composite on an open neighbourhood of `u`. In particular `h` need not be
  globally surjective, nor `f` globally locally of finite presentation.
  The two existentials use the existing open-subscheme inclusions, with no
  second pointwise smoothness predicate or artificial assumptions.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` (locally affine locally ringed spaces) and
  `AlgebraicGeometry.Scheme.Hom` (morphisms of locally ringed spaces).
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`; its full affine-local signature and docstring at
  lines 38–45 were read, together with `Etale.iff_flat_and_formallyUnramified`
  at 140–144 and the étale-implies-smooth instance. These are the dependency's
  recorded realization, not a private replacement.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`; the docstring and full signature at lines 58–66
  were read. The node's recorded realization uses Stacks 02H6 to identify this
  affine-local definition with locally finitely presented formally smooth maps.
- All already stated proof dependencies are imported. They include
  `AlgebraicGeometry.Smooth.of_comp_of_flat_of_surjective` from
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`, whose full
  docstring and signature were read at lines 671–681; and
  `AlgebraicGeometry.smooth_and_fibre_dimension_zero_of_etale` from
  `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`, whose module and
  proof docstring were read in full. The proof-only imports also expose
  `smooth_comp`, `UniversallyOpen.of_flat`, `IsOpenImmersion.lift`,
  `lift_fac`, `lift_uniq`, `Scheme.Hom.resLE`, and
  `IsZariskiLocalAtSource.iff_of_iSup_eq_top`, the Mathlib matches of the
  remaining proof dependencies. The theorem docstrings retain all four proof
  steps, including the open-image factorization in the reverse direction.

Edge cases checked against the statement:

- Empty `I` is allowed: `hcover` then forces `X` to have no points; the right
  side is vacuous and a morphism from the empty scheme is smooth.
- Empty `U i` members and repeated cover members are allowed; no individual
  surjectivity or nonempty-fibre hypothesis is imposed.
- The identity family reduces the global equivalence to itself. Open-immersion
  covers give the usual Zariski-local version.
- The pointwise theorem applies to an open immersion whose image is a proper
  open subset. This checks that it has no hidden global surjectivity requirement.
- Empty `U` has no point `u`; nonempty schemes and fields of arbitrary
  characteristic are unrestricted. Non-Noetherian bases and non-quasi-compact
  covers are admitted.
- An arbitrary morphism can be smooth near one point without being locally of
  finite presentation everywhere. The inline neighbourhood existentials retain
  this case. Mathlib's `Scheme.Hom.smoothLocus` at Smooth.lean:305 requires
  `[LocallyOfFinitePresentation f]`; that API would improperly restrict this node.

Searches performed for an existing statement:

1. `msearch.py Q137 lem-trf-etale-source-smoothness leanfinder
   "Smoothness of a scheme morphism is etale local on the source, and smoothness
   at a point is invariant under etale precomposition"`: eight hits, including
   `IsEtale.instIsSmooth`, smooth chart equivalences and `IsEtale.of_comp`.
   None states descent for a jointly surjective family or this pointwise assertion.
2. `msearch.py ... loogle "AlgebraicGeometry.Smooth, AlgebraicGeometry.Etale"`:
   one hit, `AlgebraicGeometry.Etale.instSmooth`; only the forward implication's
   étale-implies-smooth ingredient.
3. `msearch.py ... grep
   "smooth.*[Ll]ocal|[Ss]mooth.*[Dd]escent|[Ss]moothAt|smoothLocus"
   AlgebraicGeometry`: twelve hits, in Smooth, SmoothFiber and Group/Smooth;
   source inspection found source locality and fibre criteria, not this statement.
4. `msearch.py ... leansearch "Smoothness of a scheme morphism descends along
   a jointly surjective etale family on its source, and smoothness at a point is
   invariant under etale precomposition"`: eight hits, principally `IsSmooth`,
   its constructors, étale-implies-smooth and base-change stability; no exact match.
5. Direct `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
   `/home/ubuntu/weil-newtargets-shared/lean/Sheaf` for smooth/étale combinations,
   `smoothAt`, `smoothLocus`, and the node id: no exact statement. Read the
   general flat-surjective descent theorem in upstream Smooth.lean and the
   smooth-locus API in Mathlib to distinguish their hypotheses and conclusions.
6. Direct `rg` for both proposed declaration names in `dag/lean_names_upstream.json`,
   Mathlib, upstream WeilConjectures and side-project Sheaf: no name collision.
   Searching upstream for the exact node id also gave no hit.

Validation: `scompile.py Q137 lem-trf-etale-source-smoothness
<module path>` compiled the delivered module successfully on the server, with no
errors or warnings. Every theorem is postponed with `sorry`; there are no data
definitions, axioms, unbound universes or auto-bound implicit variables.

No statement dispute or node fault was found.

## Second reading by Q137

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
