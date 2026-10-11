## Worker report

The module `Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfDegreeOfEtaleCover` states
`AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFreeOfDegree_of_etale_cover`, with its sole proof
`by sorry`. It introduces no definitions and does not change the informal statement.

The source files in `literature/stacks-project/` are absent on this machine. Read the source
at [Stacks 02VO](https://stacks.math.columbia.edu/tag/02VO) and
[Stacks 022C](https://stacks.math.columbia.edu/tag/022C). The former asserts fpqc locality of
finite local freeness of degree d, and its last proof paragraph checks the degree on fibres;
the latter makes an étale covering an fpqc covering. These give exactly the node's specialization.
The declaration docstring records all five proof steps and their DAG dependencies.

Clause-by-clause correspondence:

- Schemes Y and T and a morphism h: `{Y T : Scheme.{u}} (h : Y ⟶ T)`.
- Integer d ≥ 0: `(d : ℕ)`, the nonnegative integers, including zero.
- An arbitrary family indexed by I: `{I : Type w} (T' : I → Scheme.{u})`
  and `(φ : ∀ i : I, T' i ⟶ T)`. The universe w is independent of u.
- Each morphism is étale: `hφ : ∀ i : I, Etale (φ i)`.
- Their images cover T: `hcover : ∀ t : T, ∃ (i : I) (t' : T' i), φ i t' = t`.
  This says exactly that every point belongs to the union of the images, with no individual
  surjectivity or finiteness assumption on the family.
- For every i the base change to T_i is finite locally free of degree d:
  `hdegree : ∀ i : I, (pullback.snd h (φ i)).IsFiniteLocallyFreeOfDegree d`.
  The second projection has domain `pullback h (φ i)` and target `T' i`.
- Conclusion: `h.IsFiniteLocallyFreeOfDegree d`, the same predicate on the original morphism.
  This includes finite, flat, locally of finite presentation, and the degree equality at
  every target point, with nothing extra.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`. Read their structure definitions and docstrings:
  schemes are locally ringed spaces locally isomorphic to affine spectra; morphisms are
  morphisms of the underlying locally ringed spaces.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`. Read its affine-local ring-map definition
  and `Etale.iff_flat_and_formallyUnramified`, which gives the node's equivalent
  flat/unramified/locally-of-finite-presentation characterization.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; read their full signatures,
  the projection docstrings, and `pullback.lift` expressing the universal property.
- `def-pc-finite-locally-free`: `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`
  and `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree`,
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`, lines 776–792.
  Read both full signatures/docstrings and the underlying `fiberDegree` definition at
  lines 324–327: it is `Module.finrank (X.residueField x) Γ(g.fiber x, ⊤)`.
  The degree class extends the finite/flat/lfp class, so the finite-dimensional fibre
  interpretation agrees with the node. These exact recorded declarations are reused.

Edge cases checked before writing: d = 0 is allowed; the empty target is allowed and all
pointwise assertions become vacuous; an empty index type forces the target to be empty via
hcover; empty members of a nonempty family are allowed. No field, characteristic, reducedness,
Noetherian, separation, target quasi-compactness, or individual quasi-compactness is imposed.
For an identity covering the statement reduces to its hypothesis. The pointwise coverage
condition is equivalent to the node's union-of-images equality. No node fault or disputed
statement was found. No new nodes or dependency replacement modules are needed.

Searches made (2026-10-11; via msearch.py J1 with this item):

- LeanSearch: `finite locally free of fixed degree descends along etale covering of schemes`.
  Service unavailable, Internal Server Error; not interpreted as a negative search result.
- LeanFinder: `finite locally free morphism of constant degree descends along an etale covering`.
  Eight hits on étale definitions, composition, and base change, and standard smooth ring
  maps; none is the required finite-local-freeness descent statement.
- Loogle: `AlgebraicGeometry.Etale, AlgebraicGeometry.Scheme.Hom.finrank`: zero hits.
- Mathlib grep: `IsFiniteLocallyFreeOfDegree|finiteLocallyFree.*desc|finrank.*desc`
  in `AlgebraicGeometry`: zero hits.
- Source rg: `IsFiniteLocallyFreeOfDegree|isFiniteLocallyFree.*[Ee]tale|finite_locally_free.*etale`
  in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: the existing degree class in
  FiberDegree.lean and its use in Modules/FinitePushforward.lean, no covering descent theorem.
- Source grep for the exact item id: no hits. Also read the related source descent results
  in `WeilConjectures/AlgebraicGeometry/Descent.lean`; they address modules/descent data or
  closed subschemes, rather than this statement about an arbitrary scheme morphism.
- Project rg for finite-local-freeness and the degree class in `lean/Sheaf`: existing modules
  about locally free modules and a tangent criterion, no matching theorem.
- Exact proposed declaration name searched in `dag/lean_names_upstream.json`, Mathlib and
  `lean/Sheaf`: no collision. Local MCP index unavailable in this session; source searches used.

Validation: scompile.py compiled the module on the server in 1.7 seconds, exit code 0,
with no errors or warnings. All universes and variables are explicitly bound. The node copy
changes only its lean record, whose statement is verbatim from the declaration signature.

## Second reading by J1

I independently opened the base node, sandbox node and module, all four statement-dependency
nodes, and the declarations below. I read the Stacks TeX at the labels
`lemma-descending-property-finite-locally-free` in `descent.tex` (02VO) and
`lemma-zariski-etale-smooth-syntomic-fppf-fpqc` in `topologies.tex` (022C), fetched from
https://raw.githubusercontent.com/stacks/stacks-project/master/ because this machine has no
literature checkout. I also read https://stacks.math.columbia.edu/tag/02VO and
https://stacks.math.columbia.edu/tag/022C. These source places impose no standing Noetherian,
separation, characteristic, or quasi-compactness hypothesis on the schemes. 02VO gives descent
along an fpqc covering; 022C applies to the jointly surjective étale family of the node.

The complete object/hypothesis/conclusion checklist, in node order:

- Schemes Y and T and a morphism h:Y→T: `{Y T : Scheme.{u}} (h : Y ⟶ T)`.
  Verdict: exact. Mathlib `Scheme` is a locally ringed space with locally affine neighbourhoods;
  `Scheme.Hom` is a morphism of the underlying locally ringed spaces. I read their definitions
  in `Mathlib.AlgebraicGeometry.Scheme` (lines 36–79). These are the Mathlib leaves of
  `def-pc-scheme`, not a specialization to affine or field-based schemes.
- A nonnegative integer d: `(d : ℕ)`. Verdict: exact, including zero.
- An arbitrary family indexed by I: `{I : Type w} (T' : I → Scheme.{u})`
  and `(φ : ∀ i : I, T' i ⟶ T)`. Verdict: exact. No finite-family assumption;
  the independent index universe w is explicitly bound.
- Every φ_i is étale: `(hφ : ∀ i : I, Etale (φ i))`. Verdict: exact.
  I read `Etale` in `Mathlib.AlgebraicGeometry.Morphisms.Etale` (lines 38–45)
  and `Etale.iff_flat_and_formallyUnramified` (lines 140–143), including its lfp clause.
  This is the affine-local ring-map definition recorded for `def-weil-etale-morphism`;
  no individually surjective or quasi-compact cover map is required.
- The images cover T: `(hcover : ∀ t : T, ∃ (i : I) (t' : T' i), φ i t' = t)`.
  Verdict: exact membership in the union of the images, with the same quantifier order.
- For each i, the base change Y×_T T_i→T_i is finite locally free of degree d:
  `(hdegree : ∀ i : I, (pullback.snd h (φ i)).IsFiniteLocallyFreeOfDegree d)`.
  Verdict: exact. I read the full `pullback`, `pullback.snd`, `pullback.lift` and
  `pullback.isLimit` signatures in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: the second projection
  targets T_i, and the limit gives precisely the universal fibre product of
  `def-pc-fibre-product`. Scheme pullbacks are provided by the imported library,
  with no additional assumption on h.
- Conclusion h is finite locally free of degree d: `h.IsFiniteLocallyFreeOfDegree d`.
  Verdict: exact. I read the recorded `Scheme.Hom.IsFiniteLocallyFree` and
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` (lines 776–792), and
  `fiberDegree` with its residue-field algebra (lines 312–327). The former extends
  `IsFinite`, `Flat`, and `LocallyOfFinitePresentation`; the degree class additionally
  requires `fiberDegree_eq (s : S) : f.fiberDegree s = d`. Thus both clauses of
  `def-pc-finite-locally-free` are present. Its inherited finiteness supplies affineness
  and finite dimensionality for the fibre-section dimension; this is not a hidden
  hypothesis on the statement.

Edge cases: d=0 remains permitted. Empty Y and empty cover members remain permitted.
If I is empty, hcover forces T empty; if T is empty, every pointwise condition is vacuous,
exactly as in the source. No nonempty index or scheme instance is assumed. Schemes have
arbitrary universe u, independent of w; all variables and both universes are bound.
There is no base field or characteristic restriction. The hypothesis gives the same d
on all members, and the conclusion gives that d at every point, not merely locally constant
rank or a bound.

Independent searches on 2026-10-11, with words differing from the worker's:

- `msearch.py J1 ... leanfinder "jointly surjective etale family descent finite flat
  morphism constant fiber dimension"`: eight hits, on ring-level standard étale maps,
  étale composition, and smooth presentations; no exact descent statement.
- `msearch.py J1 ... loogle "AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree"`:
  index reports an unknown identifier, hence unavailable for this upstream declaration,
  not evidence of absence. The worker's LeanSearch failure is likewise not a negative result.
- `rg` for `IsFiniteLocallyFreeOfDegree|finite.*free.*[Dd]esc|[Dd]esc.*finite.*free`
  across Mathlib AlgebraicGeometry, all upstream WeilConjectures, and project lean/Sheaf:
  the upstream degree class, finite pushforward, module descent and closed-subscheme
  descent appear; no theorem with this statement. I opened the full signature and docstring
  of `isSheaf_fpqc_finiteLocallyFreeSubscheme` in upstream `Descent.lean` (lines 461–497):
  it descends compatible closed subschemes and is not this arbitrary-morphism theorem.
  The module descent statements concern module sheaves, not morphisms of schemes.
- Exact proposed full-name search across `dag/lean_names_upstream.json`, Mathlib,
  upstream WeilConjectures and project lean/Sheaf: no collision.

No mathematical mismatch was found, and no Lean or node repair was needed. There are no new
nodes or dependency modules, no statement correction, no private or hollow definition,
and no proof beyond the sole `by sorry`. Both docstrings identify the source and blueprint;
the theorem docstring follows all five node proof steps and names their dependencies.
The node's lean.statement is verbatim the theorem signature before `:= by`.
I appended this independent reading only, leaving the correct statement untouched.

Validation: independent `scompile.py J1 lem-weil-pbc-finite-locally-free-degree-etale-descent
lean/Sheaf/AlgebraicGeometry/IsFiniteLocallyFreeOfDegreeOfEtaleCover.lean` compiled in 1.7 s,
exit code 0, with no errors or warnings.
