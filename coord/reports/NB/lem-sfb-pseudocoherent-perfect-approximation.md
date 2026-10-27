## Worker report

The module `Sheaf.AlgebraicGeometry.PseudoCoherentPerfectApproximation` states
`AlgebraicGeometry.Scheme.exists_perfect_approximation`. Its only theorem has proof
`sorry`; it introduces no definitions. The item node changes only in `lean`.

Source read: `literature/stacks-project/perfect.tex`, `definition-approximation-holds`
(Tag 08EM), `definition-approximation` (Tag 08EN), and `theorem-approximation`
(Tag 08ES). The latter asserts the uniform supported approximation property for a
qcqs scheme. Taking the full closed support gives exactly the item's assertion.

Hypothesis and conclusion correspondence:

- A scheme X is `(X : Scheme.{u})`.
- Quasi-compactness is `[CompactSpace X]`, compactness without a Hausdorff requirement.
- Quasi-separatedness is `[QuasiSeparatedSpace X]`. Mathlib's
  `AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated` identifies this with
  quasi-separatedness of `terminal.from X`, the morphism convention in the DAG.
- E belongs to the full derived category of module sheaves:
  `(E : schemeDerivedCategory X)`. No quasi-coherence assumption on E is added.
- Pseudo-coherence is exactly `(hE : IsPseudoCoherent X E)`, using the recorded
  definition, with bounded-above finite free local models.
- The chosen degree is `(a : ℤ)`, with no sign or size restriction.
- The two `HasDerivedCategory.{w}` binders choose the shared derived categories of
  module sheaves on X and on each localized open site. They are the binders of
  both recorded predicates, not finiteness or geometric assumptions. Universes u
  and w are declared explicitly and independently, and auto-implicit variables
  are disabled.
- The existential P in `D_QCoh(O_X)` is
  `(P : schemeDerivedQCohCategory X)`. Its underlying derived object is `P.obj`;
  its bundled property is exactly quasi-coherence of every cohomology sheaf.
- Its perfectness is `IsPerfect X P.obj`, using the recorded perfect predicate.
- The map in the full derived category is `(u : P.obj ⟶ E)`.
- For every integer i strictly greater than a, the statement requires
  `IsIso ((DerivedCategory.homologyFunctor ... i).map u)` under `a < i`.
  `homologyFunctor` uses `ComplexShape.up ℤ`, so these are the cohomological degrees
  in the node, without a sign reversal.
- Surjectivity at the endpoint is
  `Epi ((DerivedCategory.homologyFunctor ... a).map u)`. This is epimorphism in
  the abelian category of module sheaves, equivalently stalkwise surjectivity.
  It does not impose surjectivity on sections over every open.
- No Noetherian, separated, ample-line-bundle, characteristic, or base-ring
  hypothesis occurs in the signature. There is no extra cone or triangle clause.

Recorded statement dependencies used, with source signatures and docstrings read:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-pc-morphism-conventions` is explicitly a convention node with no declaration.
  Its qc/qs meanings are supplied by `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`; the scheme is given the
  equivalent absolute topological properties above.
- `def-pc-derived-category`: `WeilConjectures.AlgebraicGeometry.DerivedCategory`,
  `AlgebraicGeometry.schemeDerivedCategory`, `schemeDerivedQCohProperty`, and
  `schemeDerivedQCohCategory`.
- `def-pur-pseudo-coherent-complex`:
  `WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex`,
  `AlgebraicGeometry.Scheme.IsPseudoCoherent`.
- `def-pc-perfect-complex`: `WeilConjectures.AlgebraicGeometry.PerfectComplex`,
  `AlgebraicGeometry.Scheme.IsPerfect` (also read `IsStrictlyPerfect`).

The module also imports the stated proof dependencies, using plain imports:
`Sheaf.AlgebraicGeometry.SupportedPerfectApproximation`
(`Scheme.HasSupportedPerfectApproximation`),
`Sheaf.AlgebraicGeometry.AffineSupportedPerfectApproximation`
(`Scheme.exists_supported_perfect_approximation_of_isAffine` and
`Scheme.hasSupportedPerfectApproximation_of_isAffine`),
`Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`
(`AlgebraicGeometry.compactSpace_inter_of_quasiSeparated`),
`WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction`
(`AlgebraicGeometry.quasiCompactOpen_induction`),
`WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh`
(`Scheme.schemeDerivedQCohProperty_of_isPseudoCoherent`), and
`WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh`
(`AlgebraicGeometry.schemeDerivedQCohProperty_of_isPerfect`).
Names beginning `Scheme.` here are in namespace `AlgebraicGeometry`.
The proof dependency `lem-sfb-supported-perfect-approximation-open-step` has no
recorded declaration in the read snapshot, so it has no import yet. It is not
needed to type this statement; the theorem docstring retains its role in step 2.

Edge cases checked before writing: the empty scheme is admitted, with the zero
perfect object supplying the conclusion; for E=0 on any qcqs X, P=0 and the zero
map work in every degree. All positive, zero, and negative choices of a remain
allowed. The endpoint requires only an epimorphism; it does not accidentally
require an isomorphism there or any condition below a. Nonseparated qcqs schemes
and schemes without a chosen base or ample bundle remain allowed. Full support
T=X has empty, hence retrocompact, complement, making the support conditions in
08EN vacuous without any extra hypothesis.

Searches actually made via `batch2/msearch.py`, all logged in `searches.jsonl`:

- LeanSearch, `Pseudo coherent complexes on quasi compact quasi separated schemes
  admit perfect approximations`: 8 hits, chiefly finite presentation and
  quasi-coherence of sheaves, and qc/qs properties of schemes; no perfect
  approximation theorem.
- LeanFinder, `On a quasi compact quasi separated scheme a pseudo coherent complex
  has a perfect approximation inducing cohomology isomorphisms above a chosen
  integer and a surjection at that integer`: 8 hits. These are the bounded
  representative results `DerivedCategory.exists_iso_Q_obj_of_isGE`,
  `exists_iso_Q_obj_of_isGE_of_isLE`, `exists_iso_Q_obj_of_isLE`, fraction
  factorizations, and `CochainComplex.cm5b`; none requires a perfect source.
- Loogle, `"Perfect", "Complex"`: 0 hits.
- Mathlib grep, `perfect.*approximat|approximat.*perfect|PseudoCoherent|pseudo_coherent`:
  0 hits.
- Direct rg with `perfect.*approximat|approximat.*perfect|exists_perfect_approximation`
  over `lean/WeilConjectures` and `lean/Sheaf` found the uniform supported property,
  its affine specialization, and the algebraic-space approximation theorem.
  The space theorem is `AlgebraicGeometry.AlgebraicSpace.exists_perfect_approximation`,
  on its separately encoded small etale module category with extra triangle data;
  its full signature and docstring were read. It is not the scheme statement on
  the recorded `schemeDerivedCategory X`. No existing declaration has the exact
  present statement.
- Direct grep for the item id in `lean/WeilConjectures`, and rg for
  `exists_perfect_approximation` or the item id in `dag/lean_names_upstream.json`,
  found no recorded upstream match. A further rg for `exists_perfect_approximation`
  over Mathlib and `lean/WeilConjectures` found none.

No disputed statement or dependency repair was needed. The accepted split and
all natural-language node fields are preserved. The declaration docstring carries
all four proof steps from the node, including the endpoint and full-support
specialization.

Validation: `scompile.py NB lem-sfb-pseudocoherent-perfect-approximation` compiled
both the sandbox view and the actual module view cleanly on the server (2.5 s and
2.2 s). The file has no diagnostic commands, local notation, local definitions,
unbound variables, or lines exceeding 100 characters.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
