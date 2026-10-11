## Worker report

The module `Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing` states
`AlgebraicGeometry.Scheme.Modules.ext_support_cohomology_vanishing`, with proof `sorry`.
No definition, dependency module, new node, or statement correction is needed.

Hypotheses and clauses of the unchanged node are rendered as follows:

- Scheme: `X : Scheme.{u}`.
- Quasi-compact: `[CompactSpace X]`, without a separation assumption.
- Locally Noetherian: `[IsLocallyNoetherian X]`; together these are Noetherian.
- Regular: `hregular : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ IsRegularRing Γ(X, U)`.
  This is exactly the affine-neighbourhood rendering prescribed by the dependency's
  `mathlib_match` and `lean.note`, rather than a new regular-scheme predicate.
- Finite dimension d: `d : ℕ` and `hdim : X.dim = (d : WithBot ℕ∞)`.
- Both O_X-modules: `F G : X.Modules`; coherence is separately `hF` and `hG`, each
  `RingedSpace.IsCoherent X.toRingedSpace` applied to the corresponding module.
- Every integer q≥0: `q : ℤ` and `hq : 0 ≤ q`.
- The sheaf Ext is the recorded `AlgebraicGeometry.moduleSheafExt X q F G`, i.e.
  cohomology of derived internal Hom of F[0],G[0]. The explicit
  `[HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]`
  is its existing size infrastructure, not an additional geometric condition.
- Support: the subtype `{x : X // ¬ Subsingleton ((Scheme.Modules.presheaf
  (AlgebraicGeometry.moduleSheafExt X q F G)).stalk x)}` has the subspace topology.
  Its stalk is the underlying abelian group of the module stalk, so subsingleton means zero.
- For q≤d, the first conjunct bounds `topologicalKrullDim` of that subtype by
  `(((d : ℤ) - q).toNat : WithBot ℕ∞)`. Under this condition toNat is exactly d−q.
- For q>d, the second conjunct makes every stalk subsingleton, exactly saying the
  displayed support is empty. This is the negative-bound case, without truncated
  subtraction accidentally permitting a nonempty zero-dimensional support.
- Every integer p>d−q: the third conjunct quantifies `p : ℤ` and uses
  `(d : ℤ) - q < p`. `IsZero` is applied to the module-cohomology object:
  if p≥0, `(RingedSpace.moduleCohomology X.toRingedSpace p.toNat).obj
  (AlgebraicGeometry.moduleSheafExt X q F G)`; otherwise the zero object.
  This is the conventional zero extension of the recorded nonnegative right-derived
  functors to negative degrees. No alternative cohomology definition is introduced.

Dependency declarations read and used:

- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularRing` and `IsRegularLocalRing`;
  regularity follows the dependency record's exact affine form.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.Dimension`: `AlgebraicGeometry.Scheme.dim`, supremum of
  local-ring Krull dimensions (rather than replacing it by topological dimension).
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`.
- `Sheaf.AlgebraicGeometry.SheafExt`: `AlgebraicGeometry.moduleSheafExt` (read all four
  declarations including its embedding of both modules in degree zero).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.Paper.PQFCohomology`: `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`
  records the cohomology notion, which uses `AlgebraicGeometry.RingedSpace.moduleCohomology`
  from `Sheaf.Topology.RingedSpaceModuleCohomology`; both full signatures and docstrings read.
- Mathlib's `AlgebraicGeometry.Scheme.Modules.presheaf` supplies the underlying abelian
  presheaf. Fully qualifying it is necessary because moduleSheafExt returns SheafOfModules.

Edge cases: q=0 gives the bound d and vanishing above d; q=d gives dimension at most
zero and positive-degree vanishing; q>d gives empty support and vanishing including p=0.
Negative p in the inequality is also covered by the zero branch. F=0 or G=0 yields
empty support and zero cohomology. For the empty scheme, dim is bottom, so the hypothesis
that dim=d for a natural d cannot hold, consistently with the node's finite dimension d.
There is no field, characteristic, irreducibility, equidimensionality, separatedness or
nonempty hypothesis added. Universes u and w are explicit; module universe is tied to X.

Sources checked at https://stacks.math.columbia.edu/tag/0FZ3 and
https://stacks.math.columbia.edu/tag/02UZ because literature/stacks-project is absent on
this machine. Tag 0FZ3's proof gives exactly the support bound and cohomology inequality.
No STATEMENT-DISPUTED flag or node fault.

Searches for an existing statement (2026-10-11 UTC):

- msearch LeanSearch, `sheaf Ext support dimension regular scheme cohomology vanishing`:
  unavailable, Internal Server Error; no verdict drawn from this unavailable service.
- msearch LeanFinder, `support dimension of sheaf Ext on regular Noetherian scheme
  cohomology vanishing`: eight hits, general injective/projective dimension Ext vanishing
  only; no sheaf Ext support/cohomology statement.
- msearch Loogle, `topologicalKrullDim, Ext`: zero hits.
- msearch grep of Mathlib, `sheafExt|support.*dimension|cohomology.*support`: 24 hits,
  unrelated analysis, local cohomology, and module Krull-dimension infrastructure; no match.
- rg of the same expression in upstream WeilConjectures/AlgebraicGeometry: unrelated
  coherent-support and curve material; no sheaf Ext definition or matching theorem.
- rg of the item id in upstream WeilConjectures: no hit.
- rg of `ext_support_cohomology_vanishing` in the upstream names index: no hit;
  `tools/lean_names_upstream.py show` provides no declaration for this item.
- rg of `moduleSheafExt|support.*dimension|cohomology.*support` in lean/Sheaf's
  AlgebraicGeometry and Topology directories: existing sheaf Ext definition and references
  to this unimplemented lemma in CoherentExtVanishing, plus unrelated support results;
  no exact declaration. The proposed full declaration name is absent from these sources.

Validation: scompile.py compiled the final module cleanly on the server. Stage 2 leaves
only the named theorem's `sorry`. The independent second reader will supply their section.

## Second reading by C1

I read the node statement, the source places (Stacks Tags 0FZ3 and 02UZ), all recorded
dependency signatures, and the module together. The object and hypothesis checklist is:

- `X` is `Scheme.{u}`, rendered by the theorem's first binder; verdict: exact.
- Quasi-compact and locally Noetherian are `[CompactSpace X]` and
  `[IsLocallyNoetherian X]`; verdict: exact Mathlib/dependency encodings, with no
  separation hypothesis.
- Regularity is the affine-neighbourhood predicate `hregular` with
  `IsRegularRing Γ(X,U)`; verdict: exact recorded rendering of `def-weil-regular-scheme`.
- Finite dimension is `d : ℕ` and `hdim : X.dim = (d : WithBot ℕ∞)`; verdict: exact.
- Coherent modules are `F G : X.Modules` with `hF` and `hG` using
  `RingedSpace.IsCoherent`; verdict: exact.
- For `q : ℤ`, `hq : 0 ≤ q`, the Ext object is the recorded
  `AlgebraicGeometry.moduleSheafExt X q F G`; verdict: exact, and the explicit
  `HasDerivedCategory` binder is required size infrastructure of that definition.
- The support is the subtype of points whose module stalk is not subsingleton, with
  its inherited topology; verdict: exact support-as-subspace and zero-stalk criterion.
- For `q ≤ d`, the first conjunct bounds its `topologicalKrullDim` by the natural
  subtraction represented as `(((d : ℤ)-q).toNat : WithBot ℕ∞)`; verdict: exact under
  the stated inequality.
- For `d < q`, the second conjunct says every stalk is subsingleton; verdict: exact
  empty-support clause, including the strict negative-bound case.
- For every integer `p` with `d-q < p`, the third conjunct gives `IsZero` of the
  recorded module cohomology for nonnegative `p`, and the zero object for negative `p`;
  verdict: exact integer-degree convention and quantifier order.

No mismatch was found and no code or node statement was changed. Edge cases checked:
`q=0`, `q=d`, `q>d` (including `p=0`), negative `p`, zero `F` or `G`, empty support,
and the empty scheme. The latter cannot satisfy `X.dim = d` for a natural `d`, as in
the node's finite-dimension hypothesis. Universes are explicit and no characteristic,
irreducibility, equidimensionality, separatedness, or nonempty assumption was added.

Searches were independently checked with LeanSearch (service unavailable), LeanFinder,
Loogle, grep of Mathlib, grep of upstream `WeilConjectures`, grep of `lean/Sheaf`, and
the upstream names index. They found no existing matching theorem or alternate notion;
the only relevant declarations are the recorded `moduleSheafExt`, `Scheme.dim`,
`moduleCohomology`, `topologicalKrullDim`, `CompactSpace`, `IsLocallyNoetherian`,
`IsRegularRing`, and `RingedSpace.IsCoherent`. The module compiles cleanly with only
the named theorem proof left as `sorry`.
