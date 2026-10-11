## Worker report

`Sheaf.AlgebraicGeometry.PerfectJumpLoci` states
`AlgebraicGeometry.Scheme.pseudoCoherent_jump_loci`, with its proof `sorry`.
`Sheaf.AlgebraicGeometry.DerivedFiberBetti` defines the cohomology vector space and
its finite rank in full, with no postponed data or proof. The source was read at
https://stacks.math.columbia.edu/tag/0BDI (Lemma 36.31.1); this machine does not have
`literature/stacks-project/perfect.tex`.

Hypothesis and clause correspondence:

- Scheme X: `(X : Scheme.{uX})`, the Mathlib scheme of def-pc-scheme.
- E in D(O_X): `(E : schemeDerivedCategory X)`, the recorded specialization of
  Mathlib's derived category on the shared `SheafOfModules (moduleRings ...)` carrier.
- Pseudo-coherent E: `(hE : IsPseudoCoherent X E)` uses the recorded scheme-local
  bounded-above finite-free definition, without assuming perfectness. The node's
  perfect-complex parenthesis is an example, not an additional hypothesis; its
  declaration `Scheme.IsPerfect` was read but is consequently not imported.
- Every integer i: `(i : ℤ)`. No degree restriction is imposed.
- β_i(x): `derivedFiberBetti X E i x` is `Module.finrank (X.residueField x)` of
  `derivedFiberCohomology X E i x`. The latter is obtained by `derivedPullback
  (X.fromSpecResidueField x)`, then `DerivedCategory.homologyFunctor ... i`, then
  `SheafOfModules.evaluation ... (op ⊤)`, then scalar restriction along the inverse
  of `ΓSpecIso`. Spec of a field is a one-point space: sections of the cohomology
  sheaf on the whole space are exactly its cohomology vector space. This uses
  cohomology of a complex, not an alternative definition of sheaf cohomology.
  Pseudo-coherence makes every such space finite dimensional; Mathlib finrank
  therefore equals the dimension in the node and in Tag 0BDI.
- Arbitrary base change: the first conjunct quantifies over every scheme Y,
  morphism `g : Y ⟶ X`, and point y, and equates the Betti number of
  `((derivedPullback g).obj E)` at y with that of E at g y. No geometric property
  of g or Y, and no separately assumed pseudo-coherence of its pullback, is required.
- Upper semicontinuity: `UpperSemicontinuous (derivedFiberBetti X E i)`.
- Every level set locally constructible: `∀ r : ℕ, Topology.IsLocallyConstructible
  {x : X | derivedFiberBetti X E i x = r}`. β takes natural-number values as in
  the source, so this quantifies over all its levels.
- The `HasDerivedCategory` binders supply the chosen localizations required by
  the shared definitions, including restrictions on opens for IsPseudoCoherent
  and residue-field spectra for derived fibres. They impose no mathematical
  restrictions on schemes or complexes. All variables and universes are explicit.

Recorded dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`.
- `Sheaf.AlgebraicGeometry.PseudoCoherentComplex`: `AlgebraicGeometry.Scheme.IsPseudoCoherent`.
- Through the new definition, `Sheaf.AlgebraicGeometry.DerivedPullback`:
  `AlgebraicGeometry.derivedPullback` (its universal-property specification and
  its full signature were read).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.fromSpecResidueField` and
  `Scheme.residueField`; `Scheme.ΓSpecIso` from Mathlib's Scheme module;
  `SheafOfModules.evaluation`, `DerivedCategory.homologyFunctor`,
  `ModuleCat.restrictScalars`, and `Module.finrank` from Mathlib.
- Also read: `Sheaf.AlgebraicGeometry.PerfectComplex`, `Scheme.IsPerfect` and its
  strict-perfect local definition; these are not extra hypotheses of this lemma.

Edge cases checked: empty X gives vacuous point conditions and empty level sets;
zero complex has β identically zero, with full zero level and empty other levels;
negative i and unbounded-below pseudo-coherent E are included, since the local
truncation only needs degrees i-1,i,i+1; r=0 uses the zero level, not positive
levels only. Non-Noetherian schemes are included: the proof needs finite-minor
quasi-compact opens, not an inference of constructibility from openness alone.
Arbitrary base change includes the empty scheme, identity, field extension,
non-flat maps and non-finite-type maps. No characteristic is imposed. The object
universe is shared by schemes and their residue fields and the localization
universe is shared by all the derived categories, as in the recorded pullback.

Searches performed with msearch.py (recorded in searches.jsonl):

- LeanFinder, `pseudo-coherent complex derived fibre cohomology dimension upper
  semicontinuous locally constructible`: eight generic derived-category support
  results, no jump-locus statement.
- Loogle, `UpperSemicontinuous, IsLocallyConstructible`: zero hits; the second
  identifier needs its Topology namespace in the pinned Mathlib.
- Mathlib grep, `jump.?loci|IsLocallyConstructible|betti`: ten hits, generic
  constructibility and Chevalley results, no jump-locus theorem.
- LeanSearch, `dimension cohomology derived fibre of a scheme complex`:
  unavailable (Internal Server Error), recorded as unavailable.
- LeanFinder, the same dimension query: eight results, sheaf Ext cohomology,
  cotangent spaces and smooth differentials; none define derived scheme fibres.
- Mathlib grep, `derivedFiber|derivedFibre|fiberBetti|fibreBetti`: no hits.
- rg on project Sheaf and upstream WeilConjectures for jump loci and fibre
  cohomology: finite-free complexes and proper direct-image semicontinuity are
  different statements, no match to this lemma.
- rg on DAG, project Sheaf and upstream for the four proposed derived-fibre names:
  no hits. blueprint_refs.py search `derived fibre`: zero blueprint nodes.
- grep for `lem-sc-perfect-jump-loci` in upstream WeilConjectures: no hits.

No statement correction and no disputed mathematical clause.

## Second reading by H1

Statement checklist against Stacks Tag 0BDI (Lemma 36.31.1):

- `X` is rendered as `(X : Scheme.{uX})`; this is the scheme object of
  `def-pc-scheme`, with no extra finiteness, separatedness, Noetherian, or
  characteristic hypothesis. Verdict: matches.
- `E ∈ D(O_X)` is rendered as `(E : schemeDerivedCategory X)` and
  `hE : IsPseudoCoherent X E`; the parenthetical perfect-complex example in
  the node is not incorrectly made a hypothesis. Verdict: matches.
- The integer degree is `(i : ℤ)`, with no sign or boundedness restriction.
  Verdict: matches.
- `β_i(x)` is rendered by `derivedFiberBetti X E i x`, whose definition is
  `Module.finrank` of the degree-`i` cohomology of the derived residue-field
  pullback. Verdict: matches the source dimension, including Mathlib's zero
  convention outside finite dimension.
- Arbitrary base change is rendered by quantifying over every
  `Y : Scheme.{uX}`, every required derived-category instance, every
  `g : Y ⟶ X`, and `y : Y`, with equality of the pulled-back and original
  Betti numbers. Verdict: matches; no geometric condition on `g` is added.
- Upper semicontinuity is `UpperSemicontinuous (derivedFiberBetti X E i)`.
  Verdict: matches.
- Every level set is rendered as
  `∀ r : ℕ, Topology.IsLocallyConstructible {x | derivedFiberBetti X E i x = r}`.
  Verdict: matches all natural levels, including zero.
- The `HasDerivedCategory` binders provide localization choices only; they do
  not impose mathematical restrictions. The scheme and test-scheme universes
  are shared (`uX`), so no vacuous independent index universe is introduced.

Edge cases checked: empty schemes and empty fibres make the point clauses
vacuous; the zero complex has only the zero level; `i` may be negative; `r = 0`
is included; arbitrary base change includes the identity, empty schemes,
field extensions, non-flat maps, and non-finite-type maps; no characteristic is
assumed.

Searches were rechecked in Mathlib, upstream `WeilConjectures`, and the DAG for
jump-locus, derived-fibre, Betti, upper-semicontinuity, and locally
constructible declarations. No existing declaration states this notion or
lemma. The added `def-sc-derived-fiber-betti` node and module are therefore
required and are cited by the item node.

Mismatch review: the worker's item statement and Lean theorem agree clause by
clause. The only dependency bookkeeping issue was that the new Betti
definition had to be included in `stmt_deps`; the sandbox node already contains
that correction. No Lean source change was needed. Both modules compile
together with only the theorem proof `sorry`.

## New nodes

`def-sc-derived-fiber-betti` supplies the cohomology vector space of `Li_x^* E`
and its finite rank, using the existing derived pullback. Source: Tag 0BDI,
definition of β_i. It is not a new derived pullback or a new sheaf-cohomology
construction. The dimension searches above found no existing declaration;
related finite-free models only compute fibres for explicitly given complexes.
The node cites the existing scheme, derived category, and derived pullback
nodes. The item's only additional statement dependency is this definition node.
For general E the finite rank has Mathlib's zero-for-infinite-rank convention;
for pseudo-coherent E it is the actual finite cohomology dimension of the source.
