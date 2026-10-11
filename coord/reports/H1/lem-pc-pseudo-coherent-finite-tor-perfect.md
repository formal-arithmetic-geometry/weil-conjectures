## Worker report

The main module states `AlgebraicGeometry.Scheme.isPerfect_of_isPseudoCoherent_of_isFiniteTorDimension`
with proof `sorry`, exactly the scheme criterion in the item. A second module defines the missing
scheme-level finite Tor dimension predicate, with full data and no sorry.

Hypothesis/clause correspondence:
- “S a scheme”: `(S : Scheme.{uP})`, Mathlib `AlgebraicGeometry.Scheme`.
- “K in D(O_S)”: `(K : schemeDerivedCategory S)`, with the shared
  `HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings S.toRingedSpace))` binder.
- “K pseudo-coherent”: `(hK : IsPseudoCoherent S K)` uses exactly the recorded predicate.
  The per-open HasDerivedCategory binder is the one required by that predicate and IsPerfect,
  representing the derived categories of the restricted module sheaves, with no geometric condition.
- “finite Tor dimension”: `(hTor : IsFiniteTorDimension S K)`. Its definition is
  `∃ a b : ℤ, a ≤ b ∧ ∀ F, ∀ i, i < a ∨ b < i → ...`, using the recorded
  `schemeDerivedTensorCohomologyVanishes S K F i`. The interval precedes the test module,
  so the bounds are uniform. F ranges over all O_S-module sheaves, without quasi-coherence.
- “K is perfect”: `IsPerfect S K`, exactly the dependency predicate, which asks for local
  isomorphisms to strictly perfect complexes and permits different bounds at different points.

Declarations read and reused:
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom (full signatures/docstrings).
- Sheaf.AlgebraicGeometry.DerivedCategory: AlgebraicGeometry.schemeDerivedCategory.
- Sheaf.AlgebraicGeometry.PseudoCoherentComplex: AlgebraicGeometry.Scheme.IsPseudoCoherent.
- Sheaf.AlgebraicGeometry.PerfectComplex: Scheme.IsStrictlyPerfect and Scheme.IsPerfect.
- Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes:
  AlgebraicGeometry.schemeDerivedTensorCohomologyVanishes (full definition/docstring read).

The node and all four statement dependencies were read, including their Lean records and source
modules. Source checked online because this machine lacks literature/stacks-project/cohomology.tex:
[08CQ](https://stacks.math.columbia.edu/tag/08CQ) and
[08CG](https://stacks.math.columbia.edu/tag/08CG). 08CQ gives the locally finite Tor version;
the item's global finite Tor hypothesis is its valid specialization, as its proof and citers require.
No statement correction is needed. The three DAG proof steps are recorded in the theorem docstring.

Edge cases checked: the empty scheme has vacuous local pseudo-coherence/perfectness and is included;
the zero complex admits bounds [0,0]; a finite free sheaf in one shifted degree has a singleton
Tor interval; arbitrary shifts and negative degrees are allowed by integer bounds. There is no
Noetherian, quasi-compactness, characteristic, or quasi-coherence assumption. Universes of S and its
module sheaves are shared, and the derived localization universe is explicit. No independent smaller
universe of test modules makes the hypothesis vacuous. Global and local finite Tor dimension are
kept distinct. A disjoint union of complexes in unboundedly many degrees need not satisfy the global
hypothesis even if it is perfect locally; this agrees with the node, which only asserts one implication.

Searches for the theorem (msearch.py H1/item): LeanFinder query “pseudo-coherent complex on a scheme
of finite Tor dimension is perfect” returned eight generic T-structure/K-projective hits, no match;
Loogle “IsPseudoCoherent, IsPerfect, finiteTorAmplitude” returned zero hits (unknown IsPseudoCoherent);
Mathlib grep “PseudoCoherent|finiteTorAmplitude|IsPerfect” in AlgebraicGeometry returned zero hits.
rg of WeilConjectures for the item ID returned no declaration. rg of WeilConjectures and lean/Sheaf
for Tor, finite Tor, IsPerfect found the recorded predicates, coefficient-site results and generic
ring/module results, no scheme theorem. The generic source DerivedCategory.finiteTorAmplitude and
its full signature/docstring were read: it requires a derived monoidal structure; server #synth checks
showed no such automatic monoidal structure for the moduleRings carrier. The landed vanishing
predicate avoids adding arbitrary structure hypotheses. All scratch #checks were removed.

Validation: both modules compile together cleanly on the server; every variable/universe is explicit.
No definitions contain sorry. The only theorem is deliberately unproved for stage 2.

## New nodes

`def-pc-finite-tor-dimension` defines global finite Tor dimension, exactly Stacks Definition 08CG(1,2),
using the existing scheme derived tensor vanishing node rather than duplicating derived tensor.
Its Lean definition is the uniform interval predicate described above. The item gains only this
new definition ID in stmt_deps. Mathlib searches: LeanSearch query “finite Tor dimension of a complex
of sheaves of modules on a scheme” unavailable (Internal Server Error); LeanFinder same query gave
injective/projective dimension and SheafOfModules.IsFiniteType hits, no match; grep
“finiteTor|FiniteTor|torAmplitude|TorDimension” gave zero Mathlib hits. Source and project grep,
DAG definition search and blueprint_refs.py search “finite Tor” found only coefficient-site notions
or theorems using the scheme notion. No existing DAG definition gives scheme finite Tor dimension.
The new node records these searches, the ancestor lem-sc-finite-duality and the item's via chain.

## Second reading by H1

I read the item node in `dag/nodes/sec-picard-framework/lem-pc-pseudo-coherent-finite-tor-perfect.json`, the two delivery modules, and the declarations of every statement dependency.

The node introduces a scheme `S` [def-pc-scheme], a derived object `K` in `D(O_S)` [def-pc-derived-category], and the hypotheses that `K` is pseudo-coherent [def-pur-pseudo-coherent-complex] and has finite Tor dimension [def-pc-finite-tor-dimension]. The Lean renders these as `(S : Scheme.{uP})`, the global and open `HasDerivedCategory` instances, `(K : schemeDerivedCategory S)`, `(hK : IsPseudoCoherent S K)`, and `(hTor : IsFiniteTorDimension S K)`. The open derived-category instance is required by the recorded definitions and introduces no geometric or finiteness assumption. `IsFiniteTorDimension` quantifies integers `a ≤ b`, every sheaf of `O_S`-modules, and every integer outside the interval, requiring `schemeDerivedTensorCohomologyVanishes`; its bounds are uniform and its test sheaves are unrestricted. The conclusion `K` is perfect is exactly `IsPerfect S K`.

The theorem declaration is therefore an item-by-item match:
`isPerfect_of_isPseudoCoherent_of_isFiniteTorDimension (S : Scheme.{uP}) [HasDerivedCategory ...] [∀ U : S.Opens, HasDerivedCategory ...] (K : schemeDerivedCategory S) (hK : IsPseudoCoherent S K) (hTor : IsFiniteTorDimension S K) : IsPerfect S K`.
No hypothesis or conclusion was added, dropped, strengthened, or weakened. The theorem proof remains the required `sorry`; the finite-Tor definition has no hollow data or proof.

Edge cases checked: empty schemes are covered by the pointwise local predicates; the zero object satisfies the vanishing condition with interval `[0,0]`; integer bounds permit negative degrees and arbitrary shifts; `n = 0`, characteristic, quasi-compactness, Noetherianity, separatedness, and quasi-coherence are not introduced; universe parameters are shared with the scheme and module sheaves, so no test-object universe is accidentally too small. A globally unbounded direct sum is not asserted to satisfy finite Tor dimension, consistent with the one-way implication.

I searched for an existing statement or notion with `msearch.py` LeanFinder (`pseudo-coherent complex finite Tor dimension perfect`: only generic projective/injective-dimension and K-projective hits), Loogle (`IsPseudoCoherent IsPerfect`: zero hits, unknown identifier), and grep (`PseudoCoherent|finiteTorAmplitude|IsPerfect`: zero hits in AlgebraicGeometry). Repository and DAG searches found no duplicate scheme-level theorem or finite-Tor definition. The source is Stacks Project Cohomology of Sheaves, Lemma 20.49.5 (Tag 08CQ), whose local finite-Tor criterion agrees with the node's global specialization.

No mismatch was found, so no source, statement, dependency, or module change was needed. Both delivery modules compile together cleanly with `scompile.py`; all variables and universes are explicit and line widths satisfy the project convention.
