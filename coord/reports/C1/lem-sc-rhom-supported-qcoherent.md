## Worker report

The module `Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent` states
`AlgebraicGeometry.rhom_supported_quasiCoherent`, with one `sorry` and no new definitions.
The node is unchanged except for `lean`. No statement correction or disputed statement.

Source read: https://stacks.math.columbia.edu/tag/0A6H, clauses (1) and (2),
and https://stacks.math.columbia.edu/tag/0A9C, the first paragraph of the proof.
The local literature checkout has no `stacks-project/perfect.tex`, so the published tags
were read directly. They agree with the node. In particular 0A6H states *locally* bounded
below; its historical comments also explain why a global bound would be false.

Hypothesis and clause correspondence:
- `X : Scheme.{u}` is an arbitrary scheme; `K L : schemeDerivedCategory X` are objects
  of the derived category of all structure-sheaf modules, not only quasi-coherent ones.
- The shared `HasDerivedCategory.{w}` instances, globally and on every localized open
  site, make these categories available and are the same binders used by the recorded
  perfect and pseudo-coherent definitions. They impose no finiteness hypothesis on X.
- `hL : schemeDerivedQCohProperty X L` expresses the common quasi-coherence assumption
  in both cases; it is a property of all cohomology sheaves, not of a representative.
- The first implication assumes `Scheme.IsPseudoCoherent X K` and
  `∃ a : ℤ, L.IsGE a`. The latter says L belongs to D⁺, using Mathlib's canonical
  cohomological t-structure (`DerivedCategory.isGE_iff`). Its conclusion is the
  conjunction of `schemeDerivedQCohProperty X` for RHom and
  `∀ x, ∃ U, x ∈ U ∧ ∃ a, ∀ n, n < a → IsZero (...)`.
  Here `...` is the restriction by `SheafOfModules.overFunctor` of Hⁿ(RHom).
  Thus the bound varies with the neighbourhood and no uniform bound is asserted.
- The second implication assumes `Scheme.IsPerfect X K` and concludes
  `schemeDerivedQCohProperty X` of RHom, with no boundedness assumption on L.
- The final clause quantifies over `T : Set X` with `hT : IsClosed T`, assumes either
  the pseudo-coherent/bounded-below case or the perfect case, and assumes every Hⁿ(L)
  restricts to zero on `⟨Tᶜ, hT.isOpen_compl⟩`. It concludes the identical vanishing
  assertion for Hⁿ(RHom). These are precisely the node's definition of support.
- In every clause RHom is the recorded `CategoryTheory.derivedInternalHom` applied to
  `(op K, L)` on the structure sheaf of X. There is no alternative Hom construction.

Dependency declarations read:
- `Sheaf.AlgebraicGeometry.PseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsPseudoCoherent`, used directly.
- `Sheaf.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, `schemeDerivedQCohProperty`, used directly.
- `Sheaf.AlgebraicGeometry.PerfectComplex`:
  `AlgebraicGeometry.Scheme.IsPerfect`, used directly.
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`:
  `CategoryTheory.derivedInternalHom_restrict_open`, the restriction isomorphism used
  in proof steps 1 and 3. This imports the recorded
  `Sheaf.Algebra.Homology.DerivedInternalHom`, `CategoryTheory.derivedInternalHom`.
- `Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison`:
  `AlgebraicGeometry.perfect_rhom_tensor_comparison`, read in full; a proof dependency
  for the perfect clause, not an additional assumption or notion in this signature.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh`:
  `AlgebraicGeometry.derivedPullback_tensor_preserve_QCoh`, read in full; the tensor
  closure clause is used in the natural-language proof, not in the signature.
- `Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent`:
  `CategoryTheory.affinePseudoCoherentRHomQuasiCoherent`, read in full; the affine
  calculation used in the natural-language proof, not in the signature.

The latter three modules introduce no notion required to elaborate this statement,
so are not imported solely to carry unused proof dependencies. The four proof steps in
the declaration docstring reproduce the node's route and name its dependencies.
Restriction of cohomology sheaves uses Mathlib's `SheafOfModules.overFunctor`, rather
than defining a second derived open-restriction functor. This is the localized-open
carrier also used by the dependency definitions and restriction lemma.

Edge cases checked: the empty scheme makes the local neighbourhood clause vacuous,
as it should. K=0 and L=0 satisfy the asserted vanishing without a nonzero assumption.
T=∅ gives zero L and zero RHom; T=X gives vanishing on the empty open. No quasi-compact,
quasi-separated, Noetherian or characteristic assumption occurs. On a disjoint union of
schemes with different upper bounds for K the conclusion permits different lower
bounds for RHom, avoiding the false global-bound assertion. In the perfect case L can
be unbounded in both directions. Universes u and w are explicit; there is no independent
universe for test schemes and no auto-bound implicit variable.

Searches actually run through `msearch.py C1 lem-sc-rhom-supported-qcoherent`:
- LeanFinder: `derived internal Hom pseudo coherent perfect quasi coherent support bounded below`:
  8 hits, consisting of derived-category t-structure and unrelated Grothendieck-category
  declarations; no scheme RHom quasi-coherence/support result.
- Loogle: `DerivedCategory.IsGE, SheafOfModules.overFunctor`: 0 hits.
- LeanSearch: `derived internal Hom perfect pseudo coherent quasi coherent`:
  unavailable, Internal Server Error (not treated as no match).
- Mathlib grep: `derivedInternalHom|IsPseudoCoherent|IsLocallyBoundedBelow`: 0 hits.
- Direct rg in upstream `WeilConjectures` for the item id, IsPseudoCoherent,
  derivedInternalHom, IsLocallyBoundedBelow: no matches. The required item-id grep
  also returned no matches.
- Direct rg in `lean/Sheaf/AlgebraicGeometry` and `lean/Sheaf/Paper` for support and
  local boundedness found affine RHom, support-generator, support-annihilation and
  perfect-comparison modules; none states this full three-clause result. The support
  generator uses inline stalkwise support, equivalent to the open-restriction vanishing
  used here, rather than supplying a separate support definition.
- Name search for `rhom_supported_quasiCoherent`, `rhom_supported`, and internal-Hom
  quasi-coherence variants in upstream, Sheaf and `dag/lean_names_upstream.json`:
  no declaration clash or exact existing statement.
- Read `coord/upstream-overlaps.md`: upstream `DerivedCategory.IsPerfect` is the
  ring-complex notion; it does not replace scheme-local `Scheme.IsPerfect`.

Validation: local `lcompile.py` compiled the module cleanly (exit code 0).

## Second reading by C1

Node list and Lean rendering, checked clause by clause:

- The object `X` is rendered by `(X : Scheme.{u})`; the explicit universe `u` covers
  arbitrary schemes, including the empty scheme. The shared derived-category instances
  are the two binders `[HasDerivedCategory.{w} ...]` and
  `[∀ U : X.Opens, HasDerivedCategory.{w} ...]`; these are infrastructure required by
  the recorded definitions and do not add geometric hypotheses.
- The objects `K L : D(O_X)` are rendered by `(K L : schemeDerivedCategory X)`, with
  `schemeDerivedCategory` exactly the dependency declaration for the ambient derived
  category. The hypothesis that `L` is quasi-coherent is `hL :
  schemeDerivedQCohProperty X L`, which quantifies over every cohomology sheaf.
- `RSheafHom(K,L)` is rendered uniformly as the object
  `((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
  X.toRingedSpace.sheaf).obj (op K, L))`, using the recorded
  `CategoryTheory.derivedInternalHom` declaration; no alternate Hom notion is used.
- The first implication has exactly `Scheme.IsPseudoCoherent X K` and
  `∃ a : ℤ, L.IsGE a` as hypotheses. Its conclusion is the conjunction of
  `schemeDerivedQCohProperty X` for RHom and the pointwise local bound
  `∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (...)`.
  The displayed object is the restriction by `SheafOfModules.overFunctor` of the
  homology sheaf, so the bound is local and may depend on `U` and `x`.
- The second implication has exactly `Scheme.IsPerfect X K` and concludes
  `schemeDerivedQCohProperty X` of the same RHom, with no boundedness condition on `L`.
- The support clause quantifies `T : Set X` and `hT : IsClosed T`, assumes the exact
  disjunction `((Scheme.IsPseudoCoherent X K ∧ ∃ a : ℤ, L.IsGE a) ∨
  Scheme.IsPerfect X K)`, assumes vanishing of every restricted homology sheaf of `L`
  on `⟨Tᶜ, hT.isOpen_compl⟩`, and concludes the corresponding vanishing for every
  homology sheaf of RHom there. Quantifier order agrees with the node.

Dependency declarations were re-opened: `Scheme.IsPseudoCoherent`,
`Scheme.IsPerfect`, `schemeDerivedCategory`, `schemeDerivedQCohProperty`,
`CategoryTheory.derivedInternalHom`, and `derivedInternalHom_restrict_open` are the
recorded notions and signatures. The three proof-only dependencies remain out of the
signature and introduce no extra assumptions. No dependency was unusable, so no
additional module or node was needed.

Edge cases checked: `X = ∅` makes the pointwise local-bound clause vacuous; `K = 0` or
`L = 0` is permitted; `T = ∅` and `T = X` give the expected complement restrictions;
no quasi-compact, quasi-separated, Noetherian, characteristic, nonzero, or finiteness
hypothesis is present. The lower bound is pointwise (not a false global bound), and the
perfect clause allows unbounded `L`. Universes `u` and `w` are explicit, with no
independent test-scheme or index universe.

Searches found no existing declaration: `msearch.py` LeanFinder search for derived
internal-Hom/pseudo-coherent/quasi-coherent/support (eight unrelated boundedness hits),
Loogle search for `DerivedCategory.IsGE, SheafOfModules.overFunctor` (zero hits), and
LeanSearch (service unavailable). Grep of Mathlib, upstream `WeilConjectures`, this
project's `lean/Sheaf`, and `dag/lean_names_upstream.json` found no matching theorem or
notion. The source pages Tag 0A6H parts (1), (2), and Tag 0A9C's support observation
match the three clauses.

No mismatch was found. The worker module already had the exact node statement, correct
imports and docstrings, and compiled cleanly with `lcompile.py`; therefore no Lean or
node changes were made in this second reading.
