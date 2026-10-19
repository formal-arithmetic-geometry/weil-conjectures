## Worker report

`Sheaf.Paper.StratifiedLatticeRank` states
`AlgebraicGeometry.ProEtale.exists_clopen_rank_decomposition_of_isLisse`, with its
single theorem proof `sorry`. This packet repairs H3 in returned immutable head
`62e4e13a3aa2`: coefficients now use the canonical spectralNorm topology explicitly.
It retains the previously delivered rank-decomposition conclusion, the published
coefficient construction, and Q77's landed lisse predicate. No definitions or
new dependency modules are introduced.

Source: the current main-20261015 blueprint,
`sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice-rank.md`,
read with the enclosing unit and the node's reviewed seven-step proof. The natural
statement already specifies the l-adic topology, so correcting its Lean rendering
requires no change to the node's natural statement or proof.

### Hypotheses and clauses

In the descriptions below, “canonical continuous coefficient ring” means the
explicit expression used at every occurrence in the theorem:

```lean
@Profinite.continuousCoefficientRingObj E
  (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
  (@NonUnitalSeminormedRing.toIsTopologicalRing E
    (@SeminormedRing.toNonUnitalSeminormedRing E
      (spectralNorm.seminormedRing ℚ_[l] E)))
```

This is report shorthand only; the Lean signature repeats the actual expression.
The ring argument `_` is inferred from `Field E`, and the displayed topological-ring
instance is the one for the spectral seminormed ring. No topology is an implicit
input to the theorem and no new coefficient object is defined.

- Prime ell is `(l : ℕ) [Fact l.Prime]`.
- A finite extension E/Q_l is `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. Its prescribed topology is exactly
  `(spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace`.
  There is no arbitrary `NormedField E` or `NormedAlgebra ℚ_[l] E` parameter.
  This uses the same spectral norm as `Padic.coefficientExtensionAbsoluteValue`.
- An arbitrary scheme is `(X : Scheme.{u})`. There are no Noetherian,
  quasi-separated, characteristic, connectedness, or quasi-compactness binders.
- Underlined E is the canonical continuous coefficient ring above. The existing
  `Profinite.continuousCoefficientRingObj` has continuous-function sections with
  pointwise operations, in the coefficient universe; its commutativity comes from
  `Profinite.isCommMonObj_continuousCoefficientRingObj`.
- E_X = p_X^*(underlined E) is `condensedRingObj` applied to that ring and X.
  Every coefficient ring in the conclusion uses this very same topology.
- L is an internal module through the binder `L : Mod
  (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj ... X)`.
  `Mod` supplies the action, associativity, unitality, and module morphisms.
- Lissity is `hL : IsLisseCoefficientModule ... L`, the existing predicate:
  there exists a `Scheme.Cover.{u} Scheme.proetalePrecoverage X` whose canonical
  pullbacks satisfy `Mod.IsFree`, meaning isomorphic to `Mod.finiteFree R n` for
  some natural n on each member. Ranks can vary; the cover need not be finite.
- The loci are `∃ R : ℕ → X.Opens`, open by their type. The first conjunct
  `(∀ r : ℕ, IsClosed (R r : Set X))` supplies closedness.
- “Some” and the prescribed pointwise meaning are the second conjunct:
  `x ∈ R r ↔ ∃ (U : X.ProEt) (v : U.left), U.hom v = x ∧ Nonempty (...)`.
  The isomorphism is from the canonical pullback of L to `Mod.finiteFree ... r`.
  A finite-free neighborhood of a preimage is itself a pro-etale object over X.
  Conversely a trivializing object can be adjoined to an existing covering,
  which retains its fpqc finite refinements. This expresses the node's condition
  without choosing a particular covering as extra input.
- “Every”, independence of covering, and independence of preimage are the third
  conjunct: for every `U : X.ProEt`, rank `n`, isomorphism to `Mod.finiteFree ... n`,
  point `v : U.left`, and `r : ℕ`, `U.hom v ∈ R r ↔ n = r`. Applying this to
  open neighborhoods also handles rank trivializations near the chosen preimage.
- Finiteness is exactly
  `CompactSpace X → {r : ℕ | (R r : Set X).Nonempty}.Finite`.
  Quasi-compactness is assumed only for this clause.
- The decomposition is `IsIso (Sigma.desc (fun r : ℕ ↦ (R r).ι))`, the canonical
  map from the scheme coproduct of the actual open subschemes `(R r).toScheme`
  to X. This includes both covering and disjointness, with their scheme structures.
- Constant rank on the r-th piece is the final conjunct: there is a pro-etale
  `Scheme.Cover` of `(R r).toScheme` on every member of which pullback along
  `C.f i ≫ (R r).ι` is isomorphic to `Mod.finiteFree ... r`. The fixed r is used
  throughout that cover, and canonical pullback composition identifies it with
  restriction to the rank piece followed by restriction to the cover.

### Dependencies and source inspection

The module imports the recorded dependency interfaces and uses the following
existing declarations; no private replacement is made.

- `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` publicly imports
  `Sheaf.NumberTheory.Padics.CoefficientExtension`. The latter's
  `Padic.coefficientExtensionAbsoluteValue` is the absolute value of
  `spectralMulAlgNorm ℚ_[l] E`. Mathlib's
  `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` supplies
  `spectralNorm.normedField` and `spectralNorm.seminormedRing` for an algebraic
  extension of a complete nontrivially normed field; finite dimensionality
  supplies algebraicity. Their definitions and full signatures were inspected.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `sk-def-sfb-condensed-ring` and
  `def-weil-pbc-condensed-e-module-category`:
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`,
  `Profinite.continuousCoefficientRingObj` and
  `Profinite.isCommMonObj_continuousCoefficientRingObj`. The public import
  `ContinuousCoefficientUniverse` gives the full continuous-function constructor
  with parameters T, topology, ring, and topological-ring instance.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing` and `condensedRingObj`.
- `sk-def-sfb-module-objects`: Mathlib's `CategoryTheory.Mod`, `ModObj`,
  `Mod.forget`, and `Mod.regular`, as recorded in its closed upstream audit.
  `WeilConjectures.CategoryTheory.ModuleObjects.Free` supplies `Mod.finiteFree`
  and `Mod.IsFree`. These are internal modules, not discrete module sheaves.
- `sk-def-pe-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `Scheme.ProEt`, `Scheme.ProEt.topology`, and `Scheme.proetalePrecoverage`.
  Covers retain the fpqc finite-refinement condition.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace` in
  `Mathlib.Topology.Defs.Filter`, with no Hausdorff condition.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; actual rank pieces use `Scheme.Opens.toScheme`
  and `Scheme.Opens.ι`.
- `def-sfb-lisse-coefficient-module`: Q77's landed binding to
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`, in
  `Sheaf.Paper.CoefficientHeartCommonStratification`. Its complete definition was
  reread: a pro-etale cover with finite-free pullbacks and varying natural ranks.

Proof dependencies remain imported non-publicly: continuous-field realization,
continuous lattice coefficients, finrank, fpqc descent of opens, precoverage base
change, and weakly etale stability. Scheme coproducts and quasi-compactness are
provided by the public statement imports. The declaration docstring retains all
seven DAG proof steps and their identifiers. The current server source of
`Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization` was read using
`scompile.py --source` when absent from the local checkout.

### Edge cases

The empty scheme has empty rank loci and empty covers; all assertions involving
preimages are vacuous. The zero module has rank zero, allowed by the natural-number
indices and `Mod.finiteFree R 0`. Empty trivializing objects can have isomorphisms
at different ranks without contradiction because there is no point v. Distinct
nonempty rank loci are disjoint by the universal characterization. Disconnected
schemes can have ranks 1 and 2. An infinite disjoint union with unbounded ranks is
allowed, since finiteness is conditional on quasi-compactness. Nonreduced schemes,
characteristic l, and non-quasi-separated schemes are not excluded. Site objects
remain in universe u+1, site morphisms in u, and module values in u+1.
The base extension E = Q_l is included: no proper-extension or positive-degree
condition is added. The explicit spectral topology applies in this case as well.

### Searches

The saved packet records these earlier `msearch.py` searches, retained because the
rank assertion and dependency notions are unchanged:

- Lean Finder: “A lisse sheaf over pulled back condensed p-adic field coefficients
  has locally constant rank and a clopen rank decomposition on a scheme”. Eight
  hits, including `Module.isLocallyConstant_rankAtStalk` and its free-locus variant;
  none concerns these internal coefficient modules.
- Loogle: `SheafOfModules.IsLocallyFree, Module.isLocallyConstant_rankAtStalk`.
  No hits for the combined query; the separate notions inspected do not state
  this descent theorem.
- Mathlib grep: `locallyFree.*rank|rank.*locallyFree|rank.*locallyConstant` under
  `Algebra/Category/ModuleCat/Sheaf`: no hits.
- LeanSearch: “The rank of a finite locally free sheaf over a topological field
  is locally constant on a scheme and its rank loci form a clopen decomposition”.
  Eight hits, consisting of algebraic rank-at-stalk and locally constant functions;
  none is this statement.
- Direct `rg` searches in upstream `WeilConjectures`, `lean/Sheaf`, and the
  declaration index for the item id, rank/lisse combinations, `finiteFree`, and
  `IsLisseCoefficientModule` found the reused definitions, but no matching theorem.

For this repair, direct `rg` for `spectralNorm.normedField` and
`continuousCoefficientRingObj` in `lean/Sheaf`, plus inspection of Mathlib
`Analysis/Normed/Unbundled/SpectralNorm.lean`, `Analysis/Normed/Field/Basic.lean`,
`Analysis/Normed/Ring/Basic.lean`, and `Analysis/Normed/Ring/Lemmas.lean`, established
exactly how to pass the canonical topology and its existing topological-ring
instance. No helper definition is needed.

## Repair of returned head 62e4e13a3aa2

H3 required replacing the arbitrary NormedField topology by the canonical
spectralNorm topology and updating the Lean statement/report. The theorem now
binds only Field E, Algebra Q_l E, and FiniteDimensional Q_l E; all eight coefficient
ring occurrences explicitly pass the spectral topology and its standard
IsTopologicalRing instance. The old report's claim that arbitrary normed-algebra
binders themselves fixed the spectral topology has been removed. The node's
`lean.statement` is regenerated verbatim from the repaired signature.

The initial prescribed dry run reported a stale `lean.statement` after the changed
module was collected. Updating that record repairs the concrete preflight fault.
The earlier duplicate-node repair is retained: there is no packet copy of Q77's
lisse node and no obsolete module-object dependency copy. The existing stmt_deps
additions are retained. The delivery wrapper handles rebasing onto current main;
no direct git commands or shared-source writes are used.

## Second reading by Q85

I reread the natural statement, current blueprint rank lemma, saved packet, and
repaired Lean file. The finite extension binder is now algebraic data only,
`[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. Each occurrence of the
condensed coefficient ring explicitly fixes the topology to the spectral norm;
L, its lissity, both rank characterizations, and every free module therefore use
one canonical coefficient ring. This repairs the returned mismatch without a
natural-statement correction. The source's arbitrary scheme remains unrestricted.

The conclusion still gives every natural-number rank locus, its open subscheme
structure and closedness, existential and universal rank characterizations,
finiteness only for quasi-compact X, the canonical scheme coproduct isomorphism,
and local freeness of fixed rank r on each piece. Zero rank, empty objects, the
empty scheme, and infinitely many ranks without quasi-compactness remain included.
No equality between the object and morphism universes is imposed. There is one
theorem with a sorry proof, no new definition, and no remaining statement dispute.

### Validation

The repaired module passed `scompile.py Q85 det-lem-stratified-lattice-rank
lean/Sheaf/Paper/StratifiedLatticeRank.lean`: sandbox 8.2 s, library-module check
58.8 s, no errors or warnings. `autoImplicit` is disabled, the universe is explicit,
and all Lean lines are at most 100 characters. The signature in `lean.statement`
is exactly the source from `theorem` through the text before `:=`.
