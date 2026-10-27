## Worker report

The module `Sheaf.AlgebraicGeometry.HenselianCompletionOpenRigidity` states
`AlgebraicGeometry.Etale.henselian_completion_open_rigidity`. Its only theorem
has proof `sorry`. Three auxiliary definitions give real data for the canonical
objects in the statement; they introduce no independent mathematical notion.
The node copy changes only `lean`.

Hypotheses and clauses, matched individually:

- The commutative Noetherian ring is `C : Type u`, `[CommRing C]`,
  `[IsNoetherianRing C]`; the ideal is `I : Ideal C`.
- The henselian pair is `[HenselianRing C I]`, precisely the recorded
  henselian-terminology interface (the root-lifting formulation equivalent to
  unique lifting of idempotents in finite algebras).
- The completion is Mathlib's `AdicCompletion I C`. Its compatible sequences
  are indexed by natural numbers including zero; the zeroth quotient is the
  zero ring, so this is the same inverse limit as the node's positive indices.
- The two affine spectra are `Spec (CommRingCat.of C)` and
  `Spec (CommRingCat.of (AdicCompletion I C))`. The canonical map is
  `henselianCompletionSpecMap C I`, defined by `Spec.map` applied to
  `algebraMap C (AdicCompletion I C)`; the latter sends an element to its
  residue classes, as read in AdicCompletion/Algebra.lean.
- `henselianCompletionOpen C I` is the open with underlying set
  `(PrimeSpectrum.zeroLocus (I : Set C))ᶜ`. Thus its points are exactly the
  primes not containing `I`. Its `.toScheme` is the node's `U`.
- The completed open is literally the categorical pullback
  `pullback (henselianCompletionSpecMap C I) (henselianCompletionOpen C I).ι`.
  The canonical restricted map is `henselianCompletionOpenMap C I`, defined as
  `pullback.snd _ _`; no arbitrary map or chosen nonempty object is substituted.
- `F : Sheaf (henselianCompletionOpen C I).toScheme.smallEtaleTopology
  AddCommGrpCat.{u + 1}` is an abelian sheaf on the specified small etale site.
  The small site has object universe `u+1` and morphism universe `u`;
  coefficients use the published `u+1` convention, with no universe equality
  imposed on the site.
- `hF : F.IsTorsion` is the recorded local torsion predicate: on a covering
  sieve each restriction of a section has finite additive order, equivalently
  is killed by some positive integer. There is no uniform bound or
  constructibility assumption.
- `q : ℕ` ranges over exactly the integers `q ≥ 0` in the statement, including
  zero. Cohomology is `Sheaf.H F q`, the existing Ext/right-derived-global-
  sections encoding explicitly permitted by the etale-cohomology node's note.
  No alternative cohomology construction is introduced.
- The comparison is the published `Etale.cohomologyMap` along the canonical
  `henselianCompletionOpenMap C I`. Its codomain is definitionally
  `Sheaf.H ((upperStar AddCommGrpCat.{u+1}
  (henselianCompletionOpenMap C I)).obj F) q`, hence the inverse-image sheaf
  in the node. `Function.Bijective` says that this additive homomorphism is
  an isomorphism of abelian groups.
- Naturality is the second conjunct: for every torsion sheaf `G`, every
  `φ : F ⟶ G`, and every `x : Sheaf.H F q`, pullback after `Sheaf.H.map φ q`
  equals `Sheaf.H.map ((upperStar ...).map φ) q` after pullback. This is the
  explicit naturality square of the canonical maps, not existence of some
  unrelated natural equivalence.
- There is no excellence, regularity, invertible-torsion-order, local-ring,
  strict-henselian, or finite-type hypothesis in the Lean statement.

Dependency interfaces read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with
  `isNoetherianRing_iff_ideal_fg`, every ideal finitely generated.
- `WeilConjectures.Mathlib.RingTheory.Henselian` and its Mathlib import:
  `HenselianRing C I`; the recorded companion
  `IsStrictlyHenselianLocalRing` was read but is not assumed here.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`:
  `AdicCompletion`, its commutative-ring and algebra instances and canonical
  `algebraMap`; `evalOneₐ` identifies the projection to `C/I`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`;
  `Mathlib.AlgebraicGeometry.Pullbacks`: scheme pullbacks and `pullback.snd`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `Sheaf`;
  `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves` uses the recorded torsion
  predicate `CategoryTheory.Sheaf.IsTorsion` from
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`
  and its adjunction, via the public import of
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`;
  the latter supplies `cohomologyMap` and `cohomologyMap_map`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: the recorded
  `Etale.cohomology` and `rightDerivedGlobalSections`. The node explicitly
  permits the sheaf `Sheaf.H` encoding for the ordinary cohomology groups.
- Proof-only imports use the recorded
  `Sheaf.CategoryTheory.SpectralSequencePageInduction` and
  `WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension`.
  The three geometric/valuative proof dependencies currently have no Lean
  record and are not imported. They are not statement prerequisites.

The source was read directly: the local ILO PDF, Expose XX §4.4, printed
pp. 373–374. It states CTC for torsion abelian sheaves, then the strictly local
open-complement comparison (*), and describes the admissible blowup spectral
sequence and dense henselian valued-field reduction. The node's existing
Noetherian open-complement formulation and proof plan are preserved. The
maintenance repair note is resolved at stage 1 and does not withdraw the
current stage-2 assignment; the current node is `split` with no Lean record.

Edge cases checked semantically before writing:

- For `I = 0`, and more generally nilpotent `I`, the open complement is empty;
  the theorem retains this case without a nonemptiness assumption.
- For `I = ⊤`, the henselian-pair hypothesis forces the zero-ring case under
  the Jacobson condition. The zero ring itself is allowed; its spectrum and
  both opens are empty. No `Nontrivial C` instance is required.
- `q = 0` uses the same canonical cohomology map; no positive-degree
  restriction is introduced. The zero sheaf and its maps are allowed.
- Torsion of sections need only hold locally. Infinite etale objects are
  allowed, so pointwise torsion of every section group is not silently used.
- No residue-characteristic restriction or excellence assumption is present.

Searches actually run (logged in `searches.jsonl` by the prescribed wrapper):

- LeanFinder: “Torsion etale cohomology on the open complement of a Noetherian
  henselian pair is invariant under adic completion”. Eight hits, including
  `BDeRham`, `BDeRhamPlus`, `IsAdicComplete.henselianRing`, algebraic completion
  base-change identities, and an etale lifting lemma. None states this
  open-complement torsion cohomology comparison.
- Loogle: `"HenselianRing", "cohomology"`: zero hits.
- Mathlib grep: `Fujiwara|henselian.*cohomology|cohomology.*completion`: zero hits.
- LeanSearch: “Etale cohomology of a torsion abelian sheaf on the complement
  of a henselian pair is invariant under adic completion”. Eight hits on
  `AdicCompletion`, its ring/module structure, canonical map and algebraic
  completion lemmas; no etale cohomology comparison.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for completion/open,
  henselian/cohomology and the item's id found no declaration of this node.
  Existing Gabber results concern the closed fibre, and the topological
  invariance results assume a universal homeomorphism; neither is this
  completion map on the open complement. The canonical cohomology map and
  local torsion predicate were found and reused.
- Direct searches for all four proposed full declaration names in Mathlib's
  relevant spectrum files, project Lean, and `dag/lean_names_upstream.json`
  found no existing collision. PrimeSpectrum has `zeroLocus` as a closed set;
  the auxiliary open simply packages its complement as a scheme open.

Validation: `scompile.py` compiled the sandbox and library module cleanly
under the default 60-second limit, after marking the spectrum map
noncomputable as required by `Spec.map`. `autoImplicit` is disabled, and all
variables and the universe are explicit. The final dry-run recompiles the
finished file. No new nodes, dependency repairs, statement correction or
STATEMENT-DISPUTED flag is needed.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
