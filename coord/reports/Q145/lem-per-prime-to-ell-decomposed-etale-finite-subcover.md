## Worker report

This delivery states `AlgebraicGeometry.primeToEllDecomposed_etale_finite_subcover` in
`Sheaf.AlgebraicGeometry.PrimeToEllDecomposedEtaleFiniteSubcover`. Its sole proof is `sorry`.
There are no new definitions or nodes, dependency repairs, or statement corrections.
Only the item's `lean` field changes. Q150's earlier merged delivery was stage 1:
its `reviewed` record is present, but it supplied no `lean` or `reviewed_lean` record.
The previous Q145 worker's empty-sandbox failure therefore did not settle this stage-2 item.

Read the complete item, all four statement-dependency nodes and their recorded declarations
and docstrings, the proof-dependency records, and the finite-subcover sibling module.
Read the actual source PDF, PDF pages 32--34 (printed pp. 26--28), with `pdftotext`:
ILO Exposé II 2.1.1 gives the lifting condition; Proposition 2.2.2 gives ind-constructible
loci for arbitrary étale sources; Corollary 2.2.4 extracts finitely many indices.
The node agrees with that source. No STATEMENT-DISPUTED or node fault remains.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A scheme X: `(X : Scheme.{u})`, using the declaration of `def-pc-scheme`.
- Noetherian, meaning a finite affine cover by spectra of Noetherian rings:
  `[IsNoetherian X]`. Mathlib's class extends `IsLocallyNoetherian X` and
  `CompactSpace X`. The exact equivalence with the stated finite affine cover is
  `AlgebraicGeometry.isNoetherian_iff_of_finite_affine_openCover` in
  `Mathlib.AlgebraicGeometry.Noetherian` (also
  `isNoetherian_iff_of_finite_iSup_eq_top`). Locally Noetherian schemes admit affine
  Noetherian covers, and compactness extracts a finite cover. Thus this is the same
  condition, not just topological Noetherianity. The ring condition is the recorded
  `IsNoetherianRing` of `def-weil-pbc-noetherian-ring`.
- A prime ell: `(ell : ℕ) (hell : ell.Prime)`. Values 0 and 1 are excluded exactly
  as in the item; no invertibility or condition on residue characteristics is added.
- A set-indexed family: `{I : Type w} (U : I → Scheme.{u})
  (f : ∀ i : I, U i ⟶ X)`. The index universe w is independent of u; the family
  may have any size. No finite or nonempty-index assumption is made.
- Every morphism étale: `(het : ∀ i : I, Etale (f i))`, using precisely
  `AlgebraicGeometry.Etale` recorded for `def-weil-etale-morphism`.
- Every x has a member i and a source point z: the hypothesis starts
  `hcover : ∀ x : X, ∃ (i : I) (z : U i), ...`.
- z lies above x: `f i z = x`, both in the hypothesis and the conclusion.
- The residue extension is finite: `((f i).residueFieldMap z).hom.Finite`.
  `RingHom.Finite` means finite generation as module via that very ring map.
  The source and target are the canonical fields `(U i).residueField z` and
  `X.residueField (f i z)`; the preceding equality identifies the latter with κ(x).
  There is no arbitrary algebra structure or arbitrary residue-field map.
- Its degree is prime to ell: `Nat.Coprime ((f i).residueDegree z) ell`.
  `Scheme.Hom.residueDegree` is exactly `Module.finrank` for the algebra supplied
  by the same canonical `residueFieldMap`. With finiteness stated explicitly, it
  is the actual finite field degree. For a prime ell, coprimality is equivalent
  to ell not dividing that degree. This appears unchanged in both hypothesis
  and conclusion.
- A finite subset of the original indices: `∃ I₀ : Set I, I₀.Finite ∧ ...`.
  A set of I is intrinsically a subset of I; no reindexing or new covering maps
  are introduced.
- The same property using those indices: `∀ x : X, ∃ i ∈ I₀, ∃ z : U i, ...`,
  with exactly the same above-point equality, finite field extension and prime-to-ell
  degree as in the hypothesis. No scheme point or member is silently replaced.
- Sources need not be quasi-compact or separated: `U i` is an arbitrary scheme,
  and its only morphism condition is the displayed `Etale (f i)`. There are no
  `QuasiCompact`, `IsSeparated`, `IsNoetherian`, reducedness, finite-type-over-a-base,
  or alteration-category hypotheses on the sources.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (`def-pc-scheme`).
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, whose data are ideals
  finitely generated (`def-weil-pbc-noetherian-ring`), used by the above Noetherian
  finite-affine-cover equivalence.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (`def-weil-etale-morphism`).
- `Mathlib.AlgebraicGeometry.ResidueField`: `AlgebraicGeometry.Scheme.residueField`,
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap` (`def-weil-residue-field`) and
  `AlgebraicGeometry.Scheme.Hom.residueDegree`.
- `Mathlib.RingTheory.Finiteness.Defs`: `RingHom.Finite`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian` and its
  finite-affine-cover equivalences, `AlgebraicGeometry.IsLocallyNoetherian`
  (`pqf-def-locnoeth`), `IsNoetherian.noetherianSpace`
  (`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`),
  `IsLocallyNoetherian.quasiSeparatedSpace`
  (`lem-weil-pbc-locally-noetherian-quasi-separated`).
- Proof-only imports: `Mathlib.Topology.NoetherianSpace` for
  `TopologicalSpace.NoetherianSpace.isCompact` and `noetherianSpace_TFAE`
  (`lem-sfb-noetherian-space-compact-subsets`), `Mathlib.Topology.Spectral.Basic`
  for `SpectralSpace` (`lem-weil-pbc-qcqs-scheme-spectral`), and
  `Mathlib.Topology.Spectral.ConstructibleTopology` for
  `compactSpace_withConstructibleTopology`
  (`lem-weil-pbc-spectral-constructible-topology-quasi-compact`).
- `lem-per-prime-to-ell-decomposed-locus-constructible` has no Lean record or
  Mathlib match yet. It is only a proof dependency, introduces no notion needed
  to state this theorem, and therefore has no module to import. Its exact role
  is retained in proof step 2 of the theorem docstring. The maintainer can add
  its proof-only import when its module lands.

Edge cases checked before writing:

- X empty: take `I₀ = ∅`; every lifting clause is vacuous.
- I empty: the covering hypothesis forces X empty, so the same choice works.
- An infinite family, empty members, or an unbounded index universe is allowed.
- An identity cover has residue degree 1, hence is allowed for every prime ell.
- A residue degree divisible by ell is rejected even when finite; no substitution
  of ordinary surjectivity or a degree-one lifting condition occurs.
- An infinite residue extension fails the explicit `RingHom.Finite` clause;
  Mathlib's default degree zero at infinite extensions is never used to admit it.
- Residue characteristics may equal ell, and mixed characteristic is allowed.
- Arbitrary non-quasi-compact and non-separated étale sources remain admitted.

Searches performed (2026-10-19):

- `msearch.py ... leanfinder`: "An etale covering family with residue field degrees
  prime to a prime ell on a Noetherian scheme has a finite subfamily with the same
  residue field lifting property". Eight results concerned ring-theoretic étale
  factorization/descent, not finite extraction of such families. No exact match.
- `msearch.py ... loogle`: "AlgebraicGeometry.Etale, Module.finrank, Nat.Coprime".
  Zero hits.
- `msearch.py ... grep`: `decomposed|Nisnevich|residue.*[Cc]oprime` in
  Mathlib's `AlgebraicGeometry`. Zero hits.
- `msearch.py ... leansearch`: "An etale family on a Noetherian scheme which lifts
  every point with residue degree prime to ell admits a finite subfamily with the
  same property". Eight hits concern definitions and ring-theoretic étaleness;
  none states the finite-subfamily assertion.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for prime-to-ell,
  decomposed finite subcovers, and residue-field coprimality found no exact theorem.
  The prescribed `grep -rn` for this item's full id there returned no match.
- `rg` in `lean/Sheaf` found `CompletelyDecomposedEtaleFiniteSubcover`, which requires
  residue-field isomorphisms (degree 1), and `PrimeToEllAlterationTopology`, whose
  family predicate is restricted to objects of `Alt S`. Read their full signatures.
  Neither states this arbitrary-source finite-subfamily theorem. Reusing the Alt
  predicate would add source hypotheses, so the existing Mathlib components are
  used directly. `AlterationCoverCalculus` only mentions the desired lemma in its
  proof documentation and states no equivalent standalone assertion.
- Searched the proposed full declaration name across Mathlib, upstream and side
  Lean sources: no collision. No new notions were needed.

Validation: the prescribed `scompile.py Q145 ...` compiled this file both as a sandbox
module (5.0 s) and at its intended library module path (2.5 s), with exit status 0
and no warnings or errors. Every universe and variable is explicitly bound and
`autoImplicit` is disabled. The only postponed result is this item's named theorem;
its docstring reproduces all three DAG proof steps with their dependency ids.

## Second reading by Q145

No second reading by a worker: this dispatcher brief requires direct delivery and forbids
starting other agents. The maintainer performs the independent review. The author checked
the node against the full signature clause by clause as recorded above.
