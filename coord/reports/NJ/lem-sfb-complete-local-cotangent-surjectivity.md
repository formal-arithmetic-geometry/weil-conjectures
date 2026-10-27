## Worker report

The module `Sheaf.RingTheory.CompleteLocalCotangentSurjectivity` states
`AlgHom.surjective_iff_relativeCotangent_surjective`, with its only proof `sorry`.
No definition, axiom, extra hypothesis, auxiliary theorem, or new DAG node is introduced.
The item's JSON changes only in `lean`; its accepted stage-1 split is preserved.

Source read: Stacks Project, `formal-defos.tex`, Tag 06GZ,
`lemma-surjective-cotangent-space`, equivalence (1) and (3), and the proof of
`lemma-surjective` for the relative-to-absolute cotangent argument. This node is
its specified coefficient-field specialization with Lambda=C. The docstring carries
the complete four-step DAG proof: direct lifting, correction by coefficient residues,
Nakayama on m_S/(m_R S), then complete-source surjectivity. No statement fault or
STATEMENT-DISPUTED issue was found.

Each hypothesis and clause is rendered as follows:

- The field k is `{k : Type u} [Field k]`. The three rings have independent universes
  `{C : Type v} {R : Type w} {S : Type t}` and `[CommRing ...]` instances.
- The k-algebra structures are `[Algebra k C] [Algebra k R] [Algebra k S]`.
- The unique-maximal-ideal assumption is `[IsLocalRing C] [IsLocalRing R]
  [IsLocalRing S]`; their actual ideals are `IsLocalRing.maximalIdeal`.
- All three Noetherian assumptions are `[IsNoetherianRing C]`, and the corresponding
  R and S instances, exactly as recorded on `def-weil-pbc-noetherian-ring`.
- Completeness for powers of the maximal ideal is the three instances
  `[IsAdicComplete (IsLocalRing.maximalIdeal C) C]`, and the analogous R and S instances.
  This uses the companion declaration on `def-weil-pbc-adic-completion`, equivalent
  to bijectivity of the canonical completion map; no different completeness notion is used.
- The specified residue fields k are the k-algebra equivalences `iC`, `iR`, `iS`
  from `IsLocalRing.ResidueField` to k. They identify the quotient by each maximal ideal
  compatibly with the given coefficient-field embeddings.
- The three continuous local k-algebra homomorphisms are `cR`, `cS`, `f : ... →ₐ[k] ...`,
  their three `[IsLocalHom ...toRingHom]` instances, and `hcR`, `hcS`, `hf`.
  `Continuous` explicitly uses `maximalIdeal.adicTopology` at both ends. Thus no arbitrary
  topology, discrete topology, or extra topology instance is imposed.
- The three maps induce the identity on the specified residue field precisely by
  `hresCR`, `hresCS`, `hresF`, using `IsLocalRing.ResidueField.map` and composition
  with the residue-field identifications. These spell out the node's assumptions even
  though k-linearity and the k-algebra residue identifications also imply them.
- Compatibility with the coefficient maps is `hcompat : f.comp cR = cS`.
- The extended ideal m_C S is `(IsLocalRing.maximalIdeal C).map cS.toRingHom`.
  The target denominator is its supremum with `IsLocalRing.maximalIdeal S ^ 2`,
  where supremum is ideal sum.
- The conclusion is an iff, with `Function.Surjective f` on the left. On the right,
  `∀ s : S, s ∈ maximalIdeal S → ∃ r : R, r ∈ maximalIdeal R ∧ f r - s ∈ ...`
  expands surjectivity of the canonical relative cotangent map on representatives.

For the last clause, put D_R=m_C R+m_R^2 and D_S=m_C S+m_S^2.
Locality puts D_R inside m_R and D_S inside m_S. Locality of f sends m_R^2
into m_S^2; coefficient compatibility sends m_C R into m_C S. Hence the given
f has a well-defined induced map m_R/D_R -> m_S/D_S. It is k-linear because f is.
Every source class has a representative r in m_R, every target class has a
representative s in m_S, and equality of the image class with the target class
means exactly f(r)-s lies in D_S. Thus the displayed representative formula is
exactly the node's conclusion, with the same canonical map, source quotient,
and target quotient. D_R disappears from the expanded formula because taking
representatives in a quotient is surjective. This is an expansion of the
surjectivity predicate, not replacement by a different cotangent space or an
arbitrary map, and needs no additional definition node or postponed well-definedness lemma.

Dependency declarations read and used:

- `def-weil-field`: `Field`, in `Mathlib.Algebra.Field.Defs` (Mathlib match).
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` and `isNoetherianRing_iff`,
  in `Mathlib.RingTheory.Noetherian.Defs`. Read also `isNoetherianRing_iff_ideal_fg`.
- `def-weil-pbc-adic-completion`: `AdicCompletion`, `IsAdicComplete`, in
  `Mathlib.RingTheory.AdicCompletion.Basic`. The latter is the exact recorded
  completeness predicate used in the signature.
- Proof dependency `lem-weil-pbc-nakayama-jacobson`:
  `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`, in `Mathlib.RingTheory.Nakayama`.
- Proof dependency `lem-weil-pbc-complete-source-surjective-mod-ideal`:
  `surjective_of_mk_map_comp_surjective`, in
  `Mathlib.RingTheory.AdicCompletion.Functoriality`.

Statement imports are public, and the two proof-only imports are plain imports.
`Mathlib.RingTheory.LocalRing.ResidueField.Basic` supplies the standard residue
field/map interface, and `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology`
supplies the actual maximal-ideal-adic topologies. All binders and universes are
explicit; `autoImplicit` is disabled. There is no file-local notation or instance.

Edge cases checked before writing:

- C=R=S=k: all maximal ideals and cotangent quotients vanish and f is the identity.
- k[[t]] -> k[[t]], t maps to t^2, with C=k: the map is not surjective and the
  target linear class of t cannot be lifted modulo t^2, in every characteristic.
- k[[t]] -> k[t]/(t^2), C=k: the map and the cotangent map are both surjective;
  the target is Artinian and complete, so the statement does not exclude this case.
- C=R=k[[x]], cR=id, S=R/(x^2): both relative cotangent spaces vanish, and the
  quotient map is surjective. This checks the coefficient-ideal summand is present.
- C=R=k[[t]], cR=id, S=k[[t]], cS=f with f(t)=t^2: the source relative cotangent
  space vanishes but the target is m_S/(t^2), so neither surjectivity holds.
- A zero ring cannot carry the stated residue-field identification with a field;
  no admissible zero-ring case is lost. No restriction on characteristic, dimension,
  finiteness of the field, or equal universes is present.

Searches for existing statements (logged via msearch.py where applicable):

- Preserved Loogle query `IsAdicComplete, Function.Surjective`: one unrelated
  `surjective_fontaineTheta` result.
- LeanFinder: "A local homomorphism of complete Noetherian local algebras with common
  residue field is surjective if and only if the induced relative cotangent map is
  surjective". Eight results on algebra presentations, differentials and their
  canonical quotient maps; none is this complete-local iff criterion.
- Loogle: `IsLocalRing, Function.Surjective`. Twelve results on locality under
  surjections, residue maps, finite module arguments and the smooth Jacobian
  criterion; none is the requested statement.
- LeanSearch: "A local map of complete local rings is surjective if its map on relative
  cotangent spaces is surjective". Eight hits, including `Ideal.mapCotangent`,
  residue-map surjectivity and `surjective_of_mkQ_comp_surjective`; no exact match.
- Mathlib grep via msearch: `cotangent.*[Ss]urjective|[Ss]urjective.*cotangent|mapQ`
  in RingTheory. Hits on extension cotangent modules, smooth presentations and
  generic quotient maps, with no matching iff criterion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for relative cotangent names,
  cotangent/surjectivity and this node id: no matching declaration. Read the existing
  `RingHom.surjective_of_finite_of_cotangent` in
  `Sheaf.RingTheory.SurjectiveOfFiniteOfCotangent`: it assumes a finite map and
  uses absolute cotangent spaces, so cannot be rebound to this node.
- Read `Ideal.mapCotangent` and `IsLocalRing.CotangentSpace` in
  `Mathlib.RingTheory.Ideal.Cotangent`; these supply absolute ideal cotangents, not
  the relative quotient or the complete-local theorem.
- Searched the proposed full declaration name across Mathlib, WeilConjectures and
  Sheaf: no collision.

Validation (2026-10-23 retry): scompile.py compiled this file in sandbox and library
modes, 1.1 seconds per compile, with no errors or warnings. deliver2.py --no-push
returned OK: commit 052901b34f5 passes the server preflight and compiles; nothing
was pushed by that dry run. The inherited unchanged-item failure did not recur.
The current stage-2 queue lists this item, and brief-stage2.md section 0 explicitly
authorizes recording its Lean statement without reopening the accepted split.
The live node still has no Lean record. No accepted split fields or launcher tools
were changed. The final delivery follows the successful dry run.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
