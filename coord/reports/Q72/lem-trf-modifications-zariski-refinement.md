## Worker report

The module `Sheaf.Paper.ModificationsZariskiRefinement` states the finite-open-cover
refinement theorem and its finite-family consequence. Both proofs are exactly `sorry`;
there are no new definitions, axioms, helper nodes, dependency repairs, or statement changes.
The modification predicate is reused directly, including both density requirements.

Hypothesis and conclusion correspondence:

- “S integral Noetherian”: `(S : Scheme.{u}) [IsIntegral S] [IsNoetherian S]` in both
  declarations. Mathlib's `IsNoetherian` extends `IsLocallyNoetherian` and `CompactSpace`,
  exactly the convention of the dependency; integrality supplies reducedness.
- “finite open cover S = union U_i”: `(n : ℕ) (U : Fin n → S.Opens)` and
  `(hcover : (⨆ i, U i) = ⊤)`. `Fin n` enumerates an arbitrary finite list, with no
  distinctness or nonemptiness assumptions on its members.
- “for each i, q_i : V_i → U_i”: the scheme family `V` and dependent morphism family
  `q : ∀ i : Fin n, V i ⟶ (U i).toScheme`.
- “q_i a modification”: `hq` uses the recorded `Orgogozo.IsModification` itself.
  Its implicit compactness argument for `(U i).toScheme` is supplied explicitly by
  `isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact
  (U i : Set S))`. This is a term made from existing Mathlib proofs of compactness of
  subsets of a Noetherian space, not an additional hypothesis or postponed helper.
  Reducedness and local Noetherianity of these open subschemes are inferred.
- “there exists a modification q : S' → S”: `∃ (S' : Scheme.{u}) (p : S' ⟶ S),
  IsModification p ∧ ...`. The conclusion retains properness, a dense open where
  the base-changed map is an isomorphism, and density of its inverse image.
- “the restriction S' ×_S U_i → U_i factors through q_i, over U_i”: for each index
  there is `a : pullback p (U i).ι ⟶ V i` with
  `a ≫ q i = pullback.snd p (U i).ι`. The equation asserts precisely compatibility
  with the indicated base, not merely existence of an unrelated morphism.
- “in particular finitely many modifications of S have a common refinement”: the
  second theorem takes `n`, `V`, maps `q i : V i ⟶ S`, and their modification proofs.
  It concludes the same existence of `(S', p)` and maps `a : S' ⟶ V i` satisfying
  `a ≫ q i = p`. It allows the empty family.

Dependency declarations read and used:

- `Sheaf.Paper.OrgogozoInductionData`, `AlgebraicGeometry.Orgogozo.IsModification`.
  Read the entire module and the dependency's natural statement; the unrelated
  nearby-cycle definitions impose no coefficient assumptions on this theorem.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and the universal
  property `pullback.lift`; Mathlib provides scheme pullbacks.
- `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian` and
  `AlgebraicGeometry.IsNoetherian`.
- `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`;
  the open embeddings in the statement are the canonical `(U i).ι`.

The public imports expose the six statement-dependency modules. Proof-only imports
retain the stated plan: properness, quasi-separatedness, admissible blow-ups,
strict transforms, blow-up properness and density, extension and elimination of
indeterminacy. The two sketch nodes have no `lean` record but their audited upstream
operations are available in `WeilConjectures.Blowup.Extension` and
`WeilConjectures.Compactification.EliminationOfIndeterminacy`, which are imported.
The docstrings carry all seven proof steps, including the proper closed-image argument
turning each open-immersion strict transform into an isomorphism, and the empty-family case.

Source checked: Orgogozo's author PDF, §2.1 on printed page 3, reduces to a finite affine
cover and cites RG71 I §5.3.3 for globalization. Its §1 definition of modification and
the recorded project's definition were read as well. The node's reviewed seven-step
expansion supplies the finite-cover construction via Stacks 081S/081T and 080M/080N.
No source-based correction is needed.

Edge cases checked before and after writing:

- Empty cover (`n = 0`): `hcover` would force `⊥ = ⊤` on the nonempty integral base,
  so this case is impossible without imposing any extra nonemptiness binder.
- Empty family of global modifications: the second theorem remains meaningful;
  `p = 𝟙 S` is a modification and the factorization clause is vacuous.
- Empty member of a nonempty cover: its pullback is empty, so the factorization is
  the unique empty-source map. The local modification forces its source empty as well.
- Singleton cover and repeated opens: both are allowed; a singleton full cover
  gives the expected local modification itself as a possible refinement.
- A field base, nonseparated integral Noetherian bases, and modifications with
  nonreduced sources are allowed. No projectivity, normality, reducedness of the
  sources, or compatibility of different q_i on overlaps is assumed.
- The arbitrary universe `u` is shared by all schemes, as in the recorded predicate;
  `Fin n` is just a finite enumeration and imposes no universe restriction on schemes.

Searches for an existing statement:

- `msearch.py`, LeanFinder: “Modifications over a finite open covering of an integral
  Noetherian scheme admit a global proper birational refinement”: eight hits,
  including normalization covers, rational-map covers, affine refinements and finite
  affine-cover criteria for Noetherianity; none constructs this refinement.
- `msearch.py`, Loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.IsOpenImmersion`:
  zero hits.
- `msearch.py`, LeanSearch: “A common modification dominates proper birational morphisms
  on a finite open cover of a Noetherian scheme”: eight hits about properness under
  restriction/composition, dominance and normalization; none states the existence claim.
- `msearch.py`, grep in Mathlib's AlgebraicGeometry:
  `modification.*refin|refin.*modification|blowup.*extend|extend.*blowup`: zero hits.
- Direct `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
  `IsModification`, modification/refinement combinations and common-modification names;
  also searched the exact node id in upstream and `dag/lean_names_upstream.json`.
  The exact id has no upstream declaration. Read
  `WeilConjectures.Compactification.CommonModification.nonempty_commonModification`:
  it glues two separated finite-type models of a prescribed common open, and does
  not state this finite-cover theorem. Read `Compactification.exists_common_dense_refinement`
  in the side library: it concerns compactifications of one fixed morphism and boundary
  conditions, not modifications of arbitrary local bases. Neither is an exact match.

No STATEMENT-DISPUTED flag or node fault was found. The only elaboration repair supplied
existing compactness evidence explicitly; it does not change the mathematical statement.

Validation: `scompile.py Q72 lem-trf-modifications-zariski-refinement` compiled the
single delivered module cleanly in both sandbox and library contexts. The prescribed
`deliver2.py ... --no-push` returned `OK (dry run)`: preflight and compilation passed.
A final packet check confirmed that only the node's `lean` field changed, its recorded
signature is verbatim, both theorem proofs are whole `sorry` proofs, and every Lean line
has at most 100 characters. Independent review is the maintainer's delivery review, per
the dispatcher's current direct-delivery workflow; no independent worker review is claimed.

## Second reading by Q72

The delivered section was a placeholder ("No second reading by a worker"), which is H1/H11.
This reading replaces it. It was written by the maintainer's independent reviewer
(cc review service, run 2) after reading the node, its six statement dependencies, Orgogozo
§1 and §2.1 (as quoted in the node), Stacks 081S, 081T, 080M and 080N, and the module. The
module, the node record and the worker report are unchanged.

Node statement, item by item, with its Lean rendering and verdict:

1. "S integral Noetherian": `(S : Scheme.{u}) [IsIntegral S] [IsNoetherian S]`. Mathlib's
   `IsNoetherian` is `IsLocallyNoetherian` + `CompactSpace`, which is exactly pqf-def-locnoeth
   plus def-weil-pbc-quasi-compact-scheme. `IsIntegral` is def-pc-integral-scheme, with
   nonemptiness included. It also yields the `IsReduced` instance that the conclusion's
   `IsModification p` needs. Verdict: exact, and no extra assumption.
2. "S = U_1 ∪ … ∪ U_n, a finite open cover": `(n : ℕ) (U : Fin n → S.Opens)
   (hcover : (⨆ i, U i) = ⊤)`. Repeats and empty members are allowed. Verdict: exact.
3. "q_i : V_i → U_i": `V : Fin n → Scheme.{u}`, `q : ∀ i, V i ⟶ (U i).toScheme`. Verdict:
   exact; the open subscheme is the canonical `(U i).toScheme`.
4. "q_i a modification [def-trf-orgogozo-induction-data]": `hq` uses the recorded
   `AlgebraicGeometry.Orgogozo.IsModification`. Its instance arguments are as follows.
   `IsReduced` and `IsLocallyNoetherian` of the open subscheme are inferred from Mathlib's
   open-subscheme instances. `CompactSpace` is the explicit Mathlib term
   `isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)`, a Prop, so any other proof
   is defeq and citers are not constrained. The predicate holds the node's three clauses:
   proper; iso over a dense open `U` (`IsIso (pullback.snd q U.ι)`); dense inverse image.
   Verdict: exact.
5. "there exists a modification q : S' → S": `∃ (S' : Scheme.{u}) (p : S' ⟶ S),
   IsModification p`. Verdict: exact, with the same universe as S, as the blow-up construction
   gives.
6. "for every i, S' ×_S U_i → U_i factors through q_i, over U_i":
   `∀ i, ∃ a : pullback p (U i).ι ⟶ V i, a ≫ q i = pullback.snd p (U i).ι`. `pullback p ι`
   is def-pc-fibre-product's `S' ×_S U_i`, and `pullback.snd` is its projection to U_i. The
   equation is precisely "over the indicated base". Verdict: exact. The quantifier order is
   ∃ p, then ∀ i ∃ a, as in the node.
7. "In particular finitely many modifications of S have a common modification refinement",
   with factorizations over S: `exists_common_modification_refinement` with
   `q : ∀ i, V i ⟶ S`, `hq : ∀ i, IsModification (q i)` and conclusion
   `∃ S' p, IsModification p ∧ ∀ i, ∃ a : S' ⟶ V i, a ≫ q i = p`. Verdict: exact, with the
   empty family allowed.

Edge cases:
- n = 0: `⨆` over `Fin 0` is `⊥`, and `hcover` is false on the nonempty integral S. The node
  is vacuous in the same way.
- An empty U_i: `IsModification` forces V_i to be empty (U = ∅ is dense in ∅, and the pullback
  is an iso). The pullback of p along an empty open is empty, so the factorization exists, as
  in node step 6.
- n = 1 with U_1 = S, repeated opens, a field base, and nonreduced sources V_i: all allowed.
- The empty family in the second theorem: `p = 𝟙 S` (node step 7).
- Universes: a single `u` for S, V_i and S', as in the recorded `IsModification`. `Fin n`
  imposes nothing.

Searches: `rg` in the side clone (lean/Sheaf, lean/WeilConjectures) and in slopmaster2 found
neither declaration name. `nonempty_commonModification` (Compactification/CommonModification)
glues two separated finite-type models of a common open; it does not state this result. No
other `IsModification`-refinement statement exists. The worker's LeanSearch, LeanFinder,
Loogle and grep records are adequate.

Gates: no definitions, so nothing can be hollow. Both proofs are exactly `sorry`
(`#print axioms` shows only `sorryAx` beyond the standard axioms). The module and both
declarations carry docstrings with the source and `(blueprint: …)`. The main theorem's
docstring carries the node's seven proof steps. Lines are at most 100 characters (maximum 92).
The public imports are what the statement uses. The private imports are exactly the
stated proof-dependency modules: Morphisms.Proper, Morphisms.QuasiSeparated,
Blowup.AdmissibleBlowup, Proper, Density and Extension, Compactification.StrictTransform and
EliminationOfIndeterminacy. `lean.statement` is verbatim in the file. Only the node's `lean`
field changed.

Compile: `tools/nt_compile.py --json` (side overlay, nice 19, 60 s limit) compiled
`Sheaf/Paper/ModificationsZariskiRefinement.lean` with no error and no diagnostic in 5.8 s and
10.5 s. A probe copy showed that the tool does report errors. The `#check` of the elaborated
signature showed every variable bound.

Mismatches found: none in the statement. The only change is this section.
