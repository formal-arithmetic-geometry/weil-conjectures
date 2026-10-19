## Worker report

`Sheaf.AlgebraicGeometry.FiniteDominantFibrePurity` states
`AlgebraicGeometry.finite_dominant_fibre_purity`, with `sorry` as its whole proof. It introduces
no definitions or additional theorems. The node copy changes only `lean`.

The correspondence with every hypothesis and conclusion is:

- `S C D : Scheme.{u}` supplies the base, target, and source schemes.
- `[IsIntegral S] [IsNoetherian S]` gives the integral Noetherian base. `IsNoetherian` extends
  the recorded `IsLocallyNoetherian` by `CompactSpace`, so global Noetherianity is retained.
- `[IsIntegral C] [IsIntegral D]` gives integrality of both total spaces.
- `h : C ⟶ S` and `f : D ⟶ S`, each with `LocallyOfFiniteType` and `QuasiCompact`, give exactly
  finite type over `S`, as prescribed by the finite-type definition node's record.
- `r : D ⟶ C`, `[IsFinite r]`, and `[IsDominant r]` give the finite dominant morphism.
  Finiteness already implies `IsIntegralHom r`; no redundant instance or normality is assumed.
- `hr : r ≫ h = f` gives precisely the compatibility making `r` an `S`-morphism.
- `n : ℕ` gives the fixed nonnegative integer. Choosing it as a parameter states the theorem
  for each possible witness, equivalently to assuming the existence of such an integer.
- `hn` quantifies over every `s : S`; `Nonempty (h.fiber s)` restricts the hypothesis to nonempty
  scheme-theoretic fibres `C_s`; `∀ Z ∈ irreducibleComponents (h.fiber s)` selects each
  irreducible component, and `topologicalKrullDim Z = (n : WithBot ℕ∞)` gives its dimension in
  the subspace topology.
- The conclusion quantifies over every `s : S` with `Nonempty (f.fiber s)` and every component
  of `f.fiber s = D_s`, requiring exactly the same dimension `n`.

The statement uses the recorded dependency declarations directly:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral` (sections over each
  nonempty open are domains; the class also supplies nonemptiness).
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`, via the
  parent of `AlgebraicGeometry.IsNoetherian` (local Noetherianity plus compactness).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`
  and `AlgebraicGeometry.QuasiCompact` (the latter defined in its QuasiCompact import).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`, with the
  canonical `IsFinite.instIsIntegralHom` instance already supplying integrality.
- `Sheaf.AlgebraicGeometry.NormalScheme`: the recorded multi-notion interface for
  `AlgebraicGeometry.IsDominant`, defined in Mathlib's Morphisms.UnderlyingMap as dense range.
  The other notions carried by that dependency are not imposed.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`, the pullback along
  the residue-field point.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, the exact `mathlib_match` of
  `def-weil-irreducible-components` (a Mathlib leaf without a Lean record).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, valued in `WithBot ℕ∞` and applied
  to each component as a subspace.

I read all statement-dependency nodes and the full signatures and docstrings of these
notions. Statement imports are public; the modules of the recorded proof dependencies are
also imported privately. The theorem docstring carries all six proof steps and their node
citations, including the generic-point fibre argument and the separate `n = 0` case.

The edge cases checked are zero dimension, empty individual fibres, structure morphisms whose
image does not contain the generic point of `S`, nonreduced fibres, and inseparable finite
maps. Integrality excludes empty total spaces as the node requires. Empty fibres impose no
condition; the hypothesis explicitly concerns `C_s` and the conclusion explicitly concerns
`D_s`. No dominance over `S`, flatness, normality, algebraic closedness, or reducedness of
fibres is added. There is no test-object universe in this statement; all schemes and their
morphisms use the standard common arbitrary scheme universe `u`.

Searches actually run in this session (also logged by msearch in the sandbox):

- `msearch.py ... leansearch` with query "Finite dominant maps of integral schemes preserve
  pure dimension of every fibre over an integral Noetherian base": eight hits, including
  `IsFinite`, `IsDominant`, finite-implies-integral, and base-change instances; no purity
  transfer theorem.
- `msearch.py ... leanfinder` with query "For a finite dominant morphism of integral schemes
  over an integral Noetherian base, if every target fibre is pure of dimension n then every
  source fibre is pure of dimension n": eight hits, including finite/discrete fibres,
  `IsIntegralHom`, and dominance of normalization; no matching theorem.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsDominant`: zero hits.
- `msearch.py ... grep` with pattern
  `IsFinite.*[Dd]im|[Dd]im.*IsFinite|equidimensional|pure.*dimension` in `AlgebraicGeometry`:
  seven hits, on finite monomorphisms/closed immersions and explanatory cycle prose; none
  states fibre purity.
- `rg` in the slopmaster2 `WeilConjectures` tree, in `lean/Sheaf`, and in
  `dag/lean_names_upstream.json`, by the exact node id, proposed declaration name, and
  finite-dominant/fibre-purity terminology: no exact existing declaration. The related
  `FlatDenseGenericFibrePureDimension` and `RelativeDimensionBaseChange` statements concern
  flat families and arbitrary field base change respectively, so neither states this node.

The previous worker's duplicate-delivery concern was checked against the authoritative node
and Q86 report: Q86 delivered a stage-1 split, with no module or `lean` record. The node remains
in the stage-2 state queue. This delivery retains that reviewed split and supplies its first
Lean statement; it does not re-deliver or alter Q86's stage-1 proof.

Node metadata fault: its inherited `source.document` still says `more-morphisms.tex` and
its place still mentions componentwise going-up, although the actual reviewed proof uses
02FZ in `morphisms.tex`. I opened `morphisms.tex` at
`lemma-openness-bounded-dimension-fibres`, `varieties.tex` at
`lemma-dimension-locally-algebraic`, and `schemes.tex` at `lemma-fibre-topological`.
The module cites those correct source places and follows the existing six-step proof.
Only the allowed `lean` field is changed; no mathematical statement correction is needed.

No new nodes, dependency repairs, or `STATEMENT-DISPUTED` issues are needed. During the final
clause audit I corrected the draft's conclusion guard to `Nonempty (f.fiber s)` and removed
a redundant `IsIntegralHom` instance flagged by Lean's overlapping-instance linter.

## Second reading by Q53

Independent maintainer second reading, 2026-10-18, of immutable delivery
`accba633c5f3ee7f5bdfe78953022056803a2803`. The reviewer did not author or previously
second-read this delivery. This section replaces the delivered placeholder and records
an actual reading of the item, all eight statement dependencies, source places, and Lean.

Clause audit (all pass):

- Base and total spaces: `(S C D : Scheme.{u})` introduces precisely the three schemes.
  `[IsIntegral S] [IsNoetherian S]` expresses integral and globally Noetherian, as the item
  explicitly requires. `IsNoetherian` is local Noetherianity plus compactness; the dependency
  `pqf-def-locnoeth` alone only defines the local notion. `[IsIntegral C] [IsIntegral D]`
  expresses both integral total spaces, including nonemptiness.
- Structure maps and finite type: `(f : D ⟶ S) (h : C ⟶ S)` with
  `[LocallyOfFiniteType f] [QuasiCompact f]` and the same pair for `h` is exactly the
  finite-type convention of `def-weil-finite-type-morphism`.
- The cover: `(r : D ⟶ C) [IsFinite r] [IsDominant r]` is finite and dominant;
  `(hr : r ≫ h = f)` states the S-morphism condition in categorical composition order.
  Mathlib's finite-implies-integral instance supplies integrality of the morphism.
  No normality, flatness, separability, or dominance of either structure map is assumed.
- Dimension: `(n : ℕ)` is the common nonnegative integer. Universal quantification in
  this witness states the requested implication for every possible witness to the
  prose's existence assumption.
- Hypothesis: `hn` quantifies over all `s : S`, guards by `Nonempty (h.fiber s)`, and
  requires `topologicalKrullDim Z = (n : WithBot ℕ∞)` for every
  `Z ∈ irreducibleComponents (h.fiber s)`. These are scheme-theoretic fibres and component
  subspace dimensions, not local-ring dimension or dimensions of component stalks.
- Conclusion: exactly the same condition for `f.fiber s`, guarded by
  `Nonempty (f.fiber s)`. The base point, component, and dimension quantifiers are correct.
- The JSON `lean.statement` equals the theorem signature verbatim, from `theorem` through
  the conclusion before `:= by`; checked by direct string equality. All variables and the
  arbitrary universe `u` are explicitly bound. The common scheme universe follows the
  ambient category; no test-object quantifier or hidden universe equality is introduced.

Declaration audit: read Mathlib `IsIntegral` and its reduced/irreducible equivalence
(Properties.lean:240,307), `IsLocallyNoetherian` and `IsNoetherian`
(Noetherian.lean:57,280), `LocallyOfFiniteType` (FiniteType.lean:43), `QuasiCompact`
(QuasiCompact.lean:43), `IsFinite` and its integral instance (Finite.lean:39,117),
`IsDominant` (UnderlyingMap.lean:217), `Scheme.Hom.fiber`, projections and fibre homeomorphism
(Fiber.lean:38,41,46,103), `irreducibleComponents` (Irreducible.lean:107), and
`topologicalKrullDim` (KrullDimension.lean:39). Read NormalScheme.lean: it imports the
recorded existing dominance notion and adds no hypothesis to this theorem. No private
copy or new definition is present.

Source and proof audit: Morphisms 02FZ (`morphisms.tex:5468`) makes the bounded local
fibre-dimension locus open in the source. The six docstring steps correctly use it on D,
exclude the generic point from the smaller-dimension locus, and treat n=0 separately.
The common image t of the total-space generic points need not be generic in S.
Schemes 01K1 (`schemes.tex:3511`) justifies the fibre-subspace argument at t; Varieties
0A21 (3),(5) (`varieties.tex:3783`) gives the locally algebraic dimension comparisons;
Algebra 00OK/00OY (`algebra.tex:27361,28025`) gives the finite-surjective dimension
argument. Topology 0055/0B7I (`topology.tex:1392,1428`) gives local dimension and its
supremum formula. Read the exact imported dimension, openness, equidimensional-open,
and constant-local-dimension-component interfaces; their assumptions are available on
these fibres. The supremum formula's current source was retrieved using
`scompile.py --source WeilConjectures.Topology.DimensionSupremumLocalDimensions` because
that file is absent in the older local source trees.

Edge cases pass: n=0, empty individual fibres, integral (hence nonempty) total spaces,
structure maps supported over a nongeneric base point, nonreduced fibres, inseparable
finite covers, and arbitrary characteristic. Nothing requires geometric fibres, an
algebraically closed field, reduced fibres, or a normal base. Finite type over each residue
field supplies the needed Noetherianity and finite dimensions.

Independent searches used `rg` with purity/fibre, finite/dominant/dimension and
equidimensional terminology across Mathlib algebraic geometry, slopmaster2
WeilConjectures, the group's lean/Sheaf tree and upstream-name index. No existing theorem
states this transfer. Opened FlatDenseGenericFibrePureDimension and
RelativeDimensionBaseChange: their flat-family and base-change statements differ.
The worker's three kinds of search are retained above. No duplicate notion is introduced.

Pilot gates pass: one theorem, whose whole proof is `by sorry`; no definition, axiom,
helper construction, local proof, or additional assumption. Both module and theorem
docstrings identify sources and blueprint; the theorem carries all six DAG proof steps.
All lines are at most 100 characters. Statement dependencies are public imports and
recorded proof interfaces are imported. No pro-etale substitute or infinity/dg/model
machinery occurs. No statement/proof dependency occurs in the current route-pivot dropped
list, and no item-specific repair note exists on origin/newtargets-dag.

Findings and changes: H11 was the sole landing defect: the delivered second-reading
section merely said that no second reading had taken place. This complete independent
audit repairs it without changing Lean or the node. The inherited node source metadata
still names more-morphisms.tex and advertises componentwise going-up; this is not the
argument being used. The worker disclosed it, and the actual proof, proof_origin and Lean
docstrings identify the correct sources above. No unsupported componentwise claim is
used. Stage-2 field restrictions do not permit an unrelated source-field edit here.

Compiler evidence: the immutable worker report contained no explicit per-file compile
transcript. Reproduced on 2026-10-18 with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q53 lem-trf-finite-dominant-fibre-purity <review-root>/snapshot/lean/Sheaf/AlgebraicGeometry/FiniteDominantFibrePurity.lean`.
Exit status 0, no Lean diagnostics. Output: sandbox `Sheaf/Stage2/Sandbox0.lean`
compiled into the private overlay in 3.1 s; library
`Sheaf/AlgebraicGeometry/FiniteDominantFibrePurity.lean` passed in 45.7 s.
The installed scompile.py is the 2026-10-17 server-overlay wrapper, despite the brief's
older local-overlay description; only this prescribed wrapper was invoked. Each Lean
invocation retains the 60 s limit. No direct ssh, global build, live Lean write, delivery,
merge, or repository mutation was performed. The three delivered files were compared
byte-for-byte with the named immutable Git commit and match.

Verdict: FIX, solely the complete report replacement containing this real second reading
and reproducible compiler evidence. The Lean statement is correct in substance.
