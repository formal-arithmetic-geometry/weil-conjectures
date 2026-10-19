## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteOverProjective` states
`AlgebraicGeometry.finite_over_projective_affineLocally`, with one `sorry` and no definitions
or proved lemmas. The item's natural statement is unchanged, including its previously reviewed
correction from a global conclusion to an affine-local conclusion.

Hypothesis and conclusion correspondence:

- Schemes S, T, Y: `{S T Y : Scheme.{u}}`; the universe is arbitrary and shared by the schemes.
- S Noetherian in the specified sense: `[CompactSpace S] [IsLocallyNoetherian S]` renders
  exactly quasi-compactness plus local Noetherianness.
- The named projective morphism p: `(p : T ⟶ S) [IsProjective p]`. This is precisely the
  global closed-embedding plus quasi-compactness convention of the dependency.
- The named finite morphism h: `(h : Y ⟶ T) [IsFinite h]`.
- Every affine open U of S: `∀ (U : S.Opens), IsAffineOpen U → ...`.
- The inverse image Y_U is `((h ≫ p) ⁻¹ᵁ U).toScheme`. T_U is intermediate proof notation,
  not extra data or a separate conclusion in the statement.
- The nonnegative integer N is `(N : ℕ)`; N=0 is allowed.
- Projective space P^N_U is `ℙ(ULift.{u} (Fin (N + 1)); U.toScheme)`, with exactly N+1
  homogeneous coordinates, lifted to the scheme universe.
- The asserted embedding is the existential morphism i from that Y_U into P^N_U with
  `IsClosedImmersion i`.
- Being over U is exactly the equation `i ≫ ℙ(...) ↘ U.toScheme = (h ≫ p) ∣_ U`.
  `morphismRestrict` is the canonical map from the indicated inverse-image open to U.
- The explicit 'thus projective' clause is `IsProjective ((h ≫ p) ∣_ U)`.
- The affine-base 'in particular' clause is `IsAffine S → IsProjective (h ≫ p)`.
  There is no unconditional global projectivity conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian` (the
  affine-open coordinate-ring definition, equivalent to the node's cover formulation).
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no separation axiom).
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `AlgebraicGeometry.IsProjective`
  and `AlgebraicGeometry.IsHProjective`. The local source mirror retains the identical
  definitions in `Sheaf/AlgebraicGeometry/Morphisms/Projective.lean`; the node's canonical
  upstream import was accepted by the server compile.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `AlgebraicGeometry.ProjectiveSpace`
  and its structural morphism. `Mathlib.AlgebraicGeometry.Restrict`: `morphismRestrict`.

The modules of all recorded, stated proof dependencies are imported (proof-only imports
without `public`). Mathlib properness, closed-immersion, finite-type and projective-spectrum
interfaces are included directly or through these imports. The docstring follows all six
steps of the node's proof and names the dependencies at each step.

Edge cases checked: empty base or empty source, empty affine opens, zero coordinate rings,
N=0, arbitrary characteristic, and arbitrary scheme universe. No nonemptiness, field,
reducedness, integrality, separatedness of the base, or surjectivity of h is assumed.
An empty source can still admit a closed immersion into P^0. The statement retains the
Noetherian and quasi-compact base hypotheses even though some conclusions may hold more
generally. The existing reviewed affine-local correction is sufficient; no further node
fault or statement dispute was found.

Searches for an existing statement:

- `msearch.py leanfinder`: 'A finite morphism to a projective scheme is projective locally
  on a Noetherian base'. Eight hits: Proj properness and local finite type, finite implies
  proper, proper implies local finite type, finite iff proper and affine, and preservation
  of local Noetherianness. None supplies this projective embedding assertion.
- `msearch.py loogle`: 'AlgebraicGeometry.IsProjective, AlgebraicGeometry.IsFinite'.
  Zero hits; the public service does not know the project's IsProjective identifier.
- `msearch.py grep`: 'IsProjective|finite.*projective', subdirectory AlgebraicGeometry.
  Zero Mathlib hits. Also searched 'finite.*projective|IsProjective', with no hits.
- `msearch.py leansearch`: 'A finite cover of a projective scheme over a Noetherian base
  is projective over each affine open of the base'. Service unavailable (Internal Server
  Error); no mathematical conclusion is drawn from that failed service.
- `rg` of the upstream WeilConjectures tree for the item id: no hits. Concept searches
  'finite.*[Pp]rojective|[Pp]rojective.*finite' found unrelated module-projectivity,
  Chow, group-scheme and affine-immersion results, not this finite-cover theorem.
- `rg` of `lean/Sheaf` found uses in `FiniteGenericCurveModel.lean`, not a statement
  implementing this node. Searches for the chosen full declaration name and
  `finite_over_projective` in the upstream name index and both source trees found no clash.

Validation: `scompile.py NU lem-fin-finite-over-projective` accepted the module on the
server, nice 19, two threads, 60 seconds per file. Its private overlay compiled the relative
Proj side dependencies first; the delivered module compiled in 1.4 seconds, without warnings.
No local compiler or global build was run.

## Second reading by NU

I independently read the item JSON, all its statement-dependency nodes and their
recorded definitions, the sandbox Lean module, and the blueprint source at
sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-over-projective.md, order 1601.
I also read Morphisms 01W8 and 01WB (the H-projective/local-projective distinction)
and 01VT (the affine-base ample immersion argument) in literature/stacks-project/morphisms.tex.
The blueprint starts with Noetherian S and ends its proof with an embedding locally
on S. The already reviewed stage-1 node makes that local conclusion explicit.
Its natural statement is identical to the repository's current node: this delivery
has no new statement correction, and no statement_change record is needed.

Object/hypothesis/conclusion inventory and correspondence (all PASS):

1. Arbitrary schemes S, T and Y: `{S T Y : Scheme.{u}}`, with arbitrary bound
   universe u. Mathlib Scheme is the locally affine locally ringed space definition
   recorded by def-pc-scheme. No field or characteristic is fixed.
2. S Noetherian, explicitly quasi-compact and locally Noetherian:
   `[CompactSpace S] [IsLocallyNoetherian S]`. CompactSpace imposes no Hausdorff
   requirement. IsLocallyNoetherian requires Noetherian rings on affine opens;
   its affine-cover equivalence gives precisely pqf-def-locnoeth.
3. Named projective p:T -> S: `(p : T ⟶ S) [IsProjective p]`.
   I read IsHProjective.exists_closedImmersion and IsProjective in the project's
   Projective module: the latter extends the former and QuasiCompact. The former
   uses `ULift.{u} (Fin (n + 1))`, a closed immersion, and exactly the structural
   map equation. This is the global H-projective convention of the dependency,
   rather than the broader projective-bundle convention of Stacks 01W8.
4. Named finite h:Y -> T: `(h : Y ⟶ T) [IsFinite h]`. Mathlib IsFinite extends
   IsAffineHom and asks that every affine-open section map be finite. This matches
   def-weil-finite-integral-morphism; no surjectivity or flatness is imposed.
5. Every affine open U of S: `∀ (U : S.Opens), IsAffineOpen U → ...`.
   IsAffineOpen is IsAffine on the associated open subscheme. U is universally
   quantified before the embedding dimension and morphism, as required.
6. T_U and Y_U are inverse-image open subschemes. T_U is only used in the proof;
   Y_U in the conclusion is `((h ≫ p) ⁻¹ᵁ U).toScheme`. Composition has the correct
   order Y -> T -> S. No arbitrary replacement of the source occurs.
7. For each U there exist N >= 0 and an embedding into P^N_U:
   `∃ (N : ℕ) (i : ((h ≫ p) ⁻¹ᵁ U).toScheme ⟶
   ℙ(ULift.{u} (Fin (N + 1)); U.toScheme)), IsClosedImmersion i ∧ ...`.
   ProjectiveSpace is the recorded base change of integral polynomial Proj;
   its index counts homogeneous coordinates, so N+1 is correct. IsClosedImmersion
   is Mathlib's closed embedding with surjective maps on stalks, matching the
   closed-immersion dependency and its affine quotient characterization.
8. The embedding is over U: `i ≫ ℙ(...) ↘ U.toScheme = (h ≫ p) ∣_ U`.
   I read morphismRestrict in Mathlib Restrict.lean: it maps the indicated inverse
   image to U via the canonical pullback restriction isomorphism. ProjectiveSpace's
   canonical structural morphism is the first pullback projection. Thus this is
   precisely the equation over U, with no lost compatibility clause.
9. Thus Y_U -> U is projective: `IsProjective ((h ≫ p) ∣_ U)` is the second
   conjunct under each affine-open quantifier. It includes quasi-compactness as
   the node requires, in addition to the displayed embedding.
10. If S is affine, the original composite is projective:
    `IsAffine S → IsProjective (h ≫ p)` is the final conjunct. It asserts exactly
    the node's in-particular clause, without imposing global projectivity on an
    arbitrary base.

Edge cases: the empty base and empty affine open (the spectrum of the zero ring)
are allowed. Empty Y and T are not excluded by any Nonempty or Nontrivial instance;
empty sources embed into P^0. N=0 is present, with one homogeneous coordinate.
There is no unrelated empty index-set quantification: the projective coordinates
are necessarily indexed by Fin (N+1). No assumption of a field, characteristic,
reducedness, integrality, separated base, or surjectivity was introduced. The
single arbitrary scheme universe and ULift of the finite coordinate type match
both recorded projectivity and projective-space declarations and impose no test
universe restriction.

Independent H4 searches used different queries from the first reading:

- msearch leanfinder: "A finite morphism into a scheme with a projective embedding
  over an affine base has a projective embedding". Eight hits: Proj properness,
  universal closedness, finite type, quasi-compactness, Proj itself, separatedness
  and fromOfGlobalSections. None states the finite-cover embedding theorem.
- msearch loogle: `"IsFinite", "projective"`. The sole hit is
  MeasureTheory.IsProjectiveLimit.isFiniteMeasure, unrelated to schemes.
- msearch leansearch: "A scheme finite over a projective scheme over an affine
  Noetherian scheme admits a closed immersion into projective space".
  Service unavailable (Internal Server Error); no negative mathematical verdict
  is inferred from that outage.
- Independently searched Mathlib AlgebraicGeometry, the upstream WeilConjectures
  tree and project lean/Sheaf with `finite_over_projective`, `IsHProjective`,
  `IsProjective` and finite-cover/morphism phrases. Inspected the plausible hits:
  CoordinateCover.exists_isImmersion requires a supplied finite coordinate cover
  and concludes an immersion, not this theorem; CurveProjection and SerreDuality
  construct finite maps from curves to projective lines, the opposite direction.
  ProjectiveFiniteCohomologyPresentation is a cohomological presentation theorem,
  and FiniteProjectiveStandardFreeCover concerns modules. FiniteGenericCurveModel
  cites this item but does not supply its general statement. No exact existing
  theorem or duplicate full declaration name was found.

No new nodes or dependency modules are in this delivery. There is no private
notion or definition, hence no hollow data. The only theorem ends in `by sorry`;
nothing was proved. The module and declaration docstrings identify the source
and blueprint id; all six proof steps and their dependency names are present.
Public imports serve the signature and proof-only imports serve the recorded
proof dependencies. All source lines are at most 100 characters. All scheme
variables and the universe are explicitly bound; no local notation or instances
hide signature data. I mechanically checked the node's lean.statement is
verbatim the full signature in the file.

I also inspected two existing uses of the reviewed local correction:
lem-fin-generic-curve-model applies this over a field or after shrinking to an
affine open; lem-weil-pbc-normalization-projective-components applies it over
Spec(k). Both uses hold with the affine-base clause. No citer was edited.

Mismatches found: none in the statement, dependency notions, or proof docstring.
Changes: appended this independent reading only; retained the correct Lean and
node record verbatim. Validation is by scompile.py on the server only, nice 19,
two threads, 60 seconds per file; no local Lean or lake build was run.

Second-reader compile result: PASS, no errors or warnings. The private overlay
compiled RelativeProjData (3.3 s), RelativeProjExists (1.4 s), and
RelativeProjectiveSpace (2.5 s); FiniteOverProjective compiled in 1.4 s.
