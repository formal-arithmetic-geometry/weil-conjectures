## Worker report

This is an existing-declaration attachment, with no new Lean module and no new sorry.
The exact construction is `AlgebraicGeometry.Compactification.baseChange`, in
`WeilConjectures/Compactification/BaseChange.lean`, lines 140–148 of slopmaster2.
Read its full definition, its module and declaration docstrings, and the underlying
`ofIsPullback` construction (lines 88–104), including the actual data fields and proofs.
The node is unchanged except for `lean`.

Clause-by-clause correspondence:

- The node fixes an external scheme S and S-schemes. The construction works in the
  underlying scheme category, with all schemes in arbitrary universe u. For S-schemes,
  equip the ambient c.Z with structural map c.g followed by Y → S. The factorization
  equality makes c.i an S-morphism. The pullbacks inherit their S-structure by composition
  with Y′ → S. Thus the external base is retained without requiring separate choices in
  the construction. The source variable S in baseChange denotes the node’s Y, its T
  denotes Y′, and its t denotes g; it is not the external S of the node.
- The initial Cartesian square is rendered by `ofIsPullback (hsq : IsPullback h u p t)`.
  Here h = g′, u = f′, p = f, t = g. The dependency’s `ChosenCartesianSquare` extends
  CommSq and has `isoPullback`, `hom_fst`, and `hom_snd`, precisely the chosen Cartesian
  identification that realizes such a pullback square. No competing square is defined.
  The node subsequently chooses the literal fibre product X′ = X ×_Y Y′; this is exactly
  `baseChange`, obtained by calling `ofIsPullback (.of_hasPullback f t) c`.
- Separatedness and finite type are hypotheses of the node’s input situation. This
  existing construction needs only the given compactification and works for every such
  input, including separated finite-type f. There is no invented existence assertion or
  extra restriction on f. The finite-type assumption in particular ensures the open
  immersion is quasi-compact by Compactification.quasiCompact_openImmersion_iff.
- A compactification c = (j,p) is the existing `Compactification f`: c.Z is the ambient
  scheme, c.i is j, c.g is p, c.comm says f = c.i ≫ c.g, and its instance fields assert
  IsOpenImmersion c.i and IsProper c.g. There is no density requirement in either the
  node or this structure. Refinements and their category remain the dependency’s
  `Compactification.Refinement` and `Compactification.category`; none is redefined.
- The base-change morphism g is unrestricted: `(t : T ⟶ S)` has no flatness, finite-type,
  separatedness, or other predicate in either baseChange or ofIsPullback.
- The ambient fibre product Xbar′ is `(c.baseChange t).Z = pullback c.g t`, definitionally
  and by `baseChange_Z`. The source fibre product is `pullback f t` in its return type.
- The map bar-g′ is `pullback.fst c.g t`; p′ is `pullback.snd c.g t`, definitionally the
  g field and also stated by `baseChange_g`. The map g′ is `pullback.fst f t`.
- The map j′ is the concrete `pullback.lift (h ≫ c.i) u …` in ofIsPullback.
  `baseChange_i_fst` and `baseChange_i_snd` identify its two projections; no arbitrary
  open immersion is substituted. `isPullback_i_ofIsPullback` proves it is the base
  change of c.i, and `isPullback_g_ofIsPullback` supplies the proper projection square.
- The concluding compactification c′ of f′ is the return type
  `Compactification (pullback.snd f t)` (or `Compactification u` for the given square).
  The construction provides comm from pullback.lift_snd, properness by Mathlib’s
  pullback projection instance, and openness using stable-under-base-change applied
  to isPullback_of_isPullback. It therefore includes every asserted property of c′.

Dependency declarations inspected:

- `WeilConjectures.Compactification.Refinement`: AlgebraicGeometry.Compactification.Refinement
  and category; its imported Defs module provides the full Compactification structure.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: AlgebraicGeometry.ChosenCartesianSquare;
  read its complete structure and docstring. Its canonical inverse-image comparison is
  irrelevant to the compactification construction and is not duplicated here.
- def-weil-pbc-scheme-conventions has a convention-only record (no declaration to import).
  This attachment uses precisely its Scheme, IsProper, and IsOpenImmersion meanings.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: isOpenImmersion_stableUnderBaseChange and
  its IsOpenImmersion (pullback.snd f g) instance; read lines 590–610 and 835–850.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: IsProper.isStableUnderBaseChange and
  the IsProper (pullback.snd f g) instance; read lines 65–90. Both stability notions
  are used by the existing BaseChange construction.

Edge cases checked by reading the construction: empty schemes and empty open immersion
are allowed; g may be nonflat and need not be finite type or separated; the open immersion
need not be dense. In particular, base change to a boundary point can give empty X′ and
nonempty Xbar′, which remains a compactification in exactly the stated sense. Identity
base change yields the canonical fibre products, not an unjustified literal equality
with the original schemes. Universes are arbitrary, with no field, Noetherian, or
nonemptiness assumptions. No statement fault or correction was found.

Searches for an existing declaration (all msearch commands used the stage-2 sandbox root):

- msearch leansearch: "Base change of a compactification of a scheme morphism is a
  compactification"; service unavailable, Internal Server Error (recorded as unavailable).
- msearch leanfinder: "Base change of a compactification of a scheme morphism along an
  arbitrary morphism is a compactification"; eight hits, including IsProper stability and
  proper pullback projections; no compactification construction in Mathlib.
- msearch loogle: "AlgebraicGeometry.Compactification"; unknown identifier, zero hits.
- msearch grep, AlgebraicGeometry: "compactification|isOpenImmersion_stableUnderBaseChange";
  one hit for the open-immersion stability instance, no compactification definition.
- rg on upstream WeilConjectures/Compactification for pullback/baseChange and declaration
  names found BaseChange.lean: ofIsPullback and baseChange, with the exact construction.
- rg on upstream WeilConjectures for the item id had no hit; the notion nevertheless
  exists under the Nagata base-change names. dag/lean_names_upstream.json associates
  baseChange and ofIsPullback with def-nagata-compactification-base-change.
- rg on project lean/Sheaf for compactification and CompactSupportSquare found applications
  and specialized curve compactifications; no new general notion is needed.

Validation: the sandbox scratchpad/ExistingCheck.lean probes every recorded declaration
through scompile.py. deliver2.py --no-push repeats the server probes and checks the node
and report. The second reading is reserved for the independently dispatched reader.

## Second reading by NJ

Independently read the sandbox node, its exact blueprint source
(sec-smooth-purity/sk-prop-sf-cbc/def-cbc-compact-support-square.md), all five
statement-dependency nodes and their recorded declarations, and upstream
Compactification/Defs.lean, Refinement.lean and BaseChange.lean. The source is a
blueprint definition, not a Stacks statement with implicit section hypotheses.
Also read Stacks schemes.tex, lemma-base-change-immersion (01JY), and the
Mathlib open-immersion and proper base-change instances used by the construction.

Object/hypothesis/conclusion inventory, with independent verdicts:

- External scheme S and schemes over S: Scheme.{u}, with the structural morphism
  of c.Z given by c.g followed by Y → S. Its base-changed structural morphism
  factors through Y′. The equality c.comm and the pullback projection equations
  make every displayed arrow an S-morphism. Verdict: same objects; external
  S adds no datum to the construction. Upstream's S names the node's Y.
- Given Cartesian square (g′, f′, f, g): ofIsPullback takes precisely
  IsPullback h u p t, where h = g′, u = f′, p = f, t = g. The dependency
  ChosenCartesianSquare provides an isomorphism to pullback f g respecting both
  projections, hence the same Cartesian property. Its chosen isomorphism does
  not alter the induced lift, which is uniquely determined by the projections.
  Verdict: covers the initially given square as well as the literal pullback.
- f separated and finite type: this is the node's input situation. The existing
  construction is defined on any given Compactification f and specializes
  directly to that situation, without requiring an existence theorem or changing
  the meaning of compactification. Verdict: no extra restriction; the more
  general domain of an existing definition does not change its specified value.
- Input c = (j,p): Compactification f has Z, i, g, comm : f = i ≫ g,
  isOpenImmersion and isProper. Thus Z = Xbar, i = j, g = p. The dependency's
  Refinement and category use exactly these objects; properness of a refinement
  is derived from its commuting structure maps. Verdict: same notion, with no
  density condition or independent choice of ambient scheme.
- Arbitrary g : Y′ → Y: baseChange's t has no instance hypotheses; neither does
  ofIsPullback. Verdict: no flatness, characteristic, or finiteness restriction.
- Xbar′ = Xbar ×_Y Y′ and X′ = X ×_Y Y′: ofIsPullback.Z is pullback c.g t;
  baseChange returns Compactification (pullback.snd f t). Verdict: exact fibre
  products, not just an unrelated compactification of the same morphism.
- Projections bar-g′, p′ and g′: pullback.fst c.g t, pullback.snd c.g t and
  pullback.fst f t respectively. baseChange_Z and baseChange_g confirm the
  ambient scheme and proper map. Verdict: all named arrows accounted for.
- j′ is the base change of j: ofIsPullback.i is
  pullback.lift (h ≫ c.i) u with the equation coming from c.comm and hsq.w.
  isPullback_i_ofIsPullback establishes its Cartesian square; baseChange_i_fst
  and baseChange_i_snd give both required projection equalities. Verdict: exact
  induced morphism, not an arbitrary open immersion.
- c′ compactifies f′: ofIsPullback returns Compactification u, with comm from
  pullback.lift_snd, isProper from the proper pullback projection, and
  isOpenImmersion from stable-under-base-change applied to its Cartesian square.
  isPullback_g_ofIsPullback also identifies the proper projection square.
  Verdict: every property in the final clause is included.

Edge cases: empty X, Y′, or ambient schemes are allowed; the construction only
uses scheme pullbacks. In particular, a boundary-point base change can have
empty X′ and nonempty Xbar′, so adding density would have been wrong; neither
node nor declaration adds it. Identity base change gives canonically isomorphic
fibre products, without asserting literal equality to the original schemes.
No index, integer n, coefficient ring, field, or characteristic occurs.
Universe u is arbitrary for all schemes, including the external base, with no
extra size assumptions. No unbound variables were found in the source signature.

Independent H4 searches used different wording from the author:

- msearch leanfinder: “An open immersion followed by a proper scheme morphism
  remains such a factorization after forming fibre products”: eight hits,
  including the Mathlib open-immersion pullback projections, no compactification.
- msearch loogle: `"pullback", "IsProper"`: zero hits.
- msearch grep: `Compactification|compactif` in Mathlib/AlgebraicGeometry:
  zero hits. The author's unavailable LeanSearch attempt is recorded above.
- rg of upstream Compactification and project lean/Sheaf using
  `ofIsPullback`, `baseChange`, and compactification/base-change wording finds
  upstream BaseChange.lean's exact construction and its categorical extensions.
  The upstream name table associates it with the Nagata base-change node.
  No replacement module is needed: reusing baseChange avoids a duplicate notion.

No mismatch was found and no Lean or node field was changed. There are no new
nodes, dependency modules, statement corrections, new docstrings, proofs, or
hollow definitions to audit. The recorded lean.statement is verbatim the
baseChange signature before `:=` in the upstream file. All eight recorded
declarations were checked independently by compiling scratchpad/ExistingCheck.lean
with scompile.py: clean, 1.5 seconds, nice 19, two threads, 60-second limit.
The only change of this second reading is this report section.
