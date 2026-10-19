## Worker report

The delivery states `AlgebraicGeometry.Etale.exists_affineSpaceTopTrace` in
`Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`. All theorem proofs are `sorry`.
Every functor, adjunction, comparison and trace has real defining data; there is no
independently chosen trace, exchange, orientation, or arbitrary isomorphism used to
construct a map.

The affine space is represented by the coordinate tower `affineTraceTower S d`.
The new geometry module constructs its ordered coordinates and the actual morphism
`affineTraceToAffineSpace S d` into Mathlib's
`AffineSpace (ULift (Fin d)) S`. Its named isomorphism theorem determines the inverse
uniquely, so `affineTraceAffineSpaceIso` is a legitimate canonical construction.
The projection is the identity at zero and the composite of the coordinate projections
at each successor stage. Thus this representation includes the node's literal
identity convention at d=0 and represents its specified affine d-space.

Hypotheses and clauses are rendered as follows.

- The integer N≥1 is `(N : ℕ) (hN : 0 < N)`.
- The finite commutative ring with NA=0 is
  `(A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)`.
  For a unital ring, `(N : A)=0` is equivalent to N killing every element.
- The Noetherian base is `(S : Scheme.{u}) [IsNoetherian S]`;
  `IsNoetherian` is the finite affine Noetherian-cover condition, by Mathlib's
  `isNoetherian_iff_of_finite_affine_openCover`.
- Invertibility is `hS : IsUnit (N : Γ(S, ⊤))`. A natural number is a unit in the
  global ring precisely when it is locally a unit on this scheme. Its pullbacks are
  the named statements `affineTraceInvertible` and `affineTraceProjectiveInvertible`.
- The categories are the existing `DerivedCategoryModule A T`, hence the entire
  derived categories of ordinary small-etale module sheaves. No pro-etale site or
  completion is used; coefficient universe u+1 is the existing site's convention.
- The ordinary finite Tate line and its canonical pullback are reused through
  `OrdinaryFiniteTwistTransport`, `ordinaryFiniteP1Right`,
  `ordinaryFiniteP1RightBaseChange` and `Scheme.finiteEtaleTateSheaf`.
  `affineTraceRight` recursively tensors with one shifted line at every coordinate.
  The theorem expressly identifies this functor with inverse image, derived tensor
  with the finite Tate sheaf in degree d, and shift by 2d, as required by the node.
  The identification is an assertion, not a choice used to define the trace.
- For one coordinate `affineTraceLineCompactification` is the standard open chart
  into `ProjectiveLine S`, with its proper projection and actual factorization.
  `affineTraceLineLeft` is exactly the recorded unbounded
  `rightDerivedLowerShriekOfCompactification (ModuleCat A)` on this compactification.
- `affineTraceLineAdjunction` literally applies `Adjunction.comp` to the existing
  derived open adjunction and the normalized projective-line datum's adjunction.
  The exact-versus-left-derived inverse-image comparison is inserted canonically.
  The projective datum's decomposition and actual counit normalization fix its trace.
- `affineTraceLeft`, `affineTraceRight` and `affineTraceAdjunction` are the ordered
  coordinate composites. At zero their functors and adjunction are identity.
- `affineTraceLeftPlus` is the bounded-below version of that same tower.
  `affineTracePlusCompatibility` is its canonical restriction comparison with the
  unbounded tower. `affineTraceCompactSupportComparison` recursively uses the
  existing canonical compactification comparisons and `rightDerivedLowerShriekPlusCompIso`.
  Thus the comparison to Rp_d! uses the recorded coherent maps, not a bare existence.
  The main theorem explicitly asserts that its trace input is bounded below.
- `affineTraceCounit` is exactly `affineTraceAdjunction.counit.app (ordinaryFiniteUnit A S)`.
  The conclusion `IsIso (affineTraceCounit ...)` is the trace-isomorphism clause.
- Every Noetherian base change is quantified as
  `(S' : Scheme.{u}) [IsNoetherian S'] (g : S' ⟶ S)`.
  `affineTracePullbackInvertible N g hS` supplies the pulled-back invertibility;
  the conclusion imposes no additional hypothesis on g or on S'.
- `affineTraceLineExchange` is the existing compactification base-change map followed
  by the canonical comparison to the standard compactification on S'.
  `affineTraceExchange` pastes these maps along the ordered tower.
  By the coherent comparison and horizontal/vertical pasting in the recorded
  compact-support theorems, this is the node's compactification-independent C_{d,g}
  on the indicated bounded-below input.
- `affineTraceOpenPullbackSquare`, `affineTraceLineRightBaseChange` and
  `affineTraceRightBaseChange` use the actual inverse-image composition comparison,
  canonical chart square, tensor comparison, shifted-line roots-of-unity transport,
  and their coordinatewise composites. They are the canonical Tate identifications.
- The final equality starts with `affineTraceExchange`, then maps the canonical
  right-object and constant-object identifications through the changed-base left
  functor, and ends with `affineTraceCounit` on S'. The other side pulls back the
  original counit and applies `ordinaryFiniteUnitPullback`. In ordinary right-to-left
  composition notation this is precisely t_{p'_d} C_{d,g}=g* t_{p_d}.
  Both sides are actual morphisms with the same source and target.

The theorem existentially packages the normalized projective-line family already
provided by `lem-asd-ordinary-finite-p1-adjunction`, together with its base-change
normalization and the affine trace assertions. The normalization fixes the actual
counit: this is the stated explicit adjunction, not a hypothesis that an arbitrary
adjunction happens to have an invertible trace.

Dependency interfaces read and reused:

- Mathlib `AlgebraicGeometry.Scheme`, `AffineSpace`, its `homOfVector`, coordinates,
  maps, structure projections and affine-base polynomial description.
- `Sheaf.AlgebraicGeometry.DerivedCategories`, with the source
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients.DerivedCategoryModule`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback.Scheme.etaleFiniteTwistPullback`
  and its concrete finite Tate sheaves, through the normalized ordinary P1 arrows.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification` and its D+ compatibility.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data`:
  `OrdinaryFiniteP1Datum`, its `.adjunction`, `.trace`, `.counit_normalization`,
  `OrdinaryFiniteP1BaseChange`; its public arrows supply all normalized tensor,
  inverse-image, shifted-line and constant-object maps.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons` and its existing upstream
  `rightDerivedLowerShriekOfCompactificationPlusIso`,
  `rightDerivedLowerShriekPlusId`, `rightDerivedLowerShriekPlusCompIso`.
- Mathlib `CategoryTheory.Adjunction.comp`, `Adjunction.id`; their actual formulas
  were read in `Mathlib.CategoryTheory.Adjunction.Basic`.
- `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion.compactSupportFiniteTorsion`
  and its canonical coherence/pasting interface, with the actual unbounded
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap` and its comparison.
- The ordinary derived open and closed adjunctions in the dependency module below.

Edge cases checked: d=0 (literal identity adjunction, trace and exchange), d=1
(the actual open/projective composite), N=1 and the zero coefficient ring (all
coefficient objects are zero), empty base, disconnected or nonreduced Noetherian
base, arbitrary g including identity, isomorphisms and non-flat g, and no
constructibility or boundedness restriction on the categories themselves.
The only boundedness assertion concerns the indicated shifted Tate trace input.

Searches: msearch LeanFinder `compact support affine space trace counit isomorphism
etale cohomology` returned eight unrelated counit/affine-spectrum hits;
Loogle `"trace", "AffineSpace"` returned zero hits; Mathlib grep
`affine.*trace|affine.*counit` in AlgebraicGeometry returned zero hits.
LeanSearch `affine space compactly supported trace etale derived adjunction`
was unavailable (Internal Server Error), recorded without claiming a mathematical
verdict. Further tower searches and their exact responses are in the new node.
Ripgrep of upstream for the item ID found no declaration; affine/trace searches
of the side library found only unrelated algebraic trace-discriminant declarations.
The blueprint search found no coordinate-tower node; the DAG mentions this tower
only in the item and downstream purity assertions.

Compilation uses scompile.py only. The normalized projective-line theorem and other already-stated proof
dependencies are imported for stage 3. An initial stale local `ProjectionMateExact`
overlay had an incorrect KFlat universe arity; the wrapper confirmed against the
current server sources. No live library or tool file was modified. All temporary diagnostics
are inside this sandbox and will not be delivered.

The final three-module scompile.py invocation succeeds without warnings against
the current server sources: geometry 2.3 seconds, open/closed adjunctions 2.6 seconds,
and the complete main module with proof imports 7.2 seconds. The recursive Tate
comparison uses an explicit one-coordinate pasting step to keep kernel checking
within the unchanged 60-second limit. The prescribed deliver2.py --no-push checks
the whole delivery and its existing-declaration probes; the second reader supplies
the second-reading section and performs delivery.

No statement correction and no STATEMENT-DISPUTED issue is needed. The existing
finite-invertible-coefficient statement is preserved verbatim.

Worker continuation, 2026-10-16: re-read the current item and every statement
prerequisite, the ordinary finite P1 datum and adjunction, the actual compact-support
and inverse-image comparisons, and the upstream pro-etale adjunction interfaces.
Read the detailed blueprint source and its unit on the project server. The earlier
construction still matches the source. The recollement node uses ordinary derived
categories on pro-etale sites in its dependency context and proof; its ordinary-etale
helper supplies the specialization needed here. No Lean statement or defining data
was changed. Repeated LeanFinder, Loogle and focused Mathlib grep found no existing
affine-space counit-trace statement; upstream and side-library searches likewise
found no duplicate. Refreshed the delivered theorem and existing trace record signatures to preserve
the source files' actual whitespace. The inherited second-reading section is retained as
prior review evidence; this continuation is the worker check for the next reader.

Current worker validation: the three-file `scompile.py` invocation succeeded on
the server, without errors or warnings. File times were 2.4 seconds (tower),
2.6 seconds (recollement), and 8.0 seconds (main statement), each under the unchanged
60-second limit. The wrapper used server confirmation after its local published
`OrdinaryFiniteP1Kummer` overlay timed out. No delivered Lean source required a change.

## New nodes

`def-amb-affine-trace-tower` specifies the ordered coordinate model, projection,
coordinatewise change of base, its concrete coordinate map to the existing affine
space, the standard projective-line compactification and its Cartesian chart
square, finite type/separatedness/Noetherianity, and pullback of N-invertibility.
Its source is sk-prop-an Steps 5(b) and 6, the very coordinate tower required by this
item. The independent components already exist in Mathlib/upstream and are reused;
no node or declaration packages their tower or its chart-square interface. Searches
use LeanSearch (service unavailable), LeanFinder (only unrelated projective elliptic
curve maps and the individual affine map coordinate lemma), Loogle (no interface),
Mathlib grep (no tower), and upstream/side/DAG grep (only the prescribed source and
its downstream references). Every postponed geometric property has a named theorem
and a full proof docstring; the coordinate morphism and all defining data are real.

## Dependency modules

`prop-weil-open-closed-recollement-adjunctions` had no Lean declaration. The supplied
module reuses the exact existing ordinary derived open and closed adjunctions and
states invertibility of their actual open unit and closed counit. The second reading below supplies the pro-etale declaration required by this
dependency node as well, while retaining the ordinary-etale helper used by the item.

`def-amb-p1-trace` had no Lean record, but the existing
`OrdinaryFiniteP1Datum.trace` already is decomposition inverse followed by the second
projection. The same datum gives trace_chern and the actual counit's ordered
projection equation. Invertibility of that projection is the recorded proper
projection formula, making this exactly the inverse-projection, tensor-trace and
unit-constraint formula required by the node. Its lean-only repair records these
existing declarations; no second trace or module is introduced.

## Earlier second reading (a previous round; superseded)

I reread the node statement, its source-step proof, all three delivered modules, and
the cited dependency records. The item-by-item rendering is:

- `N ≥ 1` is `(N : ℕ) (hN : 0 < N)`; verdict: exact.
- `A` finite commutative with `NA = 0` is `(A : Type (u + 1)) [CommRing A]
  [Finite A] (hA : (N : A) = 0)`; verdict: exact, including the stated coefficient
  universe.
- `S` Noetherian and `N` invertible are `(S : Scheme.{u}) [IsNoetherian S]`
  and `(hS : IsUnit (N : Γ(S, ⊤)))`; verdict: exact.
- The ordinary derived categories are `DerivedCategoryModule A T`; verdict: exact
  ordinary small-etale module-sheaf encoding.
- The normalized finite Tate data are the existential `t`, `D`, and
  `OrdinaryFiniteP1BaseChange A N hA t D`; verdict: this supplies the explicit
  normalized projective-line family required by the node.
- The coordinate affine space and projection are rendered by
  `affineTraceTower S d` and `affineTraceProjection S d`, with
  `affineTraceToAffineSpace_isIso` identifying the tower with Mathlib's
  `AffineSpace (ULift (Fin d)) S`; verdict: canonical representation of the node's
  `\mathbf A^d_S`, including the identity at `d = 0`.
- The right adjoint and Tate/shift identification are `affineTraceRight` and the
  displayed `Nonempty` isomorphism to `derivedTensorRight` followed by
  `shiftFunctor`; verdict: every right-adjoint clause and its `d`-fold Tate twist
  and `2d` shift are present.
- The bounded-below compact-support comparison is
  `affineTraceCompactSupportComparison` together with
  `affineTracePlusCompatibility`; verdict: the required coherent `Rp_{d!}`
  identification is present.
- The trace is the actual counit
  `affineTraceCounit ... = (affineTraceAdjunction ...).counit.app
  (ordinaryFiniteUnit A S)` and `IsIso` is asserted; verdict: exact actual-counit
  isomorphism clause.
- For every `(S' : Scheme.{u}) [IsNoetherian S'] (g : S' ⟶ S)`, the theorem gives
  `affineTraceExchange`, the canonical right-object/base-change comparisons, and the
  displayed equality of actual morphisms; verdict: exact arbitrary-Noetherian-base
  change compatibility, with no flatness or extra hypothesis.

Edge cases checked independently: `d = 0` gives literal identity functors and
identity trace; `d = 1` is the standard affine/projective-line compactification;
`N = 1`, zero coefficients, empty or disconnected/nonreduced Noetherian bases, and
identity, isomorphic, flat, and non-flat base maps all remain within the binders.
No index nonemptiness, characteristic, constructibility, or global boundedness was
silently added.

The existing-definition searches were rechecked with `rg` over Mathlib,
`WeilConjectures/`, and `lean/Sheaf`, plus the recorded LeanFinder/Loogle searches.
They found no affine-space compact-support trace statement or coordinate-tower
declaration; the only matches are Mathlib's `AffineSpace` and unrelated trace maps.
The new `def-amb-affine-trace-tower` module supplies the missing canonical tower,
coordinate map, chart compactification, pullback square, and real geometric data;
its statements and source steps match its node.

One mismatch was found and repaired. The recorded dependency
`prop-weil-open-closed-recollement-adjunctions` explicitly describes pro-etale
ambient derived categories, but the worker's dependency module recorded only an
ordinary-etale specialization. I added
`AlgebraicGeometry.ProEtale.proEtaleOpenClosedAdjunctions` with the exact pro-etale
open-unit and closed-counit interface, imports for the published pro-etale
adjunctions, and a proof docstring; the ordinary-etale helper used by this item
remains in the same module. The dependency node's `lean` record now points to the
exact pro-etale declaration and records this repair. No item statement or
target-unit statement was changed.

The source blueprint file and its unit `_section.md` were read on the project
server: the node's ordinary-etale notation and Steps 5(b), 6 give exactly the
restricted projective-line trace and ordered coordinate induction used here.
The dependency's pro-etale proof and its six source steps were also read. The
current side-library versions of the pro-etale adjunction declarations and
`coord/pefw-upstream-framework.md` were checked; these finite constant-coefficient
sheaf adjunctions use the fixed-scalar presentation, with no condensed coefficient
or completed derived category substituted.

Independent searches by this reader used LeanFinder query
`compactly supported derived pushforward affine d space Tate orientation counit`
(eight unrelated Riesz/Haar integration results), Loogle query
`AlgebraicGeometry.AffineSpace, CategoryTheory.Adjunction` (zero hits), and `rg`
with `affine.{0,35}(counit|integration|orientation|trace)|coordinate.{0,15}tower`
over Mathlib, upstream, and the side library. The upstream
`affineLineOrientation` and `isIso_affineLineOrientation` were opened: they concern
the zero section's supported Kummer orientation and require a normalized Kummer
datum, so they do not state this node's compact-support projection counit.
The scalar P1 datum was read directly: `trace` is literally
`decomposition.inv ≫ biprod.snd`, and `counit_normalization` is precisely the
projection-formula equation. No further definition module is needed for that
dependency. All definitions have real data; the only postponed proofs are named
theorems recorded on their owning DAG nodes.

Second-reading validation: the repaired dependency compiled cleanly through
`scompile.py`. The final delivery wrapper attempted all three modules plus the
existing-declaration probe. Its local check timed out in the published
`OrdinaryFiniteP1Kummer` overlay dependency, so the wrapper used its prescribed
server confirmation; that confirmation passed without warnings. The record
signatures match the files and all delivered Lean lines meet the width limit.


## Second reading by Q24

Independent second reading of the current delivery, 2026-10-16. I opened the
item node, all three sandbox modules, every statement-dependency record and the
relevant declaration signatures and defining data. I read the blueprint source
lemma and sk-prop-an Steps 5(b) and 6 on the server. The source calls for the
ordinary-etale affine compact-support counit, first by the standard open in P1
and then by the ordered coordinate tower. Stacks etale-cohomology.tex,
lemma-kummer-sequence, explicitly requires N invertible. I also read
sites-modules.tex, lemma-extension-by-zero and lemma-extension-by-zero-exact,
and proetale.tex, lemma-closed-immersion and lemma-open-immersion, for the
additional dependency module. Those open/closed adjunction statements need no
quasi-compactness assumption; that assumption belongs to the separate
localization short exact sequence.

The node's objects, hypotheses and conclusion clauses, matched individually:

- Positive integer N: `(N : ℕ) (hN : 0 < N)`. Exact; N=0 is excluded by the node.
- Finite commutative coefficient ring annihilated by N:
  `(A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)`.
  Exact: multiplication by N kills every element precisely when the cast of N
  vanishes in a unital ring. No field, nonzero-ring or prime hypothesis occurs.
- Noetherian base S with N invertible: `(S : Scheme.{u}) [IsNoetherian S]`
  and `(hS : IsUnit (N : Γ(S, ⊤)))`. Exact. Mathlib Noetherianity is equivalent
  to the node's finite affine Noetherian cover condition; global invertibility
  of this integer agrees with its invertibility in all stalks.
- Ordinary unbounded categories: `DerivedCategoryModule A T`, whose opened
  definition is `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat A))`.
  Exact; it is neither a constructible subcategory nor a completed category.
- Finite Tate sheaves and tensor twist: the displayed right-functor isomorphism
  uses `Scheme.finiteEtaleTateSheaf A N ... hA (d : ℤ)`, its degree-zero
  `singleFunctor`, `derivedTensorRight`, and `shiftFunctor _ (2 * (d : ℤ))`.
  Exact. I read `etaleFiniteTwistPullback` and `OrdinaryFiniteTwistTransport`:
  the root comparison is fixed by its inclusion in the units sheaf and the
  coefficient comparison by pure tensors, so no orientation is freely chosen.
- Nonnegative dimension and affine projection: `(d : ℕ)`,
  `affineTraceTower S d` and `affineTraceProjection S d`. Exact representation:
  the concrete `affineTraceToAffineSpace` sends each polynomial generator to
  its ordered coordinate, and its named IsIso theorem identifies it with the
  recorded `AffineSpace (ULift (Fin d)) S`. Its inverse is uniquely determined.
- Specified one-dimensional compactification and adjunction:
  `affineTraceLineCompactification S` has actual open `ProjectiveLine.affineChart S`
  and proper structural projection. `affineTraceLineAdjunction` is the existing
  derived open adjunction, transported by the canonical exact/left-derived
  comparison, composed with `D.adjunction`. Exact, in the prescribed order.
- Prescribed projective trace: `OrdinaryFiniteP1Datum.trace` is literally
  `decomposition.inv ≫ biprod.snd`; its `counit_normalization` is the ordered
  proper-projection equation. I read those definitions and the projection map.
  Inverting that projection yields precisely the node's counit formula.
  The initial existentials t,D and `OrdinaryFiniteP1BaseChange` reuse the
  already-stated normalized P1 existence theorem and supply the required family.
- Ordered composite adjunction: `affineTraceLeft`, `affineTraceRight`, and
  `affineTraceAdjunction` recurse along the coordinate projections using
  `Adjunction.comp`. Exact; I read its actual counit formula and `Adjunction.id`.
- Right adjoint p* followed by twist d and shift 2d: the first `Nonempty`
  natural-isomorphism conjunct identifies the explicitly constructed right
  functor with exactly that composite on every object. Exact; this asserted
  comparison is not used as a choice to construct the trace.
- Bounded-below comparison with Rp_d!: `affineTraceCompactSupportComparison`
  recursively uses the existing canonical compactification comparison and
  `rightDerivedLowerShriekPlusCompIso`; `affineTracePlusCompatibility` identifies
  the ambient restriction. The next conjunct explicitly asserts that the
  constant object's right-adjoint image lies in `TStructure.t.plus`. Exact;
  no boundedness hypothesis is imposed on the ambient adjunction categories.
- Actual trace and its isomorphy: `affineTraceCounit` is defined by
  `(affineTraceAdjunction ...).counit.app (ordinaryFiniteUnit A S)` and the theorem
  asserts `IsIso` of that very map. Exact; no replacement isomorphism is chosen.
- Every Noetherian change of base: `∀ (S' : Scheme.{u}) [IsNoetherian S']
  (g : S' ⟶ S)`. Exact, with pulled-back invertibility supplied by
  `affineTracePullbackInvertible`; there is no condition on g.
- Specified exchange: `affineTraceLineExchange` uses the actual proper/open
  compactification base-change map followed by the canonical comparison to
  the new standard compactification. `affineTraceExchange` pastes these maps.
  Exact under the existing bounded-below comparison and vertical-pasting
  interface of `compactSupportFiniteTorsion`; no arbitrary exchange is supplied.
- Equality of actual maps under canonical Tate identifications: the final
  equality composes exchange, the changed-base left functor applied to
  `affineTraceRightBaseChange` and the constant-object comparison, and the
  new counit. Its other side is the pullback of the old counit followed by
  `ordinaryFiniteUnitPullback`. Exact rendering of t' C = g* t with both
  sources and targets explicitly identified. Quantifier order is unchanged.

Edge cases: d=0 has the literal identity tower, functors and adjunction; its
trace and exchange are identities. At d=1 the left and right functors have
only harmless identity-composition factors and give the specified open/P1
adjunction. N=1 forces the zero coefficient ring, which is permitted; the
zero ring for any N, the empty base, and disconnected or nonreduced bases
are also permitted. Arbitrary base maps include identity, isomorphisms,
empty-source maps and non-flat maps. No characteristic or constructibility
restriction was added. The single universe u is arbitrary; coefficient size
u+1 is the recorded small-etale module-category convention and imposes no
additional equality between site object and morphism universes. There is no
independent index set or hidden nonemptiness hypothesis. `autoImplicit false`
is set in every delivered module and all variables/universes are bound.

New-node reading (H12): `def-amb-affine-trace-tower` states the ordered
construction explicitly required by the source's Step 6, with the chart of
Step 5(b), and reuses Mathlib affine space and the existing projective line.
Its projection, coordinate maps, coordinate isomorphism, Cartesian chart square,
Noetherianity, finite-type/separatedness and invertibility properties each match
the declarations in AffineTraceTower. All data are real. The named postponed
geometric theorems have proof docstrings and are listed on this node; the IsIso
proof determines the inverse uniquely. The fields have the required chapter,
unit, ancestry, created record, empty proof/proof_deps, null mathlib_match,
none audits and complete Lean record. DAG searches found references to the
coordinate tower in this item and its consumers, but no separate definition node.

Dependency reading (H13): the open/closed node's dependency context and proof
specify pro-etale ordinary derived categories. The delivered
`ProEtale.proEtaleOpenClosedAdjunctions` states exactly its actual open-unit and
closed-counit invertibility. I opened the pro-etale adjunction definitions in
the shared source and checked their coefficient hypotheses against ModuleCat A;
the ordinary-etale helper used in this item is separately present. Thus the
prior round's repair remains correct. The trace dependency uses the existing
normalized P1 datum with `existing: true`; I verified its full trace signature,
its data and its normalization rather than relying on the record's name.

Independent searches (H4): LeanFinder query `Integration trace of affine space
with finite etale coefficients from the composite open and projective line
adjunction` returned eight affine-space/integral and etale-algebra results,
none this trace. Loogle `"AffineSpace", "counit"` returned zero hits. Mathlib
grep `affine.{0,40}(shriek|trace|counit)|coordinate.{0,20}tower` returned zero
hits. I searched upstream, lean/Sheaf and dag/lean_names_upstream.json by the
new names and by integration/orientation/trace and tower synonyms. The upstream
`affineLineOrientation` and its IsIso theorem were opened: their map is the
zero-section supported Kummer class into Rs!, not this compact-support counit.
Other side-library matches concern affine module tensor comparisons.
For the new notion, LeanFinder `Iterating affine line bundles gives affine n
space with ordered polynomial coordinates and standard projective charts`
returned eight existing affine-space components, which are reused here.
Qualified Loogle `AlgebraicGeometry.AffineSpace.map` returned the existing
single-stage map and its projection-square/coordinate lemmas, not this tower
or its projective-chart square. The earlier LeanSearch service failure remains
recorded as unavailable, never as evidence of absence.

Mismatch found and repaired in this reading: the new definition node gave a
no-match verdict to an invalid unqualified Loogle query whose response said
unknown identifier. I corrected that verdict to explicitly exclude it as search
evidence, and added the successful qualified Loogle and independent LeanFinder
queries with their actual results. The Lean and mathematical statements needed
no new change. No statement_change or unit-statement correction is involved.
Every theorem proof remains sorry, every definition has real data, docstrings
carry the appropriate source and blueprint ID, and the main docstring follows
all nine proof steps. Every lean.statement is verbatim present in its source;
all delivered Lean lines are at most 100 characters.

Current second-reader validation: the prescribed three-file scompile.py run
completed successfully on the local side overlay with exit 0 and no warnings
or errors. The wrapper retained its unchanged per-file 60-second compiler
limit; displayed total times include compiler-slot acquisition. No Lean file
was changed after this compile. Delivery preflight also checks the existing
trace declaration record.

The second-reader deliver2.py --no-push run printed OK: the complete package
compiled and passed server preflight. Its temporary dry-run commit was
3d7c18c5bc. The wrapper preserved the newer maintainer-owned reviewed_lean
metadata on the open/closed dependency; this delivery changes only its Lean
record.


Concurrent dependency landing checked before delivery: the refreshed base now records
`WeilConjectures.openClosedRecollement_adjunctions` from
`Sheaf.Paper.OpenClosedRecollementAdjunctions` (N8). I opened the complete module.
Its coefficient ring is `Padic.coefficientExtensionRing l E (n + 1)` and it
requires a prime l, a finite-dimensional p-adic field E, and invertibility of l
in the residue fields of the schemes. It uses pro-etale ring-sheaf modules.
These are not the arbitrary finite commutative coefficients of this item;
for example, a product ring with distinct nonzero residue characteristics is
not such a p-adic quotient. It also supplies no ordinary-etale helper. Thus its
interface cannot replace the delivered dependency interface for this consumer.
The generic finite-constant-coefficient words of the dependency node are still
rendered by the supplied pro-etale fixed-scalar theorem, with the ordinary-etale
specialization used above. I updated lean.note to identify the current unusable
record precisely, rather than retaining the earlier historical explanation.
I interrupted the first push-wrapper run before it could push its old repair
note. No Lean source or mathematical statement changed; the successful compile
and dry-run results above still apply, and the final delivery reruns all checks.
