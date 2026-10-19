## Worker report

The module Sheaf.AlgebraicGeometry.CompletedLocalBaseChange states
AlgebraicGeometry.Scheme.completedLocalBaseChange, with its only theorem proof
left as `sorry`. Four auxiliary declarations construct the canonical base
morphism, its actual fibre product, the local stalk map, and the scalar map.
Their data are explicit composites of existing Mathlib constructions, with no
postponed well-definedness proofs or arbitrary choices of maps.
The node changes only in `lean`. No statement correction, new nodes, dependency
repairs, or mathematical dispute is needed.

Hypothesis and conclusion audit against the node:

- Schemes X and S are `{X S : Scheme.{u}}`, and local Noetherianity of S is
  `[IsLocallyNoetherian S]`. There is no global Noetherianity, separatedness,
  properness, flatness, or G-ring assumption.
- The given morphism is `(f : X ⟶ S)` with `[LocallyOfFiniteType f]`; no
  quasi-compactness is required.
- The point s is `(s : S)`, the point x is `(x : X)`, and lying over s is
  `(hxs : f x = s)`.
- A is `S.presheaf.stalk s`, with its canonical local ring structure. Its
  maximal-ideal completion is exactly
  `AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
  (S.presheaf.stalk s)`.
- `S.completionBaseMap s` is Spec of the canonical algebra map from A to its
  completion, composed with `S.fromSpecStalk s`.
- `f.completionBaseChange s` is an abbreviation for
  `pullback f (S.completionBaseMap s)`, so its projections are the actual
  `pullback.fst` and `pullback.snd`.
- The closed point b is `IsLocalRing.closedPoint` of the completed base. Its
  local ring instance follows from Mathlib completion localness and the
  Noetherianity of the base stalk, both inferred from the stated assumptions.
- Existence is `∃ z`, followed by a proof `hx` that the first projection is x,
  and the equality that the second projection is b. Uniqueness quantifies
  over every `w` with these same two equalities and concludes `w = z`.
  In particular, uniqueness is not incorrectly asserted over x alone.
- The isomorphism is a `RingEquiv` between the actual maximal-ideal
  `AdicCompletion`s of `X.presheaf.stalk x` and the base-changed stalk at z.
- The canonical local map is `f.completionBaseChangeLocalMap s x z hx`:
  stalk transport along `hx.symm`, then the first projection's stalk map.
  For every n, every completed element t and every representative a of its
  nth component, the first formula says that the nth component of `e t`
  is the quotient class of the canonical local image of a. This determines
  exactly the map induced on inverse limits, rather than an arbitrary ring
  equivalence merely extending the map on a dense subset.
- The existential ring map α is the canonical completed-base action on the
  original completed stalk. Its all-level formula determines it uniquely
  as the completion of the base stalk map, transported using `hxs.symm`.
  It is constructed in the conclusion, never assumed as additional input.
- The final equation `e (α t) = algebraMap _ _
  (f.completionBaseChangeScalarMap s z t)` asserts preservation of every
  scalar in the completed base. On the right, the scalar map is the
  structure-sheaf map to the stalk on Spec of the completed base followed
  by the second projection's stalk map, then the completion inclusion.
  A ring equivalence preserving these scalar maps is exactly an algebra
  equivalence for the corresponding canonical completed-base algebras.
  Thus this clause explicitly retains the node's completed-base linearity.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType:
  AlgebraicGeometry.LocallyOfFiniteType, not the stronger finite-type condition.
- Mathlib.RingTheory.AdicCompletion.Basic and Algebra: AdicCompletion,
  its CommRing and Algebra instances, AdicCompletion.evalₐ, and algebraMap.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  CategoryTheory.Limits.pullback, pullback.fst, pullback.snd, with the scheme
  pullback instance supplied through Mathlib.AlgebraicGeometry.PullbackCarrier.
- Mathlib.AlgebraicGeometry.Noetherian:
  AlgebraicGeometry.IsLocallyNoetherian and its Noetherian stalk instance.
- Mathlib.AlgebraicGeometry.PullbackCarrier:
  AlgebraicGeometry.Scheme.Pullback.carrierEquiv and its two projection lemmas;
  these furnish the point part of the recorded proof.
- WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField:
  AlgebraicGeometry.Scheme.Pullback.exists_residueField_equiv_ofPointTensor.
  The current complete declaration/docstring was read with `scompile.py --source`;
  it is imported as a proof dependency because the signature uses only stalks.
- Mathlib.AlgebraicGeometry.Stalk: Scheme.fromSpecStalk; Scheme.stalkMap and
  stalkCongr are the actual structure-sheaf constructions. StructureSheaf.toStalk
  gives the scalar map with no auxiliary affine chart.

The available recorded proof modules are imported: the residue-field module,
WeilConjectures.RingTheory.AdicCompletionNoetherian,
Sheaf.RingTheory.FiniteTypeBaseChangeAdicQuotients,
Mathlib.RingTheory.AdicCompletion.LocalRing, and
Mathlib.RingTheory.AdicCompletion.AsTensorProduct (flat_of_isNoetherian).
The inverse-limit proof node has no recorded module, so no invented import
was added for it. It remains cited in the theorem's complete proof docstring.
No unstated dependency is needed to type the statement itself.

Source check: the local Stacks source at more-morphisms.tex,
lemma-relative-map-approximation-pre (0GDX), first proof paragraph, explicitly
introduces the completed-base fibre product and distinguished point. The
completed-local comparison is the affine quotient/localization calculation
recorded in the node, using algebra.tex lemma-completion-tensor (00MA), part 3,
and the finite-level comparison and inverse-limit proof nodes. Tag 0GDX's
input completed-local isomorphism is not used as a proof of this theorem.

Edge cases: the empty scheme X has no x, and the empty S has no s; there is
no added nonemptiness premise. A field stalk has zero maximal ideal, so its
completion and closed point are covered. Nonclosed x over s and residue
fields transcendental over κ(s) remain allowed; no closedness of x or finite
residue extension is assumed. Arbitrary characteristic and nilpotents are
allowed. The quotient characterization includes n = 0, where the quotient
by the unit ideal is the zero ring and the implication is valid; positive
n give the genuine adic components. All schemes and their stalk/completion
rings use the same arbitrary universe u; no test-object quantifier is
vacuous and no equality of distinct site universes is imposed.

Searches, before writing (raw service results are in sandbox searches.jsonl):

- msearch.py leanfinder: "completed local rings are unchanged by base change
  to the completion of a locally noetherian base" returned finite-module
  completion/tensor statements and stability of ring-map properties; no
  geometric completed-stalk theorem.
- msearch.py leansearch: "completed local ring base change completion
  noetherian scheme" returned AdicCompletion.flat_of_isNoetherian,
  liftRingHom, finite-module tensor/completion comparisons and Noetherian
  spectrum facts; none says this node's statement.
- msearch.py loogle: "AdicCompletion.map, Scheme.Hom.stalkMap" returned no hits
  with an unknown identifier notice for the shorthand Scheme.Hom.stalkMap.
  This query is not treated as evidence of absence. The subsequent query
  "AdicCompletion" checks the actual completion name separately.
- msearch.py grep, directory AlgebraicGeometry:
  "completed.*local.*ring|completion.*base.change" returned zero hits.
- rg of project lean/Sheaf and upstream WeilConjectures for
  "completed.*local|CompletedLocal|completion.*base.change" found existing
  completion-related modules but no statement of the present comparison.
  In particular FlatLocalCompletionIso is a ring-theoretic theorem about
  flat local maps with an extra extended-maximal-ideal equality, not this
  scheme theorem or its canonical completed-base compatibility.
- rg for the exact node id in upstream WeilConjectures found no declaration.
  rg for each chosen helper/declaration name in Mathlib, WeilConjectures,
  and lean/Sheaf found no name conflict; dag/lean_names_upstream.json was
  searched for the completed-base names as well.

Validation: the prescribed scompile.py compiled the module separately both
as a sandbox file and at its library path in about two seconds each, cleanly.
The initial namespace lookup error was repaired by placing morphism helpers
under Scheme.Hom; the final file has no errors or warnings. Every universe
and variable is explicit, with autoImplicit and relaxedAutoImplicit disabled.

## Second reading by Q124

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
