## Worker report

The module `Sheaf.AlgebraicGeometry.HilbertUniformSectionBound` states
`AlgebraicGeometry.HilbertSectionBound.exists_uniform_bound`, with one `sorry` and no
proved theorem. Sixteen concrete helper definitions supply the actual ideal and closed
family twists, their direct images, the polynomial module and its monomial map, the
canonical section arrows, twist multiplication, and evaluation. No definition takes
its data from a postponed existence proof.

The previous worker's stale-assignment diagnosis confused stages: the ledger's N9 PASS
at 04:39 UTC on 2026-10-22 is the stage-1 split. The live node had no `lean` record or
`reviewed_lean`, so its stage-2 statement remained to be delivered. This delivery does
not re-split or change the reviewed mathematical statement.

Hypotheses, objects and clauses, matched individually:

- The fixed projective dimension is `n : ℕ`; the homogeneous coordinates are
  `ULift.{u} (Fin (n + 1))`, including n=0.
- `P : Polynomial ℚ` and `hP` express exactly eventual integer-valuedness: some natural
  N works for every natural d >= N, with `P.eval (d : ℚ) = (z : ℚ)` for an integer z.
  Eventually large natural integers are exactly the sufficiently large integers in the
  node. No positivity, degree bound or realizability assumption is added.
- `∃ m : ℕ, 1 ≤ m ∧ ∀ (T Z : Scheme.{u}) ...` puts the bound before every base and
  family, so it depends only on n and P. A positive integer bound and all integer
  d >= m are equivalently represented by natural m and d with these inequalities.
- The ambient scheme is the already existing `ℙ(ULift (Fin (n + 1)); T)` and its
  projection is the existing first projection. The recorded definition
  `def-nagata-projective-space-base-change` explicitly identifies this with the same
  relative projective space of `def-nagata-relative-projective-space`. We use this
  existing standard realization, also used by the node's projective cohomology and
  Hilbert-polynomial interfaces. This introduces no alternate ambient hypothesis or
  arbitrary projective-space isomorphism. `RelativeProjectiveSpace.monomials` supplies
  the existing ordered homogeneous monomial index set.
- `i : Z ⟶ ℙ(...)` and `IsClosedImmersion i` are the given closed immersion.
- `Flat (i ≫ projection T n)` is flatness of Z over T.
- `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated` of that same
  composite are each retained separately, exactly as in the node's parenthetical.
- The fibre hypothesis uses `ProjectiveHilbertPolynomial.IsCoordinatePolynomial`
  on `baseChangeEmbedding n i (geometricPoint T t)` for every point t. The geometric
  point is the spectrum of the actual algebraic closure of the residue field. The
  recorded predicate is the eventual homogeneous-coordinate dimension of the actual
  quotient by equations vanishing on all projective charts, not a choice of polynomial
  and not an imposed Euler-characteristic assertion. All geometric extensions have
  the same coordinate dimensions, so checking these chosen algebraic closures is the
  fibre-polynomial condition on every geometric fibre.
- `i.ker.toModules` is the actual quasi-coherent ideal of the closed immersion, with
  its canonical inclusion `i.ker.toModulesι`. The module construction realizes its
  ideal as the kernel of the structure-sheaf restriction. The canonical closed-scheme
  presentation of the ideal is isomorphic to the given closed immersion.
- `twist T n d` is the existing `ProjectiveSpace.twist`, itself the pullback of the
  recorded `Proj.twist`. `idealTwist i d` is I tensor O(d), and `closedTwist i d` is
  the recorded tensor pullback of O(d) to Z. `idealSections` and `closedSections` are
  the two specified direct images, along p and i;p respectively.
- `polynomialModule T n d` is literally the free O_T module on homogeneous monomials
  of total degree d. `integralMonomial` projects its integral monomial to its own
  homogeneous degree (so does not alter it); `monomialSection` pulls that section back
  from integral Proj. `polynomialMap` sends each basis generator to that actual section.
  `IsIso (polynomialMap T n d)` records the canonical identification V_d = p_*O(d).
  Thus the displayed exact sequence is stated in its p_*O(d) coordinates, with an
  explicit fixed identification with V_d, not an arbitrary middle-term isomorphism.
- `sectionInclusion` is p_* of the ideal inclusion tensored with O(d), followed by
  the left unitor. `sectionRestriction` is p_* of the section-normalized pullback unit
  followed by the canonical pushforward-composition isomorphism. The existence of
  the zero-composite proof and `ShortComplex.ShortExact` asserts every part of
  0 -> p_*I(d) -> V_d -> (pi)_*O_Z(d) -> 0, including both endpoints.
- All three `.IsFiniteLocallyFree` clauses are present. Rank P(d) of the last term is
  expressed at every t by an open neighbourhood U and a finite free trivialization
  with rank r satisfying `P.eval d = r`. Placing t before r preserves the empty-base
  case for negative or unrealizable numerical polynomials.
- For every `T'` and arbitrary `g : T' ⟶ T`, the three `moduleBaseChangeMap` clauses
  assert the actual canonical base-change isomorphisms for I(d), O(d), and O_Z(d).
  The squares use Mathlib fibre products and their canonical projections, with
  `pullback.condition`. There is no flatness or finiteness assumption on g.
- The ideal after base change is explicitly the kernel ideal of
  `pullback.snd i (pullback.fst p g)`. The isomorphism φ is normalized by equality
  after composition with its monic ideal inclusion: it is the actual pullback of
  the ideal inclusion followed by `tensorPullbackObjUnitToUnit`. This rules out
  replacing the base-changed ideal by an unrelated sheaf. Tensor compatibility and
  the existing canonical twist base-change isomorphism identify the twisted targets.
- The sequence pulled back by `tensorPullback g` is explicitly short exact as well.
  The canonical maps for the whole sequence commute by
  `moduleBaseChangeMap_naturality`, including the restriction unit and the natural
  pushforward-composition maps. The normalized ideal map identifies its kernel with
  the kernel in the base-changed sequence. Thus this is the entire canonical
  sequence and both actual direct images commuting with base change.
- `Epi (evaluation i m)` is exactly surjectivity of p^*p_*I(m) tensor O(-m) -> I.
  Its definition uses the normalized counit, canonical twist multiplication,
  O(m) tensor O(-m) = O(0), O(0) = O, and the right unitor.
- Multiplication is quantified by `e : ℕ`, equivalently d=m+e and d-m=e.
  `IsIso (polynomialMap T n e)` identifies its source with V_e. The morphism μ
  has source p_*O(e) tensor p_*I(m) and target p_*I(m+e). Its formula on EVERY
  open U and pair of sections fixes it as actual multiplication (the swap of the
  two factors gives ideal-section times polynomial-section). Pure local tensor
  sections generate the sheaf tensor product, so this normalization determines μ;
  it is not an unconstrained map. `Epi μ` is the stated surjectivity, including e=0.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, with its stalkwise equivalence.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; quasi-compactness and quasi-separatedness are
  Mathlib's classes on the same composite.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`: `Proj.twist`;
  the standard-base implementation is `ProjectiveSpace.twist` in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`.
- `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace`: `RelativeProjectiveSpace.scheme`,
  `π`, and the homogeneous monomial index `monomials`; the equivalent standard scheme
  is `AlgebraicGeometry.ProjectiveSpace` in the upstream projective-space module.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullback`, `tensorPullbackSectionAdjunction`, and their normalized unit/counit.
- `Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality`:
  `equations`, `coordinatePiece`, `coordinateDimension`, `IsCoordinatePolynomial`,
  `baseChangeEmbedding`, and `geometricPoint`, recorded by the new definition node
  `def-sfb-projective-coordinate-hilbert-polynomial`, give the exact coordinate-fibre
  hypothesis. The locality theorem is used only by the proof plan, in proof_deps.
- `WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`:
  `Scheme.Modules.moduleBaseChangeMap` and `moduleBaseChangeMap_naturality`.
- Existing upstream ideal modules, tensor structure-sheaf comparison, twist tensor
  isomorphism, and finite locally free classes supply all remaining constructions.
  Every already stated proof dependency's module is imported; the three unsplit
  regularity/ideal prerequisites have no Lean modules to import yet.

The item's `stmt_deps` gains the two already landed projective-space realization and
twist nodes, plus the new coordinate-polynomial definition node described below. The
locality theorem is retained in `proof_deps` and removed from `stmt_deps`. No dependency
module or mathematical statement correction is needed.

Edge cases checked: empty T (all three sheaves zero; rank condition pointwise vacuous),
P=-1 (no nonempty family; empty T retained), P=0 and empty Z (full ideal), Z equal to
projective space (zero ideal), n=0 (one homogeneous coordinate), d=m and e=0
(multiplication by scalar 1), arbitrary nonreduced and non-quasi-compact bases, and
nonflat arbitrary base changes. No extra nonemptiness, Noetherianity or reducedness
assumptions occur. No STATEMENT-DISPUTED fault was found.

Searches actually run using msearch.py:

- leanfinder: "Uniform generation and base change of projective ideal sections for flat
  finitely presented families with fixed Hilbert polynomial": 8 hits, on Proj,
  submersive presentations and flat/projective algebra; none states this bound.
- loogle: `"Hilbert", "Sheaf"`: zero hits.
- grep: `hilbertPolynomial|HilbertPolynomial|regularity` in AlgebraicGeometry: zero hits.
- leansearch: "uniform projective Hilbert polynomial bounds ideal sections arbitrary
  base change generation": 8 hits, including power-series Hilbert polynomials and
  Proj vanishing ideals; none states the geometric relative section bound.
- Local rg of `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for Hilbert/regularity terms found the coordinate
  polynomial, relative space and twist interfaces used here. Searching the exact item
  id found only its use in the Hilbert representability module's proof plan, not an
  existing declaration of the bound.

Source reading: varieties.tex labels lemma-bound-quotients-free,
lemma-m-regular-up, lemma-m-regular-multiply, lemma-m-regular-globally-generated;
the eight reviewed DAG proof steps are retained in full in the theorem docstring.

Validation: all files are compiled only through scompile.py. The complete theorem
signature and the explicit monomial map compile cleanly against the live server
library, within the unchanged 60-second per-file limit. The only postponed theorem
is `HilbertSectionBound.exists_uniform_bound`.

## Second reading by NS

This is the author's second clause-by-clause pass, not a claim that another worker
was started. The dispatcher brief prohibits starting other agents and assigns the
independent reading to the maintainer.

I reopened the node and the final signature. The bound is outside the base/family
quantifiers; all five morphism hypotheses are retained; the coordinate-polynomial
hypothesis is the actual recorded geometric-fibre predicate; the polynomial-to-section
map has fixed monomial normalization; both short-exact endpoints are included; all
three local-freeness clauses and the precise rational rank are present. The rank
quantifier was deliberately kept pointwise to retain the negative-P/empty-T case.
The base-change clauses use arbitrary g and explicitly the new kernel ideal;
evaluation has the correct negative twist; multiplication covers every e=d-m,
including e=0, with its section formula rather than an arbitrary surjection.

The first pass's Euler-fibre rendering was replaced by the existing exact homogeneous
coordinate predicate. An integer `0+d` cast in the monomial section was made explicit
using the existing zero-add equality. No mathematical statement was changed.

Delivery preflight: deliver2.py --no-push returned OK for the three-file packet,
with clean per-file server compilation. The final pass also removed an unused
boundary-comparison import and narrowed the local-freeness import.

## New nodes

`def-sfb-projective-coordinate-hilbert-polynomial` owns the six existing plain
definitions `ProjectiveHilbertPolynomial.equations`, `coordinatePiece`,
`coordinateDimension`, `IsCoordinatePolynomial`, `baseChangeEmbedding`, and
`geometricPoint` in `Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality`,
lines 55--107. Its record is `existing: true`: brief-stage2 §1(A)/§5 requires reusing
these published declarations without a duplicate module. The existing module is
already publicly imported by the item. The theorem node's file and record are unchanged.

Clause-by-clause: `equations` takes the span of homogeneous polynomials vanishing after
`dehomogenizeX` and `chartRingEquiv` on every pulled-back standard chart; `coordinatePiece`
is the literal submodule quotient; `coordinateDimension` is its `Module.finrank`;
`IsCoordinatePolynomial` says eventual equality in `Filter.atTop` over the natural
degrees, equivalently some N works for every d >= N. `baseChangeEmbedding` is
`ProjectiveSpace.liftBaseChange` applied to the two actual pullback projections,
with their commuting-square proof. `geometricPoint` is `Spec.map` of the residue-field
inclusion into `AlgebraicClosure`, followed by `fromSpecResidueField`. All six definitions
have real data, no sorry, no polynomial choice, and no assumption of flatness or
nonemptiness. The predicate is defined for every morphism i; the main item separately
requires a closed immersion, exactly as before.

Sources reopened: varieties.tex, Tags 08AC and 08AE (Hilbert polynomial and eventual
H0 dimension); constructions.tex, Tag 03GL (kernel of homogeneous polynomial restriction,
with chartwise dehomogenization), definition-projective-space and Tag 01O3 (base change);
etale-cohomology.tex, Tag 03PO (geometric point). The inherited helper docstrings cite
01W6 and 02H5 for the last two constructions, but tags/tags maps these to proper images
and actions by derivations. The new node gives the correct source places; this return
does not require editing the published module's docstrings.

Searches performed for this repair, recorded verbatim from searches.jsonl in the new node:

- LeanSearch: "Hilbert polynomial of a projective closed subscheme as eventual dimension
  of homogeneous coordinate quotient by chartwise equations": eight scalar Hilbert-series
  polynomial hits, no geometric coordinate predicate.
- LeanFinder: "homogeneous coordinate Hilbert polynomial defined by eventual vector space
  dimensions of graded pieces of a projective scheme": eight hits on scalar Hilbert
  polynomials, Proj and vanishing ideals, no exact geometric predicate.
- msearch grep: `IsCoordinatePolynomial|coordinatePiece|coordinateDimension|HilbertPolynomial`
  in Mathlib AlgebraicGeometry: zero hits.
- rg of dag/nodes, lean/WeilConjectures/AlgebraicGeometry and lean/Sheaf/AlgebraicGeometry:
  the exact definitions occur only in the locality module; its theorem record lists
  them as helpers but no definition node owns the predicate. The Euler predicate of
  `def-sfb-projective-fibre-hilbert-polynomial` is different. The supplied-ideal quotient
  grading of `def-sfb-coordinate-quotient-grading` does not define these equations or
  this predicate. blueprint_refs.py search "coordinate Hilbert polynomial": zero matches;
  ancestor reports None, retained in blueprint.from.node with the item's full via chain.

Definition edge cases: X empty gives all equations and zero quotient in every degree;
for i the identity, no nonzero polynomial vanishes on every chart. At n=0 there is
one coordinate and the same quotient definition applies. Nilpotents are tested by
scheme-theoretic section restriction, not setwise point vanishing. d=0 is included.
Arbitrary base change uses the actual fibre product; empty T makes the point-indexed
hypothesis vacuous. The universe is u for schemes, fields and all coordinate quotients.

## Repair of H2/H12

The returned immutable head bce3fcaa8d0e was mechanically clean; the saved packet's
initial dry run again passed (a196230e944). The missing definition ownership is now
repaired by the new definition node above. In the item `stmt_deps`, it replaces
`lem-sfb-flat-projective-hilbert-polynomial-locality`; that theorem remains in
`proof_deps`. The Lean theorem signature, definitions, quantifiers and mathematical
statement are retained exactly, including every clause independently accepted in the
return. This is a node ownership repair, not a statement correction.

Second reading of the repair: I reopened all six definitions and checked each against
the new node's formula and canonical maps, and reread the item's fibre hypothesis: it
uses exactly `IsCoordinatePolynomial` of `baseChangeEmbedding` at `geometricPoint`.
None of those terms selects data from the locality theorem. Thus the new statement
dependency is a definition node and the locality theorem is solely a proof prerequisite.
The remaining hypotheses and conclusions are unchanged from the clause-by-clause
second reading above.
