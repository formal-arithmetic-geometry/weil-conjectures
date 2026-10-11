## Worker report

Module: `lean/Sheaf/CategoryTheory/ExactCoupleConvergence.lean`.
Main declaration: `CategoryTheory.BigradedExactCouple.ConvergesTo`.
The node is unchanged outside `lean`. No new nodes or dependency modules are needed:
every construction below is a clause or internal implementation of this definition node.
All theorem proofs are `sorry`; all definitions have actual data. The finite cycle tower
is selected from a named existence theorem specifying its recursion and canonical maps,
just as the dependency selects the maps of the derived couple from its existence theorem.
Each postponed theorem has a source and natural-language proof in its docstring.

Dependencies read and used:

- `Sheaf.CategoryTheory.ExactCouple`, `CategoryTheory.BigradedExactCouple`, its
  `pageCouple`, `d`, `dInto`, and `derivedEProjection`. The type-zero couple is the node's
  initial couple, and `pageCouple r` represents page `r+2`. Its structure has the prescribed
  bidegrees, zero composites, and kernel/image equalities. Its derived page is the cokernel
  of the incoming differential lifted into the outgoing kernel.
- `Sheaf.CategoryTheory.Filtration`, `CategoryTheory.DecreasingFiltration`,
  `DecreasingFiltration.gradedPiece`, `.IsSeparated`, and `.IsExhaustive`.
  These are the recorded integer-indexed subobject filtration and its specified quotients
  and extremal-subobject conditions. No private filtration definition is introduced.
- Mathlib's `Subobject`, `Subobject.pullback`, `Subobject.«exists»`, `Subobject.ofLE`,
  `Subobject.Factors`/`.factorThru`, `imageSubobject`, `kernelSubobject`,
  `factorThruImageSubobject`, `kernel`, `cokernel`, `IsGLB`, `IsLUB`, `Epi`, and `IsZero`.

Hypothesis-by-hypothesis and clause-by-clause reading:

1. An arbitrary abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`, with
   both universes explicitly declared. The exact-couple situation is
   `(X : BigradedExactCouple C 0)`. All bidegrees and total degrees are integers.
2. Cycles and boundaries are subobjects of the INITIAL page: `CycleBoundaryTower.Z`
   and `.B` take values in `Subobject (X.E p q)`. The index `r : ℕ` is an offset of two,
   covering exactly the pages numbered at least two, rather than adding pages zero or one.
3. `Z₂=E₂` and `B₂=0` are `.Z_zero` (top) and `.B_zero` (bottom). The initial quotient
   map `.projection_zero` is the arrow of the top subobject, hence the identity after its
   canonical identification with the initial page.
4. `E_r=Z_r/B_r` is expressed by the epimorphic `.projection r p q` and the equation
   `.projection_kernel`, identifying its kernel with the inclusion of `.B` into `.Z`.
   These are quotient presentations in an abelian category, not arbitrary objects called
   quotients. The target is the dependency's actual `pageCouple r` term.
5. `.Z_succ` and `.B_succ` are respectively the inverse images of the outgoing kernel
   and INCOMING differential image under `.projection`, followed by the image along
   `.Z.arrow` to regard both as subobjects of the initial page. `.B_le_Z`,
   `.Z_decreasing`, and `.B_increasing` give exactly the stated inclusions.
6. The successor quotient map is canonical: `.cycleLift_comm` specifies its lift to the
   outgoing kernel, and `.projection_succ` composes that lift with the dependency's
   `derivedEProjection`. This prevents unrelated quotient identifications from changing
   subsequent cycles and boundaries.
7. The phrase 'when these limits exist' is `L : LimitSubobjects X`. Its `.Z_glb` and
   `.B_lub` specify the intersection and union by their universal properties in the
   subobject poset, without assuming that all subobject lattices are complete. The named
   `limitBoundary_le_cycle` states the necessary inclusion. `pageInfinity` is the
   cokernel of that inclusion, hence `Z∞/B∞`.
8. `IsRegular` is pointwise eventual constancy of the finite cycle subobjects; the
   stabilization bound may depend on both `p` and `q`. It does not require boundary
   stabilization or a uniform bound.
9. `alphaIter` and `incomingAlphaIter` are the actual composites of `X.alpha`, transported
   only by integer index equalities. `IsComplete` says every subobject lying in all
   `imageSubobject (incomingAlphaIter r p q)` is bottom. Since bottom is a common lower
   bound, this says the intersection exists and is zero, with no extra limit hypothesis.
10. `IsBounded` is finiteness of `{(p,q) | p+q=n and not IsZero (X.E p q)}` for every
    integer `n`. It refers to the initial page, not to `D` or a later page.
11. The assumed diagonal colimit is `A : ∀ n : ℤ, AlphaColimit X n`. The structure stores
    its object, its canonical maps `.ι p`, their compatibility with `alphaDiagonal`, and
    the unique-factorization universal property `.isColimit`. Compatibility on consecutive
    arrows is equivalent to compatibility on all arrows of the integer chain, because
    every such arrow is a finite composite. This is exactly the colimit as `p` tends to
    negative infinity, not an arbitrary cocone, target, or isomorphic abstract object.
12. `imageFiltration` has step `imageSubobject (A.ι p)`. The named antitonicity theorem
    uses the cocone equation, yielding `F^{p+1}≤F^p`. The result is the dependency's
    `DecreasingFiltration`.
13. `initialG` transports only the unsimplified type-zero target indices `p+0,q-0` of
    the dependency's `g`. `g_factors_limitCycles` states the permanent-cycle factorization;
    `toPageInfinity` composes it with the quotient projection to `E∞`.
14. `toGradedPiece` is the canonical image factorization of `D^{p,q}→A^{p+q}`, followed
    by the dependency's graded-piece quotient map. Its sole initial transport identifies
    `q` with `(p+q)-p`.
15. `WeaklyConvergesTo` requires BOTH canonical maps to be epimorphisms and their kernel
    subobjects in the SAME `X.D p q` to coincide, at every bidegree. The named statement
    `weakConvergence_comparison` gives the unique isomorphism commuting with these maps,
    so the node's associated-graded isomorphism clause is also explicitly represented.
16. `AbutsTo` is weak convergence together with `.IsSeparated` and `.IsExhaustive` for
    every image filtration, using exactly the dependency's two predicates.
17. `quotientTransition` is the canonical `A/F^{p+1}→A/F^p`, by `cokernel.desc` from the
    earlier quotient projection. Its required zero equation is a named theorem.
    `IsInverseLimit` gives the unique-lift universal property of the canonical cone
    `A→A/F^p`. This includes existence of the inverse limit and states that the canonical
    comparison with it is an isomorphism. Once again consecutive-arrow compatibility
    specifies the entire integer-chain diagram.
18. `ConvergesTo` is exactly `IsRegular ∧ AbutsTo ∧` this inverse-limit condition for
    every total degree. Couple completeness `IsComplete` is separately defined; it is
    not accidentally imposed as a further convergence hypothesis.

Edge cases checked before writing:

- No first-quadrant restriction: negative `p`, negative `q`, and negative total degrees
  are allowed throughout. Bounds of regularity vary by bidegree, and boundedness is only
  diagonal finiteness. Empty support is finite, including the zero couple.
- Page two is the offset-zero term with top cycles and bottom boundaries. All successor
  differentials come from the recorded derived couples; the incoming differential is
  `dInto`, not the outgoing map viewed as having the wrong codomain.
- The alpha iterate of length zero is the identity (up to index transport); including
  its full image in the intersection imposes no extra completeness condition.
- All finite constructions exist in every abelian category. Infinite cycle/boundary
  bounds and diagonal colimits are supplied only where the node assumes their existence.
  No AB5, enough-injectives, countable limits, or first-quadrant assumptions are added.
- The colimit and inverse limit range over the full integer chain, not just nonnegative
  integers. Their test objects range over the same unrestricted category as the objects
  being constructed. The inverse-limit statement concerns the canonical cone, not merely
  a possibly unrelated isomorphism of objects.
- Zero objects and zero maps satisfy the stated universal properties and comparison
  clauses. Weak convergence is not defined merely by existence of unrelated isomorphisms.

Searches for an existing statement or definition:

- `msearch.py ... leanfinder "convergence of bigraded exact couple regular complete cycles
  boundaries abutment filtration"`: eight hits on homological-complex exactness,
  Grothendieck abelian categories, and unrelated homology; none match.
- `msearch.py ... loogle "SpectralSequence.AbutsTo, BigradedExactCouple"`: zero hits,
  unknown identifier `SpectralSequence.AbutsTo` in the Mathlib search service.
- `msearch.py ... leansearch "convergence of exact couple regular complete abutment
  filtration"`: unavailable, Internal Server Error. This search was attempted and is not
  treated as a negative result.
- `msearch.py ... grep "AbutsTo|WeaklyConverges|pageInfinity|ExactCouple"
  Algebra/Homology`: zero Mathlib hits.
- `rg` over the project's `lean/Sheaf` and the source project's homology/category modules
  found the recorded exact-couple and filtration modules and the upstream
  `WeilConjectures/Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`. The upstream
  declaration `SpectralSequence.AbutsTo` was read with its docstrings: it applies only to
  `E₂CohomologicalSpectralSequenceNat`, uses nonnegative bidegrees, fixes `F⁰=H` and
  `F^{n+1}=0`, and supplies unrelated nonempty graded isomorphisms. It does not express
  this general exact-couple definition, its canonical comparison, or regular/complete
  conventions. Its `pageInfinity` is also a stable first-quadrant page, not this quotient.
- `rg "def-sp-convergence"` in `dag/lean_names_upstream.json` and all of the source
  project's `WeilConjectures/` found no declaration tagged to this node.
- `rg "CycleBoundaryTower|AlphaColimit|WeaklyConvergesTo|def IsInverseLimit|def
  incomingAlphaIter"` in Mathlib, the source project, and the shared library found no
  existing declaration. The other names are in the exact-couple namespace and checked
  by the delivery preflight.

Sources read: both dependency node records and their complete Lean modules; this node's
entire statement and record; Stacks https://stacks.math.columbia.edu/tag/011N and
https://stacks.math.columbia.edu/tag/012U. The local blueprint/literature source documents
named in the records are not materialized on this machine; the available node record and
online Stacks definitions were used. The convergence predicates follow the explicit
blueprint convention in the node, with Stacks 012U supplying the separated/exhaustive/
regular/inverse-limit terminology for filtered-complex spectral sequences.
No statement correction or disputed statement.

Validation: server `scompile.py J1 def-sp-convergence` succeeds without errors or warnings
(1.6 seconds). The file has explicit universes and binders and no line over 100 columns.
The delivery dry run is the final check; no second-reading section is written by this worker.

## Second reading by J1

I independently read the complete delivered module, the item JSON, both dependency
JSON records and their complete Lean modules. No statement correction is present or
needed, and there are no new nodes or dependency modules to audit. The following is
my inventory of the node, with its Lean counterpart and verdict for every clause.

1. Ambient object and hypothesis: an arbitrary abelian category and the initial
   bigraded exact couple. Rendered by `{C : Type u} [Category.{v} C] [Abelian C]`
   and `X : BigradedExactCouple C 0`. PASS: the recorded dependency's `alpha`, `f`,
   `g`, exactness equalities and zero-composite fields have exactly the node's
   bidegrees; the type-zero specialization is the prescribed initial couple.
2. All finite cycles and boundaries are subobjects of the initial `E₂`.
   `CycleBoundaryTower.Z/B : ℕ → ∀ p q : ℤ, Subobject (X.E p q)`.
   PASS: offset `r` means page `r+2`, not a nonnegative-bidegree restriction.
3. Initial cycles equal `E₂`, and initial boundaries are zero.
   `Z_zero`, `B_zero`, `projection_zero`. PASS: top, bottom and the top-subobject
   arrow give the prescribed initial quotient, including its canonical map.
4. Every page is the quotient `Z_r/B_r`. `projection_epi` and
   `projection_kernel`, with target `(X.pageCouple r).E p q`. PASS: these are
   quotient presentations of the recorded dependency's pages in an abelian category.
5. Successor cycles are inverse images of outgoing kernels; successor boundaries
   are inverse images of incoming images. `Z_succ/B_succ` use pullback along
   `projection`, then `Subobject.«exists» Z.arrow` into the initial page.
   PASS: `dInto` was opened and its source is the incoming bidegree, so this is
   the image at the intended component, not the outgoing differential's image.
6. Boundaries lie in cycles, cycles decrease, boundaries increase, and next-page
   quotient identifications are canonical. `B_le_Z`, `Z_decreasing`, `B_increasing`,
   `cycleLift_comm`, `projection_succ`. PASS: the last equality uses the actual
   `derivedEProjection` (a cokernel projection), not an arbitrary page isomorphism.
7. When limits exist, intersection, union and quotient define the infinite page.
   `LimitSubobjects.Z_glb/B_lub`, `limitBoundary_le_cycle`, `pageInfinity`.
   PASS: GLB/LUB in the subobject order give precisely these limits; no completeness
   of the entire subobject lattice or additional category hypothesis is required.
8. Regular means each cycle tower eventually constant. `IsRegular` has
   `∀ p q, ∃ r, ∀ t, r ≤ t → Z t p q = Z r p q`. PASS: independent bounds
   at each bidegree; neither boundary stabilization nor a uniform bound is imposed.
9. Complete means zero intersection of incoming alpha images.
   `alphaIter`, `incomingAlphaIter`, `IsComplete`. PASS: the maps really compose
   the given alpha from `(p+r,q-r)` to `(p,q)`; all common lower bounds being bottom
   is equivalent to existence of the intersection with value zero.
10. Bounded means finite nonzero support on each initial total-degree diagonal.
    `IsBounded` uses `Set.Finite {pq | pq.1 + pq.2 = n ∧ ¬ IsZero (X.E ...)}`.
    PASS: no bound on the entire plane or on the D terms is introduced.
11. Assume the alpha-colimit in every total degree. `A : ∀ n : ℤ, AlphaColimit X n`,
    with `obj`, `ι`, `comm`, `isColimit`. PASS: `alphaDiagonal n p` goes from
    index `p+1` to `p`. The compatibility equation has the correct direction,
    and `∃! h` against every `T : C` is the full cocone universal property.
    Every comparable pair in the integer chain is connected by finitely many
    consecutive arrows, so this presentation neither adds nor loses a condition.
12. The induced decreasing image filtration has `F^p = im(D^{p,n-p} → A^n)`.
    `imageFiltration.step` and `imageFiltration_antitone`. PASS: antitonicity
    follows from `comm`; the output uses the recorded `DecreasingFiltration`.
13. The initial g lands in limiting cycles and gives the canonical map to E∞.
    `initialG`, `g_factors_limitCycles`, `toPageInfinity`. PASS: transports only
    simplify type-zero indices; the map is the factorization of g followed by
    the cokernel projection of the actual limiting boundary inclusion.
14. The filtration supplies a canonical map to `gr^p A^{p+q}`. `toGradedPiece`.
    PASS: transport identifies `q = (p+q)-p`, followed by the canonical image
    factorization and the recorded filtration's graded-piece cokernel projection.
15. Weak convergence requires both maps onto with the same kernel and gives
    canonical graded isomorphisms. `WeaklyConvergesTo` and
    `weakConvergence_comparison`. PASS: categorical epis mean surjections here;
    both kernel subobjects belong to the same `X.D p q`. The unique comparison
    isomorphism commutes with these two maps, so it is not an unrelated isomorphism.
16. Abutting adds separated and exhaustive filtrations for every total degree.
    `AbutsTo` uses the dependency's `IsSeparated` and `IsExhaustive` verbatim.
    PASS: their common-lower/upper-bound formulations express intersection zero
    and union the entire object, including existence of those extrema.
17. Convergence adds regularity and `A^n = lim_p A^n/F^p` to abutting.
    `ConvergesTo`, `IsInverseLimit`, `quotientTransition`. PASS: transitions go
    `A/F^{p+1} → A/F^p`; the test-family compatibility and unique lift through
    the canonical quotient maps express precisely the canonical limiting cone.
    `IsComplete` of the couple is correctly not an extra convergence condition.

Source check: the blueprint and Stacks source trees are not materialized in this
read-only clone. I obtained the official Stacks `homology.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/homology.tex into
`scratchpad/homology.tex` and read the spectral-sequence section's cycle/boundary
recursion, exact-couple formulas, `definition-bounded-ss`,
`lemma-relate-boundedness`, and `definition-filtered-complex-ss-converges`.
The section assumptions are an abelian category, with integer bigrading and
bidegree `(r,1-r)` in the bigraded discussion; no Noetherian, first-quadrant,
field, or infinite-(co)limit existence assumption is tacitly needed. Stacks
012U concerns filtered complexes; the node explicitly specializes its terminology
to the given exact-couple alpha-colimit and canonical comparison, which the Lean
retains. The cycle-stabilization definition of regular is explicitly equivalent
to eventual vanishing of outgoing differentials in `lemma-relate-boundedness`.
The exact-couple formula `Z_{r+1}=f⁻¹(im alpha^r)` confirms g's permanence.
I also read the public tag pages https://stacks.math.columbia.edu/tag/011N and
https://stacks.math.columbia.edu/tag/012U.

Edge cases: all `p,q,n` range over ℤ, including zero and negative degrees;
no arbitrary empty index set is part of this definition (the specified towers
are ℕ/ℤ indexed). Empty support is finite, and the zero couple and zero abutment
satisfy all clauses. Offset zero is exactly page two. Length-zero alpha is the
identity, whose full image adds no restriction to completeness. Infinite bounds
and colimits are supplied only where needed; no global countable completeness,
AB5, enough injectives, or well-poweredness assumption is added. Object and
morphism universes are independently bound, and universal properties test every
object of C. Schemes, characteristic and coefficient rings are not involved.

Independent searches (using words other than the worker's queries):

- LeanFinder: `integer indexed spectral sequence limiting cycles boundaries
  canonical associated graded comparison`: eight homological-complex cycle-map
  hits, none defining exact-couple convergence.
- Loogle: `IsLimit, cokernel`: service reports unknown unqualified `IsLimit`, so
  this is not evidence of absence. The local searches below cover limit notions.
- Mathlib grep service: `abutment|permanent cycles|complete filtration` under
  `Algebra/Homology`: zero hits.
- Local `rg` for `exact couple|ExactCouple|WeaklyConverges|AlphaColimit|
  CycleBoundaryTower|IsInverseLimit` in Mathlib homology, all source-project Lean,
  and project `lean/Sheaf`: only the recorded exact-couple dependency and its
  downstream users; no existing general convergence implementation.
- Broader local `rg` for abutment, permanent cycles, complete filtration and
  separated/exhaustive terminology in Mathlib CategoryTheory and homology, all
  source Lean, and project Lean found the first-quadrant spectral-sequence API.
  I opened `SpectralSequence.pageInfinity`, `.Abutment`, and `.AbutsTo` in
  `WeilConjectures/Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`:
  they use ℕ indices, finite endpoint conditions and bare nonempty graded
  isomorphisms, and cannot represent this node's general canonical comparison.
- `rg def-sp-convergence` in `dag/lean_names_upstream.json` and source Lean found
  no attachment. Thus retaining the new module is required by H4.

Mismatch repaired: the proof docstring for `g_factors_limitCycles` previously
said only that the induced g was killed by f at each page. That leaves the
relation of the INITIAL g to later cycles implicit. I replaced that explanation
with the exact-couple cycle formula, its induction, zero factorization through
all incoming alpha images, and the GLB/image-factorization argument. No Lean
signature, definition body, hypothesis, node statement, or dependency changed.
All other content was retained. Every theorem remains `sorry`; every definition
has actual data, with proof obligations separated as named theorems. The main
recorded signature is verbatim the file signature. Explicit universes and
binders were checked by eye; both imports are used, and all lines fit 100 columns.
