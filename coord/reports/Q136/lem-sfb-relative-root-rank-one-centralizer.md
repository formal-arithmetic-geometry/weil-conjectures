## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RelativeRootRankOneCentralizer`
states `AlgebraicGeometry.RelativeRootCentralizer.relative_root_rankOne_centralizer`.
Its only postponed proof is the whole proof of this named theorem. The helper module
contains real constructions and predicates, with no sorry. No statement correction.

Hypothesis and clause audit:

- Any commutative ring A, including the zero ring: `{A : Type u} [CommRing A]`.
  All test algebras have the same universe as A; no smaller test universe is imposed.
  Spec and schemes are the recorded Mathlib declarations.
- Group scheme over S: `Grp (Over (Spec (.of A)))`, using `CategoryTheory.GrpObj`.
  `RingGroupSchemes.splitTorus A r` is exactly the existing product of multiplicative
  group schemes, including r=0. The auxiliary additive group in the node is not used
  in a hypothesis or conclusion; no additional additive group datum is required.
- Smooth affine finitely presented G: `[Smooth G.X.hom] [IsAffine G.X.left]`
  `[LocallyOfFinitePresentation G.X.hom]`. An affine scheme over the affine base is
  quasi-compact and separated over the base, so this is finite presentation.
- Connected reductive geometric fibres: `hred` quantifies over every algebraically
  closed field F and ring map A to F; `extend f` is the actual pullback group functor.
  The existing `ReductiveTorusCentralizer.IsReductive` retains geometric connectedness
  and the faithful-matrix unipotence convention, including nonreduced subgroup tests.
- Split maximal torus: `i` has the recorded closed immersion hypothesis; `hmax`
  asserts the existing maximal-torus predicate on every geometric fibre.
- M=Z^r: `Fin r → ℤ`. Nonzero alpha is `hα`. Local rank one is `hline` with
  `IsLine (A := A) (weight i α)`. It is Zariski local freeness, not a global basis.
- The decomposition alpha=d alpha0 is `d`, `hd`, `hdiv`. Primitivity is the Bezout
  equation `hprimitive`, equivalent to coordinate gcd one for a finite integer tuple.
  These describe arbitrary choices satisfying the stipulated decomposition, not an
  additional existence hypothesis on a root.
- Primitive root-kernel torus: the existential `K`, `k`, closed immersion, and equality
  of its point image with `{t | characterValue r α0 t = 1}` on every algebra. The
  group is isomorphic to `splitTorus A (r - 1)`. This specifies the actual kernel,
  not the possibly nonreduced kernel of alpha itself.
- Centralizer representation: existential `H`, `h` with closed immersion, smoothness,
  affineness, local finite presentation and connected reductive geometric fibres.
  `centralizer (k ≫ i) B` is precisely the displayed universal commuting functor;
  equality with `Set.range` of h is representability with its inclusion into G.
- Torus in H and central root-kernel torus: `j ≫ h = i`, `q ≫ h = k ≫ i`, and
  universally quantified `Commute (t ≫ q.hom.hom) x`. Closed immersion into G makes
  the factorization maps genuine inclusions.
- Lie equality as submodules: `lieImage h = lieImage i ⊔ weight i α ⊔ weight i (-α)`.
  The two `Disjoint` clauses say this sum is direct. `lieImage` is the span of the
  actual differential image on dual-number points; it equals that image because
  this tangent map is linear. No field-only differential is used over A.
- Negative root line: `IsLine (A := A) (weight i (-α))`.
- Precisely the two roots on every geometric fibre: maximality of base-changed j
  and the equivalence `(m ≠ 0 ∧ weightBase j F m ≠ ⊥) ↔ m = α ∨ m = -α`.
  The universal character eigencondition is equivalent to the coaction equation
  rho(v)=v tensor z^m: test the universal torus point, and conversely evaluate it.
  The eigencondition is closed under tangent addition and scaling, so taking its
  span in `weight` and `weightBase` does not enlarge its solution set.
- Arbitrary base changes: every commutative A-algebra B has linear equivalences eG
  and eH. `IsLieComparison` fixes their action on each pure tensor by actual tangent
  points, scalar extension, epsilon scaling, and the pullback projection. They are
  not arbitrary abstract equivalences. The image equalities for every weight and
  for `lieImage h` and `lieImage i` retain the inclusions inside Lie(G_B).
  The final C-algebra quantification says the pulled-back H represents the same
  universal commuting functor over B.
- Successive changes: `ComparisonsCompose G` and `ComparisonsCompose H` equate the
  direct comparison of c h(b) tensor v with the successive comparison of
  c tensor (b tensor v), after the canonical iterated pullback projections.
  Pure tensors generate, so this is full linear coherence. The weight and tangent
  inclusions are the submodules transported by these same maps, hence their
  comparisons and decomposition maps inherit this coherence. Centralizer
  comparisons are determined by equality of their represented subfunctors in G;
  their successive comparison is the identity on the same G-points.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, bundled `Grp`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, used through reductivity.
- `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`:
  `AlgebraicGeometry.RingGroupSchemes.multiplicative`, `splitTorus`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring` and its public imports:
  `AlgebraicGeometry.GrpObj.Lie`, its A-module structure, `tangentPoint`, and
  `AlgebraicGeometry.points`, `points.map`. Lie.Basic, Lie.Functoriality and Lie.Ring
  were read in full at the relevant definitions; these APIs work over rings.
- `Mathlib.Algebra.DualNumber`: `DualNumber`, with the existing coefficientwise
  `DualNumber.mapRingHom` in `WeilConjectures.AlgebraicGeometry.DualNumbers` and
  epsilon scaling from `WeilConjectures.Mathlib.Algebra.DualNumber`.
- `Mathlib.Algebra.Module.LocalizedModule.Away`: `LocalizedModule.Away` and its
  existing `Localization.Away` module structure.

Proof imports (plain imports):
`Sheaf.RepresentationTheory.RelativeTorusBundleWeights` and its recorded theorem
`SplitTorus.relative_torus_bundle_weights` and base-change/invariants clauses;
`Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections` and
`AlgebraicGeometry.RankOneRoots.reductive_rankOne_reflections`;
`WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree` and
`Module.exists_localizationAway_equiv_finsupp_of_finite_projective`.
The other proof dependency `lem-sfb-relative-torus-centralizer-normalizer` has no
Lean record, so no module can be imported for it; its mathematical proof role is
preserved in the theorem docstring. It supplies no notion required by this statement.

Edge cases checked before writing: r=0 has no nonzero alpha; r=1 gives the trivial
kernel torus and H=G. Nonprimitive roots of SL2, including characteristic two, use
alpha0 rather than the nonreduced root kernel. The weights use actual characters,
never their differentials. A=0 has empty spectrum, making local rank-one conditions
vacuous as required; all tangent modules vanish and all fibre conditions are empty.
Nonreduced A and nonflat extensions are permitted. Nontrivial line bundles (Conrad's
GL(A plus J) example) are allowed by `IsLine`, with no free-generator hypothesis.
A torus over a nonzero base cannot supply the assumed nonzero rank-one root space.

Searches: msearch LeanFinder query “Centralizer of a root kernel subtorus in a
reductive group scheme over a ring has Lie algebra the torus and opposite root lines”
returned eight abstract Lie/root-system declarations, no relative group theorem.
Loogle `"centralizer", "Scheme"` returned zero hits. Mathlib grep
`centralizer|Centralizer|reductive` in AlgebraicGeometry returned zero. LeanSearch
“Relative Lie algebra character weights for conjugation by a split torus over an
arbitrary commutative ring” returned LieCharacter and differentiated LieModule
weights, no match. A further Mathlib grep for relative Lie/weight, character weight,
and centralizer returned zero hits. Project rg found only field-based characterValue
and field tangent weight interfaces; no relative interface. The exact item id has
no declaration in WeilConjectures. DAG and blueprint searches found no existing
relative interface node; the existing split torus and field reductivity nodes are
reused. Exact msearch JSON responses are included in the new node's mathlib_searches.

Source read: Conrad PDF, introduction p.2; Section 4 introduction p.107;
Definition 4.1.1; Lemma 4.1.3 and proof pp.108–109. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was also read. It is not this lemma's statement. No STATEMENT-DISPUTED issue found.

## New nodes

`def-sfb-relative-root-centralizer-interfaces` defines only the missing relative
character evaluation, universal character tangent weight and centralizer predicates,
and the characterization/coherence conditions for the canonical tangent comparison.
Its source is Conrad pp.107–109 and the introduction's dual-number Lie convention.
The Lie module itself, product torus, scheme pullback, dual numbers, and localizations
are all existing constructions. The searches above and the new node's exact search
records distinguish this from field-only weight/centralizer terminology and the
abstract supplied-coaction module of `SplitTorus.weightSpace`. It imports no theorem
about the centralizer it helps state. The item's stmt_deps also gains the already
landed split-torus and reductive-terminology nodes used in its signature.

## Second reading by Q136

A second in-session reading compared the full node and both modules against the
clause audit above. This was performed by the same worker; the dispatch explicitly
prohibits starting another agent, and the maintainer supplies the independent review.
The read found and fixed the need to test characters after every algebra extension,
not merely on A-points, and the need to characterize the scalar comparisons by
pure-tensor tangent points, not just assert abstract isomorphisms. It checked the
kernel at alpha0, both disjointness clauses, all geometric fibres, the negative
line, nonflat extensions, and successive comparisons. The existing Lie module was
reused instead of supplying another tangent module. Compilation errors from a wrong
module path, a unit-map expression, a missing scoped MonObj instance and an implicit
base ring of IsLine were repaired. All declaration variables/universes are explicit
and autoImplicit is false. No theorem proof other than the named main sorry is added.
