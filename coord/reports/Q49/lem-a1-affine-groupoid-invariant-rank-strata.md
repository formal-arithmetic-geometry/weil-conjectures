## Worker report

This is a stage-2 statement delivery. The repository's Q60 PASS dated 2026-10-18 is
the review of the stage-1 split, not an existing Lean statement. The node has no
`lean` record and no finished upstream declaration. The previous worker's stale
assignment diagnosis therefore does not apply to the present stage-2 brief.

`Sheaf.AlgebraicGeometry.AffineGroupoidInvariantRankStrata` states
`AlgebraicGeometry.affineGroupoid_exists_invariant_rank_strata`. Its sole theorem
has proof `sorry`. The groupoid predicate is imported from the existing module
`Sheaf.AlgebraicGeometry.GroupoidScheme`, owning node `def-a1-groupoid-scheme`.
This repair removes the former duplicate module and new definition node entirely.
The sole delivered Lean declaration is the rank-strata theorem.

Sources read: `literature/stacks-project/groupoids.tex`, the groupoid axioms before
Tag 0231 and its septuple characterization after the definition; Tag 03BI,
`lemma-finite-locally-free-disjoint-free`, including the proof; and the opening
paragraph of `lemma-integral-over-invariants`. The main node agrees with that
source's affine, quasi-compact specialization. No statement correction or dispute
is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

1. `A B : CommRingCat.{u}` and `Spec A`, `Spec B` are precisely the two arbitrary
   affine schemes. No nonzero-ring, reducedness, Noetherian or connectedness
   assumptions are imposed. The universe is arbitrary.
2. The binders `s t`, `e`, `i`, and `c : pullback s t ⟶ Spec B` are the specified
   source, target, identity, inverse, and composition. `hG : IsGroupoidScheme s t e i c`
   states that these maps, including these particular identities and inverses,
   define the groupoid functorially on test schemes. The convention is
   `c(a,b) = a ∘ b` with `s(a) = t(b)`, exactly as in the node.
3. `[s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]` give the two finite, flat,
   locally finitely presented morphisms. The recorded upstream predicate is used.
4. `I : Finset ℕ` and `∀ r : I, 0 < r.1` give a finite subset of the positive
   integers. A natural number with this strict inequality is exactly an integer
   at least one; there is no boundedness or fixed-rank hypothesis.
5. `U : I → (Spec A).Opens`, `Nonempty (U r).toScheme`,
   `IsClosed (U r : Set (Spec A))`, and `IsAffine (U r).toScheme` give nonempty
   affine open-and-closed object strata. `Pairwise ... Disjoint` and
   `(⨆ r : I, U r) = ⊤` give the disjoint decomposition. For open subschemes,
   a pairwise disjoint open cover is exactly their coproduct decomposition;
   this formulation uses the actual inclusion morphisms of the open subschemes.
6. `(IsEmpty (Spec A) → I = ∅)` is the stated empty-object-scheme clause.
   It also follows from the nonemptiness requirement on all indexed strata.
7. `V : I → (Spec B).Opens` with `V r = s ⁻¹ᵁ U r` and
   `V r = t ⁻¹ᵁ U r` specifies exactly the common inverse-image open
   subscheme `R_r`; equality is equality of opens, not just images or a
   choice of an unrelated arrow scheme. `IsAffine (V r).toScheme` is its
   required affineness.
8. For each `r`, the five existential binders `s' t' e' i' c'` have exactly
   the restricted object and arrow schemes as domains and codomains.
   `IsGroupoidScheme s' t' e' i' c'` requires all groupoid laws there.
9. The equations for `s'`, `t'`, `e'`, and `i'` after composition with the
   open inclusions say precisely that they restrict the original maps.
   The map `k` on composable pairs has both prescribed projections; the
   pullback universal property makes it the unique induced comparison,
   not an arbitrary map. `c' ≫ (V r).ι = k ≫ c` says that composition also
   restricts the given composition. This supplies all structure maps, not
   merely the source and target or an abstract existence of a new groupoid.
10. `s'.IsFiniteLocallyFreeOfDegree r.1` and its counterpart for `t'` assert
    finite local freeness and exactly the coordinate-algebra dimension of
    each scheme-theoretic fibre. The predicate uses `fiberDegree`, defined
    through `finrankΓ`; it is not a count of geometric points. Its finite
    locally free parent ensures that these dimensions are finite.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`; the full structure signatures and
  docstrings were read in the pinned source.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, in
  the same module. The main statement uses `Spec` on arbitrary commutative rings.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, its `fst`, `snd`,
  `lift`, and `map`, in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  Scheme pullbacks and their instances are supplied by
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-pc-finite-locally-free`: `Scheme.Hom.IsFiniteLocallyFree` and
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree`, from
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`. Both the local
  declaration and the current published source obtained with
  `scompile.py --source` were read. No dependency repair is needed.
- `def-a1-groupoid-scheme`: `AlgebraicGeometry.IsGroupoidScheme`, from
  `Sheaf.AlgebraicGeometry.GroupoidScheme`. Its full signature, all eleven fields,
  and docstring were read in the shared checkout and with `scompile.py --source`.
  Its composition is `c(a,b) = a ∘ b` with `s(a) = t(b)`. The first six fields
  express source and target compatibility, the next four express identities and
  inverses using the canonical pullback lifts, and `associative` is associativity
  on three composable arrows. The compatibility proofs exist by the first six
  fields; these universally quantified laws are not vacuous. This is exactly
  the groupoid notion needed here, for both the original and restricted maps.

The main module also imports the stated proof dependencies: the published
`WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant`
(read through `scompile.py --source` because the older local checkout lacks it),
`Mathlib.AlgebraicGeometry.Morphisms.FlatRank` for rank/base-change invariance,
`Morphisms.QuasiSeparated` for the affine qcqs clause,
`IdealSheaf.Subscheme` and `Morphisms.ClosedImmersion` for the recorded
affine-ideal-sheaf interface. The latter imports expose `AffineScheme` and the
prime-spectrum topology used for the clopen-idempotent and principal-open clauses.
The existing groupoid module's public pullback import exposes `OpenImmersion` as well.
The theorem docstring contains all seven proof steps, with their node citations.

Edge cases checked before writing: `A = 0` gives an empty object scheme and the
empty index set; no contradictory nonempty-ring assumption was introduced.
The identity groupoid on a nonempty affine scheme has only degree one.
A disjoint union of constant groups of orders two and three allows both strata,
so connectedness and fixed degree have not been introduced. Nonreduced finite
group schemes, such as characteristic-p roots of unity, are measured by algebra
dimension and retain their correct rank. Isotropy is allowed: there is no
monomorphism assumption on `(s,t)`. An empty arrow scheme over a nonempty object
scheme is excluded by the groupoid identity section itself. All test schemes
have the same arbitrary universe as the original schemes; this includes the
domains needed to test all diagram identities by Yoneda, so no smaller test
universe makes the condition vacuous.

Searches retained from the original packet through `msearch.py` (log `searches.jsonl`);
the stale project/DAG conclusions are superseded by the fresh repair search below:

- LeanFinder, `A finite locally free affine groupoid scheme has an invariant finite
  clopen decomposition into positive constant rank strata`: eight hits concerning
  affine covers, finite affine morphisms, and Galois-category connected
  decompositions. None states the groupoid theorem.
- Loogle, `CategoryTheory.Groupoid, AlgebraicGeometry.Scheme`: zero hits.
- LeanSearch, `groupoid object in the category of schemes with source target
  identity inverse and composition morphisms`: eight hits, abstract groupoids
  and the scheme category, with no internal groupoid structure.
- Grep, `GroupoidScheme|SchemeGroupoid|InternalGroupoid|GroupoidObject|groupoid.*rank|rank.*groupoid`:
  zero Mathlib hits.
- LeanFinder, `internal groupoid in schemes defined by source target identity
  inverse and associative composition on a fibre product`: eight hits, including
  `Scheme.GrpObjAsOverPullback`, which is a base-change instance for group objects,
  not a groupoid structure on two specified schemes. Its source was checked.
- Direct `rg` of Mathlib, `WeilConjectures`, and `lean/Sheaf` for the proposed
  declaration names found no collision. Direct groupoid/rank and
  internal-groupoid searches found no exact theorem or usable notion. The
  `SpaceGeometricDescent.IsGroupoidObject` declaration concerns simplicial spaces,
  not scheme morphisms. `FiniteFlatAffineRelationQuotient` concerns equivalence
  relations and a quotient theorem, with no exported groupoid structure.
- The prescribed upstream grep for the item ID and the search in
  `dag/lean_names_upstream.json` found no attachment. DAG searches for groupoid
  definitions and groupoid schemes found no node carrying this notion.
  `blueprint_refs.py search groupoid` returned seven imported blueprint nodes,
  none defining groupoid schemes; `ancestor` returned `lem-a1-affine-hc0`.

## Returned collision repaired

The independent review of head `3717b98ce125` found that
`GroupoidSchemeStructure` redeclared `AlgebraicGeometry.IsGroupoidScheme`, already
owned by `Sheaf.AlgebraicGeometry.GroupoidScheme`. The repaired item imports that
existing module and adds its landed node `def-a1-groupoid-scheme` to `stmt_deps`.
The sandbox-only `def-a1-groupoid-scheme-structure` node and its module are removed.
No declaration was renamed and no second groupoid predicate remains in this packet.
The theorem signature and the node's mathematical statement are unchanged.
Only `lean` and the authorized added statement dependency differ from current main.
There are no new nodes or dependency modules in the repaired delivery.

The earlier report's negative project/DAG search was stale: current main contains
Q05's groupoid node and module. A fresh `rg` finds `IsGroupoidScheme` there and
its existing consumers in `AffineGroupoidBasisDescent` and
`AffineGroupoidOrbitFibres`. `scompile.py --source` confirms the same published
interface. Comparing the full old and current structures shows the same groupoid
axioms: the old formulation quantified a map to each pullback and constrained its
projections; the existing formulation uses `pullback.lift` directly. Uniqueness
of maps to the pullback identifies these formulations. Thus importing the existing
predicate preserves every groupoid hypothesis and conclusion.

## Second reading by Q49

This is the author's second pass; the maintainer supplies the independent review
specified in the dispatch brief. For this repair I reopened the current node,
the retained rank-strata module, Q05's groupoid node and full module, the finite
local freeness declarations, and Stacks 0231/03BI. I checked the existing
`identity_comp`, `comp_identity`, `inverse_comp`, `comp_inverse`, and `associative`
fields against the source. In particular the inverse of `a` composed with `a`
gives `e(s(a))`, and the opposite order gives `e(t(a))`. The canonical pullback
lifts use exactly the two projections specified by the groupoid convention.
The first six fields ensure that all compatibility proofs in the remaining
fields exist. No involutivity assumption is needed: it follows from these laws.

I then matched every item clause as listed above. In particular, I checked the
nonempty pieces and empty index clause, pairwise disjoint cover, both equalities
of inverse-image opens, both affineness requirements, all five restriction
conditions, and both degree assertions. The comparison `k` is constrained by
both projections, which prevents a weakened arbitrary comparison. No theorem
other than the item is postponed, and no additional hypothesis or statement
correction was introduced. The historical stage-1 PASS has not been presented
as a stage-2 attachment or as this reading's independent approval.

## Validation

The prescribed `scompile.py` compiled the retained theorem in both its sandbox
and library forms without errors or warnings. The repaired normal dry run passed:
`OK (dry run): commit 4ceed00a2b passes the preflight and compiles; nothing pushed`.
It staged only the item node, its single theorem module, and this report.
The initial dry run on the saved packet was superseded: removing the duplicate
module while that run was still active made it fail when reading the removed
file. The fresh dry run above ran on the complete repaired packet and passed.
The final normal delivery follows this successful preflight and compile.
