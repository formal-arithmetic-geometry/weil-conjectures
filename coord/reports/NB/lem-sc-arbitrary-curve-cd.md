## Worker report

The module states `AlgebraicGeometry.torsionEtaleCohomologicalDimensionLE_of_dim_le_one`.
It introduces a field `k` with `[Field k] [IsAlgClosed k]`, a scheme `X`, and its structure
morphism `f : X ⟶ Spec (.of k)`. The instances `[IsSeparated f]`, `[LocallyOfFiniteType f]`,
and `[QuasiCompact f]` render separated and finite type. The explicit hypothesis
`hdim : topologicalKrullDim X ≤ 1` renders dimension at most one. The conclusion is a
case split: `IsAffine X ∧ Scheme.HasTorsionEtaleCohomologicalDimensionLE X 1` is exactly
the affine value `e = 1`, while `¬ IsAffine X ∧ ... X 2` is exactly the non-affine value
`e = 2`; the two cases are exhaustive and disjoint. The proof is `sorry` as required.

The statement dependency `def-sc-etale-torsion-cd` is used through
`Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`, declaration
`AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE`. The conventions node
`def-weil-pbc-scheme-conventions` is a convention-only node and has no declaration/module.

Edge cases checked: the dimension inequality includes the empty scheme (`topologicalKrullDim
empty = ⊥`); zero-dimensional schemes satisfy it; affine and non-affine cases are exhaustive;
`c = 1` and `c = 2` are natural-number bounds; no nonemptiness, reducedness, or uniform
annihilator hypothesis is added.

Searches: `msearch.py ... leanfinder` for “torsion etale cohomological dimension of separated finite type curve” returned eight unrelated cotangent/formally-etale hits and no match; `msearch.py ... loogle` for “cohomological dimension torsion etale scheme” returned zero hits (unknown identifier); `msearch.py ... grep` for `torsion.*cohomological|arbitrary.*curve.*cd` in Mathlib/AlgebraicGeometry returned zero hits. `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf` found only the dependency definition and no theorem.

No STATEMENT-DISPUTED flag or node fault.

## Earlier second reading (a previous round; superseded)

Read the node and module independently. Every source hypothesis is represented: algebraically
closed field, separated finite-type structure morphism, and dimension at most one. The
conclusion's two disjuncts encode the node's definition of `e` without requiring a decidable
instance for `IsAffine`; no clause is omitted or strengthened. The dependency declaration is
used directly, and the theorem has only a `sorry` proof.


## Second reading by NB

Independent second reading, 2026-10-15. Read the complete node and its three expanded proof
steps, the primary blueprint source
`sec-smooth-purity/sk-prop-sf-cbc/lem-sc-arbitrary-curve-cd.md`, and Stacks
`algebra.tex`, `lemma-separable-smooth` (Tag 00TV). The tag assumes a field, a finite-type
algebra, a prime, and separability of its residue field; it is the regular-to-smooth
criterion used in normalization, not the statement of this entire curve bound. The blueprint
introduces no additional standing hypotheses.

Object/hypothesis/conclusion list, matched item by item:

- Ground field k: `{k : Type u} [Field k] [IsAlgClosed k]`. Exactly an arbitrary
  algebraically closed field; no characteristic restriction. PASS.
- Scheme over k: `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))` supplies its structure map.
  The explicit structure-map encoding is the same scheme-over-field notion used by the
  recorded affine-curve and zero-dimensional comparison declarations; it adds no condition
  on X. No change to this acceptable encoding. PASS.
- Separated: `[IsSeparated f]`, the closed-diagonal property in Mathlib. PASS.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the two parts specified
  by the dependency `def-weil-pbc-scheme-conventions`. No independent Noetherian, smooth,
  proper, integral, reduced, connected, or nonempty assumption. PASS.
- Dimension at most one: `(hdim : topologicalKrullDim X ≤ 1)`, using Mathlib's
  `WithBot ℕ∞` dimension of the underlying topological space. PASS.
- e = 1 if affine: the first disjunct is
  `IsAffine X ∧ Scheme.HasTorsionEtaleCohomologicalDimensionLE X 1`. PASS.
- e = 2 otherwise: the second disjunct is
  `¬ IsAffine X ∧ Scheme.HasTorsionEtaleCohomologicalDimensionLE X 2`. These cases are
  exhaustive and disjoint, so the disjunction is exactly the conditional upper bound, not
  an equality of cohomological dimensions or an affine characterization. PASS.
- Meaning of the bound: opened the dependency module
  `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`. Its definition
  `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE` quantifies over every
  `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`, assumes precisely `F.IsTorsion`,
  and for every `q : ℕ` with `c < q` asserts `Subsingleton` of ordinary derived global
  sections cohomology of F in degree zero. Opened `Etale.cohomology` in
  `SixFunctors/Etale/Derived/LowerShriek.lean`: it is right derived global sections
  followed by the homology functor. Thus there is no compact-support or uniform-annihilator
  substitution. PASS.

Dependencies: opened both statement-dependency nodes. The scheme-conventions node explicitly
fixes no new notion; its finite-type and affine clauses agree with the imported Mathlib
notions. The cohomological-dimension dependency is a real universal-vanishing predicate,
with no data sorry. Opened the recorded proof-dependency declaration signatures too, including
the finite-support comparison (degree n+2), smooth-normalization criterion, affine smooth
connected curve vanishing, derived-cohomology smooth curve bound, finite direct-image
exactness, stalk/torsion characterizations, and zero-dimensional cohomology. The curve-bound
steps really concern locally torsion sheaves, while the finite-support comparison concerns
arbitrary abelian sheaves. No missing notion or unusable statement dependency was found;
there are no new nodes or dependency modules in this delivery, and no statement correction
or citer verdicts to review.

Edge cases: the empty scheme has dimension bottom and is not excluded; dimension zero and
nonreduced schemes remain included. The affine bound requires vanishing only in degrees
q ≥ 2 and the other bound only in degrees q ≥ 3; no vanishing of H^0 or H^1 is asserted.
The zero sheaf is included. All characteristics and characteristic-primary torsion are
included. There is no finite index set in the statement; the empty component union in the
proof has zero cohomology. The universe u is arbitrary and the site coefficient universe
u+1 is the recorded dependency's convention, not a new size restriction.

Independent duplicate searches (2026-10-15): `msearch.py ... leanfinder` with
“Higher etale cohomology of a singular algebraic curve vanishes above two, or above one
when affine” returned eight formally-etale/cotangent hits, no match.
`msearch.py ... loogle '"CohomologicalDimension"'` returned zero hits.
`rg -i 'cohomological.?dimension|cohomology.*curve|curve.*cohomology'` over the pinned
Mathlib, WeilConjectures, and project Sheaf trees found nearby declarations, which I opened:
`Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed` supplies only the general 2d bound;
`IsCurve.subsingleton_sheafH_of_three_le` and
`IsCurve.subsingleton_sheafH_of_two_le_of_isAffine` separately state bounds in the Ext-based
`Sheaf.H` model. Neither single declaration states the present conditional bound in the
recorded ordinary derived-section predicate; a cohomology comparison and packaging are
still needed. Thus no exact existing declaration replaces this module. No duplicate notion
is introduced; the existing torsion-cohomological-dimension predicate is used directly.

Mismatches repaired: (H8) the module/declaration attributed the whole result to Tag 00TV;
replaced this with its actual blueprint source, explaining the tag's role. The proof docstring
was too compressed to transfer the node's argument: expanded all three steps, including local
torsion preservation, dimension-zero/empty cases, and why the comparison applies for q > e.
(Stage 2 rule 7) added non-public imports of every recorded proof-dependency module, deduplicated
by module. Preserved the mathematical signature, the node's statement, and all dependency lists.
Updated `lean.statement` to the exact multiline signature from the file. No proofs were added;
the only theorem body remains `by sorry`, with no definitions, axioms, private copies, or
file-local notation/instances. All variables and the sole universe are explicitly bound.
All lines are at most 100 characters.

Validation: server `scompile.py NB lem-sc-arbitrary-curve-cd` compiled the dependency overlay
and the item cleanly (1.3 s and 2.7 s), nice 19, two threads, 60 seconds per file; no warnings.
