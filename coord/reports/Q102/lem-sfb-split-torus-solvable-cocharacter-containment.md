## Worker report

The main module `Sheaf.AlgebraicGeometry.SplitTorusSolvableCocharacterContainment`
states `AlgebraicGeometry.splitTorus_solvable_cocharacter_containment` with its
whole proof postponed by `sorry`. No existing definition or theorem was changed.
The helper module `Sheaf.AlgebraicGeometry.AdjointCharacterWeightVectors` has two
real definitions and no postponed proof. The natural-language item statement is
unchanged; `stmt_deps` gains the new weight-vector definition, a new definition node
recording the existing orbit-extension predicates, and the existing Lie-algebra
definition owner. It does not cite the limit-smooth-structure theorem as a
statement dependency.

Source read: Milne, *Algebraic Groups* (2017), Definition 21.26, Proposition 21.29,
Theorem 21.32 and Corollary 21.33, printed pp.433--435; Theorem 12.12 and Remark
12.13, pp.234--235. The current blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`
was also read. This is a supporting input along the item's inherited alteration
and split-flag chain, not the blueprint unit's own statement.

Hypotheses and clauses, matched individually:

| Node text | Lean rendering |
| --- | --- |
| Arbitrary field k | `{k : Type u} [Field k]`; no algebraic closure, infinitude, perfectness or characteristic assumption on k |
| k-group schemes G, T and V | `G T V : Grp (Over (Spec (.of k)))` |
| G reductive: smooth affine finite type, geometrically connected, no geometric smooth connected normal unipotent subgroup | `hG : ReductiveTorusCentralizer.IsReductive G`, the recorded definition, including the faithful geometric matrix definition of unipotence |
| T is a maximal torus subgroup of G | `i : T ⟶ G` and `hT : ReductiveTorusCentralizer.IsMaximalTorus i`; this definition includes closed subgroup inclusion and the torus condition |
| T is split of some finite rank, including zero | `hSplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r)` |
| V is a closed subgroup of G | `j : V ⟶ G` and `hV : IsClosedSubgroupScheme j.hom.hom` |
| V is smooth | `[Smooth V.X.hom]` |
| V is connected | `[ConnectedSpace V.X.left]` |
| V is solvable | `hSolvable : SolvableGroupStructure.IsSolvable V`; its finite normal series with commutative quotients is the dependency node's equivalent formulation of termination of scheme-theoretic commutators |
| V contains T | `tV : T ⟶ V` and `hTV : tV ≫ j = i`; the witness is a group-scheme factorization of the given subgroup inclusions |
| No maximality of V | No Borel or maximal-solvable hypothesis occurs |
| Lie(G) is the identity tangent space | `GrpObj.Lie G.X`, with the existing `GrpObj.tangentPoint` giving the actual dual-number point |
| Characters are group-scheme maps T → G_m | `chi : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k)` |
| Phi consists of nonzero characters with nonzero adjoint weight space | `chi.hom.hom ≠ 1` and `∃ v : GrpObj.Lie G.X, v ≠ 0 ∧ v ∈ AdjointCharacter.weightVectors i chi`; nonzero vector existence is exactly nonzeroness of the character-weight subspace |
| A k-defined cocharacter G_m → T exists | `∃ lam : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ T` |
| Each alpha in Phi pairs to a nonzero integer | First conjunct: for each such `chi`, `∃ n : ℤ, n ≠ 0 ∧ lam.hom.hom ≫ chi.hom.hom = (𝟙 (StandardGroupSchemes.multiplicative k)) ^ n`; this is equality of morphisms, so it says alpha(lam(t)) = t^n on every algebra |
| V is contained in P_lam as subgroup functors | Second conjunct: for every `A : CommAlgCat.{u} k` and `v : StandardGroupSchemes.affine k A ⟶ V.X`, its image `v ≫ j.hom.hom` belongs to `CocharacterLimit.parabolicPoints (lam ≫ i) A` |
| P_lam uses extension from G_m,A to A^1_A | The reused `parabolicPoints` is existential `IsOrbitExtension`: equality after the polynomial-to-Laurent open immersion on A × A^1, with the actual conjugation morphism on A × G_m. By the fibre-product universal property this is precisely an A-morphism A^1_A → G_A extending the orbit |
| Empty Phi permits lam = 0 | Last conjunct: if no nontrivial character has a nonzero weight vector, `lam.hom.hom = 1`, the trivial group morphism (additively the zero cocharacter) |

The new weight definition tests `i(s_epsilon) v_A i(s_epsilon)^-1 = chi(s) v_A`
for every commutative k-algebra A and every A-point s of T. It is a set of
vectors in the actual k-tangent space, so no arbitrary representation, root
system, map, or weight decomposition is an extra input. It is exactly the usual
character eigenspace under conjugation. Scalar multiplication after extension
is implemented by substitution epsilon ↦ c epsilon, rather than by differentiating
the character. The algebra universe equals the field's and includes the universal
coordinate algebras of these schemes; no independently smaller test universe is
introduced.

Dependency declarations used (their complete signatures and docstrings were read):

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and `Grp`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`; the bundled homomorphisms use its group-scheme convention.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`, through the
  recorded algebraic-group and reductivity predicates.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `MultiplicativeType.splitTorus`,
  `IsTorus` and `baseChange`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `multiplicative`, `affine`,
  `map` and the recorded group structure.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `IsSolvable`, `IsAlgebraic`,
  `IsUnipotent`, the latter two through reductivity.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`, through
  the recorded geometric torus and reductivity predicates.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic` and `.Lie.Ring`:
  `GrpObj.Lie`, `GrpObj.tangentPoint`, already closed upstream under `sk-d-tangent`.
- `Mathlib.Algebra.DualNumber` and `WeilConjectures.Mathlib.Algebra.DualNumber`:
  `DualNumber`, `DualNumber.scale`, `DualNumber.mapAlgebraMap`.
- `Sheaf.AlgebraicGeometry.RhoSectionModuleData`: `RhoSection.characterValue`.
- `Sheaf.AlgebraicGeometry.CocharacterLimitSmoothStructure`:
  `CocharacterLimit.IsOrbitExtension`, `parabolicPoints`.
- `Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality` is a plain proof
  import; its `multiplicative_character_antiduality` is the recorded proof input.
  The other five proof-dependency nodes have no recorded Lean module in the read
  clone and are not imported. All six inputs remain named in the proof docstring.

Edge cases checked before writing and on the completed statements:

- `G = T`, including rank zero: conjugation has only the trivial character;
  Phi is empty, lam is trivial, and P_0 is the whole group by the constant extension.
- `V = T`: no maximality requirement forces V to be a Borel.
- Opposite Borels in SL_2 require opposite chamber choices; the theorem chooses
  lam depending on V rather than fixing a positive chamber in advance.
- Finite fields: characters that agree on k-points remain distinct on universal
  algebra-valued points. In particular testing only k-points over F_2 would make
  all torus characters indistinguishable and would incorrectly classify infinitely
  many weights; the new definition avoids this.
- Positive characteristic: integer pairings remain integers, including nonzero
  multiples of the characteristic, since the assertion is a character equation,
  not a Lie-algebra eigenvalue obtained by differentiating a character.
- Imperfect fields remain allowed; reductivity is the geometric dependency predicate.
- Nonreduced algebras and the zero algebra are included in both weight equations
  and the orbit-extension containment. No reducedness or field-valued-only test appears.
- Negative exponents use the Hom group's integer power, so inverse characters are retained.
- The empty weight set does not impose an impossible nonzero-cocharacter condition.

Searches for the item: `msearch.py leanfinder` with “A smooth connected solvable
subgroup containing a split maximal torus lies in the limit subgroup of a regular
cocharacter” returned eight abstract Lie/Cartan facts, no scheme result.
`msearch.py loogle '"IsSolvable", "parabolic"'` returned zero hits.
`msearch.py grep 'cocharacter|BorelSubgroup|IsReductive|parabolic' AlgebraicGeometry`
returned zero hits. Source and project `rg -l -i 'cocharacter|limitSubgroup|tangentWeight|adjointWeight'`
located the limit-functor module and related geometric results, none stating this
containment. `rg` of the exact item ID in `lean/WeilConjectures` found no declaration.
The proposed declaration names were searched across Mathlib, WeilConjectures and
Sheaf with no collisions. `tools/blueprint_refs.py search cocharacter` found no
blueprint node. The new node's searches are recorded verbatim in its
`mathlib_searches`, including LeanSearch, LeanFinder, Mathlib grep, and local
source/project/DAG searches. `tools/blueprint_refs.py search weight` was inspected;
its hits concern other notions of weights and do not supply this universal adjoint
equation.

There is no statement dispute, statement correction, hollow definition, or
unusable recorded dependency requiring a replacement module. Both delivered
modules compiled cleanly through `scompile.py` against the live server build.

## New nodes

`def-sfb-cocharacter-limit-subfunctors` records the existing definitions
`AlgebraicGeometry.CocharacterLimit.IsOrbitExtension` and
`AlgebraicGeometry.CocharacterLimit.parabolicPoints`, with `existing: true` on
`Sheaf.AlgebraicGeometry.CocharacterLimitSmoothStructure`. There is no new Lean
module or duplicate definition for this node. Its statement defines orbit
extension on the product with the affine line and the subset of points admitting
an extension, on all commutative test algebras. Source: Milne Proposition 13.24,
p.262, and the definition of P_G(lambda), pp.263--264; these pages were read again
for the repair. The full signatures and bodies of both declarations were read.
`IsOrbitExtension` uses precisely the polynomial-to-Laurent open inclusion and
the conjugation formula, and `parabolicPoints` is its existential quantification.
The node makes no representability, smoothness or connectedness assertion and
uses no theorem or chosen theorem witness. Mathlib LeanSearch returned eight
unrelated abstract-group/representation hits, Loogle for `"parabolicPoints"`
returned zero, Mathlib grep returned zero. Source/project grep found the two
definitions only in the recorded module. DAG grep found them listed only on the
smooth-structure theorem; no separate definition owner existed. Blueprint search
for `cocharacter limit` found zero nodes. The exact results are in the new node's
`mathlib_searches`. This is the definition-owner repair prescribed in H2.


`def-sfb-adjoint-character-weight-vectors` defines the actual adjoint character
weight-vector set over arbitrary fields, using universal dual-number equations.
Its module supplies `AdjointCharacter.scaledTangentPoint` by the real composite
of existing dual-number algebra maps and Spec, and `AdjointCharacter.weightVectors`
by its set comprehension. Source: Milne Theorem 12.12 and Remark 12.13,
pp.234--235, and Definition 21.26, p.433, together with the existing tangent-point
construction. Searches are recorded as returned in the new node. The nearby
`def-sfb-torus-character-tangent-weights` intentionally tests only rational points
and its statement explicitly identifies them with true character weights only
over an algebraically closed field. It therefore does not give the required
arbitrary-field notion. The new definition does not duplicate it or alter it.
Existing character evaluation, scalar extension of dual numbers and tangent
points are reused. The item's existing `blueprint.from.node` is null, and
`blueprint_refs.py ancestor` independently reports null; the inherited chain and
place are retained, with the item prepended to `via`.

## Second reading by Q102

This is the worker's own second pass over the node and both completed files;
the dispatcher explicitly prohibits starting other agents, and the maintainer's
independent reading follows delivery. It is not claimed to be an independent
worker review. The pass matched every hypothesis and clause in the table above,
checked the real scalar-substitution map in `scaledTangentPoint`, verified the
conjugation order, checked that the Laurent coordinate is evaluated by the
existing `RhoSection.characterValue`, and checked that the orbit uses `lam ≫ i`.
It also checked the zero algebra, finite-field character distinction, the
empty-Phi implication and the absence of a Borel hypothesis on V. No further
statement change was necessary. The only theorem proof is exactly `by sorry`.


## Repair of return at fe9cd866c431

H2 is repaired by introducing `def-sfb-cocharacter-limit-subfunctors`, an
`existing: true` definition node for the two ordinary predicates already in
`Sheaf.AlgebraicGeometry.CocharacterLimitSmoothStructure`. The item now cites
this definition node in place of `lem-sfb-cocharacter-limit-smooth-structure`.
The same public import remains appropriate because it supplies the existing
definitions used by the signature; the theorem is not invoked. Neither delivered
Lean file is changed from the returned packet, and the main theorem's signature,
proof and natural-language statement remain exactly as reviewed. The new node
records the verbatim signature of `parabolicPoints` and lists both declarations.

The advisory is also addressed: `def-wf-lie-algebra-derivation` is added to the
item's and `def-sfb-adjoint-character-weight-vectors`' statement dependencies.
The weight-vector node explicitly cites that definition next to `sk-d-tangent`.
Its recorded public module is
`WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket`, declaring
`GrpObj.lieEquivTangent` and exposing `GrpObj.Lie`, its module structure and the
canonical tangent construction through its public imports. Those signatures and
docstrings were read. The broad recorded `GrpObj.Lie` definition applies to
group objects over any scheme, so no algebraic-closure or characteristic-zero
hypothesis has been added to this statement.

Current main was compared with the retained sandbox packet: the item differs
only in `lean` and the added statement dependencies; neither new definition node
from the previous packet had landed. The item was refreshed from current main
with the repaired `lean` and `stmt_deps` delta, retaining all other current-main
fields. The new orbit definition node was searched for and was absent. Delivery
will be rebuilt on current main by the prescribed wrapper. This is a substantive
node-ownership repair, not an unchanged re-push.

Second-pass repair check: the new definition statement agrees clause by clause
with the existing two predicate bodies. In particular q is a k-map from
Spec(A) times the affine line, whose product universal property is the equivalent
A-map into G_A. The equation is a morphism equation, so it retains all test
algebras. No regularity, subgroup containment, finite-field case, or empty-Phi
clause has changed. The maintainer's immutable-head reading already checked the
mathematics of both retained Lean files; the repair changes ownership metadata
only. The worker does not claim a separate independent-agent reading.
