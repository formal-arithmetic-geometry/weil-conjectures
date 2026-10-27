## Worker report

The module `Sheaf.AlgebraicGeometry.RepresentableStackQuasicompactTests` states
`CategoryTheory.representable_stack_quasicompact_tests`, with `sorry` as its sole proof.
It gives exactly the equivalence of Stacks Tag 050T, conditions (1) and (2).
The existing node is unchanged except for its `lean` field. No new nodes, dependency
repairs, or statement correction are needed. No statement is disputed.

Clause-by-clause reading:

- Base scheme S: `{S : Scheme.{u}}`, from `Mathlib.AlgebraicGeometry.Scheme`.
- Universes: all levels `u v₁ w₁ v₂ w₂ v₃ w₃` are explicitly bound. F and G have
  independent hom/object universes. The right-hand predicate is explicitly instantiated
  at all seven levels, allowing the test bounds to enlarge by `v₃` and `w₃`, exactly
  as its recorded definition does. No equality of distinct universes is imposed.
- Algebraic stacks A and B: `F` and `G` are `BasedCategory (Over S)`, with hypotheses
  `hF : IsAlgebraicModuliStack F` and `hG : IsAlgebraicModuliStack G`.
- Morphism h over S: `f : BasedFunctor F G`.
- Representability by algebraic spaces: `hrep : IsRepresentableByAlgebraicSpaces f`.
  This tests every scheme map using `HasSpaceBaseChange`, not an arbitrary space
  and an unrelated projection.
- Condition (i): `∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
  ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
  HasSpaceBaseChange f T t Z p ∧ AlgebraicSpace.MapIsQuasiCompact p`.
  The presentation explicitly identifies the base-change projection over T. Choosing
  any such presentation gives the same property, since quasi-compactness is invariant
  under isomorphism over T; this existential form makes no additional atlas choice.
  The inherited `MapIsQuasiCompact` uses affine-scheme tests and compactness of the
  point space. For algebraic spaces this is the equivalent definition in 03HE/03KG,
  as specified in the recorded StackQcqsMorphism dependency; it includes all the
  quasi-compact-space tests in the node, not just tests of the original source by
  quasi-compact schemes.
- Condition (ii): `IsQuasiCompactAlgebraicModuliMap.{u, v₁, w₁, v₂, w₂, v₃, w₃} f`.
  Unfolding the recorded definition quantifies over every algebraic stack V in the
  common enlarged bound, every `BasedFunctor V G`, algebraicity and quasi-compactness
  of V, and concludes `IsQuasiCompactModuli (moduliTwoFiberProduct f g)`.
- Equivalence: `↔`. The final agreement with stack-morphism quasi-compactness is
  literal use of that existing predicate as the right side.
- No separation, finite-type, or Deligne--Mumford hypothesis occurs.

Dependency declarations used (source signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, with its `IsSmoothModuliAtlas` definition.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`:
  `CategoryTheory.IsQuasiCompactAlgebraicModuliMap`, `IsQuasiCompactModuli`;
  the scheme test uses its already imported `AlgebraicSpace.MapIsQuasiCompact`,
  defined in `Sheaf.AlgebraicGeometry.ProperCurveModuli`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsRepresentableByAlgebraicSpaces`, `HasSpaceBaseChange`,
  `discreteModuli`, `BasedFunctor`, and `moduliTwoFiberProduct` (through the
  right-hand predicate). In `HasSpaceBaseChange`, the equivalence is to
  `moduliTwoFiberProduct t f`, and the two-isomorphism fixes the projection to T;
  the reversed factor order from the statement is canonically equivalent.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`.
- The size node is a convention, implemented by these explicit universes.

The proof docstring contains all four steps of the node's proof: spaces as stacks,
space/stack quasi-compactness agreement, forward via a quasi-compact smooth atlas
and surjection, reverse via all quasi-compact algebraic-space tests and reassociation.
All currently recorded proof-dependency modules are imported, with plain imports
when only needed for stage 3. `lem-sfb-fibred-groupoid-representable-smooth-calculus`
has no current Lean record and hence no recorded module to import; its use is
retained by name in the proof docstring. The continuous-image Mathlib leaf is
imported via `Mathlib.Topology.Compactness.Compact`.

Edge cases checked before writing: empty base or test scheme; empty source stack;
identity maps and discrete scheme/space stacks; non-quasi-compact test scheme;
non-separated and non-DM stacks; stacks with nontrivial automorphisms; independent
endpoint universes and larger test universes. There are no nonemptiness assumptions.
In particular T is arbitrary in (i), whereas only V must be quasi-compact in (ii).
For the empty stack the empty scheme is a valid quasi-compact atlas. Automorphisms
are retained by the total-category two-fibre product rather than replaced by
isomorphism classes. A quasi-compact source alone is not substituted for
quasi-compactness of its map to T.

Searches actually run through `msearch.py NR lem-sfb-representable-stack-quasicompact-tests`:

- LeanFinder: "A representable morphism of algebraic stacks is quasi compact if and
  only if every quasi compact stack base change has quasi compact source".
  Eight results, all scheme quasi-compactness/base-change statements; no match.
- Loogle: `"QuasiCompact", "baseChange"`. One result,
  `AlgebraicGeometry.quasiCompact_isStableUnderBaseChange`; its endpoints are
  schemes and it is not this stack equivalence.
- grep: `representable.*quasiCompact|quasiCompact.*representable|quasi.compact.*algebraic.stack`.
  Zero Mathlib hits.
- LeanSearch: "Quasi compact representable stack morphisms are equivalent to quasi
  compact algebraic stack base changes". Eight hits, all scheme morphism properties;
  no match.
- Direct `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for representable /
  quasiCompact combinations and quasi-compact algebraic stacks found the consumer
  `AlgebraicStackQcqsPermanence`, existing predicates, and a space affine-test lemma,
  but no copy of this equivalence. `grep -rn` of the node id under WeilConjectures
  found nothing. Exact declaration-name search in both trees and
  `dag/lean_names_upstream.json` found no existing declaration.

Source read: `literature/stacks-project/stacks-morphisms.tex`,
`lemma-characterize-representable-quasi-compact` (Tag 050T). Its two conditions agree
with the node. The typo in the last displayed product of its proof is already
corrected in the node's proof; no change to the statement is necessary.

Validation: `scompile.py NR lem-sfb-representable-stack-quasicompact-tests` compiled
the module in sandbox and library modes cleanly under the default 60-second limit.
The final compile is rerun after the explicit upper universe parameters were added.

## Second reading by NR

This section records an in-thread second reading; no independent worker was started,
as the dispatcher explicitly prohibits starting other agents. The maintainer's
independent delivery review remains separate.

Reopened the node, its dependency definitions, the source Tag 050T and the finished
module. Matched the base, both algebraicity hypotheses, representability, arbitrary
scheme test, actual base-change projection, quasi-compact-map condition and the
stack-test predicate clause by clause as listed above. The initial draft left the
upper test universes inferred; the final signature explicitly names `v₃,w₃` in
`IsQuasiCompactAlgebraicModuliMap` so its test range can enlarge. The proof docstring
was expanded to retain the full four-step DAG argument. No extra finiteness,
separation, representability-by-schemes, or DM condition was found. There are no
private definitions, local instances, hollow constructions, or proved theorems.
