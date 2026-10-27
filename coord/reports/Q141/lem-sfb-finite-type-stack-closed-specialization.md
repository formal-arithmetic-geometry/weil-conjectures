## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeStackClosedSpecialization` states
`CategoryTheory.finite_type_stack_closed_specialization`; its sole proof is `sorry`.
It constructs no replacement point space, topology, atlas, diagonal, or scheme property.
The node's mathematical statement and accepted split are unchanged.

Hypothesis and conclusion correspondence:

- Field k: `(k : Type u) [Field k]`, the declaration of def-weil-field.
- Algebraic stack over k: `F : BasedCategory.{v, w} (Over (Spec (.of k)))`
  and `hF : IsAlgebraicModuliStack F`. This is the general algebraic-stack predicate,
  not the Deligne--Mumford predicate.
- Quasi-compactness: `hqc : IsQuasiCompactModuli F`, exactly the smooth surjective
  quasi-compact scheme-atlas definition in def-sfb-stack-qcqs-morphism.
- Structural morphism locally of finite type on smooth scheme charts: `hft` quantifies
  over every `U`, chart `a`, and `IsSmoothModuliAtlas F U a`, and concludes
  `LocallyOfFiniteType U.hom`. No smoothness over k is asserted: it is the atlas map to F
  that is smooth. Together with hqc, this is the node's finite-type hypothesis.
- The diagonal is the canonical `moduliRelativeDiagonal (moduliBaseStructure F)`;
  its target is the 2-fibre product of the structural map with itself.
  For every scheme T mapping to that target, hdiag supplies its actual algebraic-space
  2-base change Z and projection p through `HasSpaceBaseChange`.
  `AlgebraicSpace.MapIsQuasiCompact p` expresses quasi-compactness and
  `AlgebraicSpace.MapToSchemeIsSeparated Z T p` expresses separatedness. These scheme
  base-change tests are equivalent to the diagonal properties: representable morphism
  properties are local on the target, and arbitrary stack tests descend from scheme
  atlases. The quasi-compact algebraic-space predicate is the same one reused by
  def-sfb-stack-qcqs-morphism (Stacks 03HE). Separatedness tests that the actual relative
  diagonal is a closed immersion, not that every etale source chart is separated.
- The point space is precisely `ModuliPoints F` with `moduliPointTopologicalSpace`,
  exposed by lem-sfb-stack-point-topology; these are existing field-object classes
  and the topology induced by all smooth surjective atlases.
- Noetherianity: `TopologicalSpace.NoetherianSpace (ModuliPoints F)`. Mathlib defines
  this as ACC on opens (equivalently DCC on closed subsets); it is not a scheme-only
  Noetherianity condition.
- Sobriety: for each closed irreducible C, `∃! x, IsGenericPoint x C`.
  Mathlib's `IsIrreducible C` includes nonemptiness, and `IsGenericPoint x C` means
  `closure {x} = C`. Thus both existence and uniqueness are present.
- Closed-point selection: for every `IsClosed C` and `C.Nonempty`, the conclusion
  is `∃ x ∈ C, IsClosed ({x} : Set (ModuliPoints F))`; the singleton is closed in the
  whole stack point space, not merely in C.
- No quasi-finite diagonal condition, no representability by schemes, and no
  nonemptiness of F is imposed.

Dependency declarations used (their full source signatures and docstrings were read):

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas` (def-sfb-algebraic-moduli-stack).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  its companion `QuasiCompact` was checked in Morphisms.QuasiCompact
  (def-weil-finite-type-morphism).
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: `IsQuasiCompactModuli`, together
  with its reused `AlgebraicSpace.MapIsQuasiCompact` (def-sfb-stack-qcqs-morphism).
- `Sheaf.AlgebraicGeometry.StackPointTopology`: `stack_point_topology`, and its
  public dependencies `ModuliPoints`, `moduliPointTopologicalSpace`,
  `moduliSchemePointMap` (lem-sfb-stack-point-topology).
- `Sheaf.AlgebraicGeometry.RelativeModuliInertia`: `moduliBaseStructure`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.MapIsQuasiCompact`,
  `AlgebraicSpace.MapToSchemeIsSeparated`. `HasSpaceBaseChange` and
  `moduliTwoFiberProduct` are the existing StablePointedModuliGroupoids constructions;
  `moduliRelativeDiagonal` comes from DmStackMorphismProperties, publicly imported
  by StackQcqsMorphism. Using that construction imposes no DM assumption.

The two already landed definition nodes `def-sfb-relative-moduli-inertia` and
`def-sfb-proper-curve-moduli` are added to stmt_deps to register the canonical structural
map and the existing separatedness predicate, as permitted by brief-stage2 section 5
(STMT_DEPS MAY GAIN LANDED NODES). No new node and no dependency repair is needed.
All other node fields are preserved except lean.

Plain proof imports register the recorded Mathlib proof dependencies:
`Mathlib.AlgebraicGeometry.Noetherian` (pqf-def-locnoeth, pqf-lem-locnoeth-lft,
and lem-weil-pbc-noetherian-scheme-closed-subsets-minimal),
`Mathlib.RingTheory.Noetherian.Defs` (def-weil-pbc-noetherian-ring),
and `Mathlib.Topology.Spectral.Basic` (def-weil-spectral-space).
The spectrum is already public from the statement imports (def-weil-affine-spectrum).
The proof node lem-sfb-qc-stack-spectral-point-space has neither a lean record nor
mathlib_match at the time of writing, so there is no recorded module to import;
it is retained verbatim in proof_deps and the theorem's proof docstring.

Source checked directly: literature/stacks-project/stacks-morphisms.tex,
lemma-locally-finite-type-locally-noetherian (06R6), lemma-Noetherian-topology
(0DQI), lemma-spectral-qc-diagonal-qc (0DQN), and lemma-sober-qs (0DQQ).
The source gives the Noetherian/sober assertions; choosing a minimal nonempty closed
subset and using uniqueness of its generic point gives the final clause.

Edge cases checked before writing:

- Empty stack: a smooth empty atlas is allowed, IsQuasiCompactModuli does not assert
  nonemptiness, its point space is Noetherian, and there are no nonempty irreducible
  or closed subsets to test.
- Empty C: the irreducibility/nonemptiness premises make both point assertions vacuous.
- Nonempty C with several components: the last clause chooses a minimal nonempty
  closed subset, not an irreducible component or a point generic in C.
- Positive-dimensional stabilizers (e.g. a finite-type classifying stack of a smooth
  affine group): no unramified/etale/quasi-finite diagonal premise excludes them.
- Arbitrary characteristic and finite/infinite/nonperfect fields: only Field is used.
- Universes u, v, w are explicitly bound and independent. Scheme/field tests live
  in the same u as k and the underlying big site; there is no smaller test universe
  or extra equality of object and morphism universes. `autoImplicit false` is set.

Searches made using the prescribed msearch wrapper:

- leanfinder: "A finite type algebraic stack over a field has a Noetherian sober space
  of points and every nonempty closed subset contains a closed point". Eight hits:
  scheme Noetherian/Artinian predicates and instances, no stack theorem.
- leansearch: "A finite type algebraic stack over a field has a Noetherian sober
  underlying topological space". Eight hits: scheme Noetherian/sober instances,
  finite spaces, abstract NoetherianSpace and finite-type algebra Noetherianity;
  none is the requested general algebraic-stack statement.
- loogle: `"AlgebraicGeometry", "NoetherianSpace"`. Five scheme-only hits, including
  IsNoetherian.noetherianSpace and affine variants. Their scheme signatures were read.
- grep (Mathlib/AlgebraicGeometry): `AlgebraicStack|stack.*Noetherian|Noetherian.*stack`.
  One hit, a bibliographic "Stacks: Noetherian Schemes" line; no match.
- rg in lean/WeilConjectures and lean/Sheaf for stack/Noetherian and finite-type-stack
  names: comments about Stacks tags, scheme results, and the consumer
  AdequateIntegralComparisonFinite; no declaration of this assertion. The consumer's
  actual signature was read; its diagonal tests reuse the same predicates as here.
- grep -rn for the item id in lean/WeilConjectures: no hit.
- rg in dag/lean_names_upstream.json: no matching existing stack theorem.

No STATEMENT-DISPUTED flag, node correction, or hollow definition is needed.

Validation: prescribed scompile.py compiled the module in sandbox and library module
modes on the live server (10.1 s and 11.8 s), with no errors or unexpected warnings.

## Second reading by Q141

A separate in-session reading compared the final node copy, the full Lean file, the
source lemmas, and the consumer AdequateIntegralComparisonFinite. No other agent was
started, as the dispatcher brief prohibits it; the maintainer's independent review is
still required. The field and stack binders preserve general algebraic stacks; hqc
and hft preserve precisely quasi-compactness and local finite type on smooth atlases;
hdiag keeps both properties of the actual diagonal base-change projection. The three
conclusion clauses preserve DCC, unique generic points, and ambient closed singletons.
In particular I checked that hft does not ask U to be smooth over k, and hdiag does not
use the erroneous source-chart test for separatedness or impose a scheme-valued diagonal.
The empty stack and empty closed subset are admitted. The signature stored in lean.statement
is extracted verbatim from the final file. No mismatch or statement change was found.
