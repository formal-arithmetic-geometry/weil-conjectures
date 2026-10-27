## Worker report

Repair of returned immutable head ce8ccc3e8aeb, H2/H12: the item and the new hull
node now cite `def-sfb-artin-square-zero-transport` for `squareZeroMap` and
`isoClassesMap`, instead of citing `lem-sfb-artin-rs-tangent-tensor` as a statement
dependency. The new definition node uses an `existing: true` record for those exact
two definitions in `Sheaf.AlgebraicGeometry.ArtinRSTangentTensor`, as explicitly
permitted by the return. No declaration is copied or moved. The theorem remains
only a proof dependency of the item; its conclusion is not used to type the hull.
The Lean signatures and bodies are unchanged from the reviewed head, whose
mathematical clauses the maintainer accepted. The current main item has no Lean
record and its original four statement dependencies; its current metadata and split
are preserved, with only lean and the authorized added definition dependencies.


The module `Sheaf.AlgebraicGeometry.SchlessingerGroupoidHullCriterion` states
`AlgebraicGeometry.ArtinDeformation.schlessinger_groupoid_hull_criterion` with
one postponed proof. No mathematical statement was corrected. A definition module
`Sheaf.AlgebraicGeometry.ClassicalDeformationHull` supplies the missing hull interface.
All its data are explicit; it has no postponed theorem or hollow construction.

Clause-by-clause correspondence with the item:

- The field is `{k : Type u} [Field k]`. No restriction on characteristic is made.
- `TestCategory k k` is exactly the augmented Artinian local k-algebra category.
  `IsTestAlgebra` supplies locality, Artinian DCC, and the residue marking. Its arrows
  are the augmentation-preserving k-algebra maps; these are local. All rings and
  tests use one ambient universe containing k, with independent fibre object and
  morphism universes `w` and `v`. Enlarging the ambient universe covers larger tests.
- The groupoid pseudofunctor is `D : CofibredGroupoids.{u, v, w} k k`; this retains
  the pseudofunctor constraints and invertibility of all fibre arrows.
- The terminal residue groupoid is `hpre : IsPredeformation D`, including nonemptiness
  and the unique arrow between any two residue objects.
- Every specified pullback equivalence is `hRS : IsRimSchlessinger D`. Its definition
  uses the literal fibre-product test, canonical comparison functor, and Mathlib's
  categorical pullback with triples and compatible arrow pairs.
- `isoClasses D A` is the actual quotient by isomorphism; `isoClassesMap D f` is
  quotient transport induced by `push D f`. `tangentSet D` is that same quotient at
  `squareZeroTest k`, namely k[epsilon]. No substitute tangent carrier is introduced.
- `[AddCommGroup (tangentSet D)] [Module k (tangentSet D)]` and `hoperations` specify
  exactly the stated deformation vector operations. Scalars use `squareZeroMap`
  for `a • LinearMap.id`; sums use transport from `k[k × k]` along `fst + snd`,
  matched with the two projections. Under predeformation and (RS), every pair of
  classes is obtained by these projections, uniquely, so the equations characterize
  the addition, rather than merely constrain a subcollection of pairs. The existing
  `artinRS_tangent_tensor` supplies existence of these vector structures.
- The finite dimension assumption is `[FiniteDimensional k (tangentSet D)]`.
- Existence of the ring is `∃ B : CompleteLocalAlgebra k k`: this structure contains
  the actual commutative k-algebra, `IsLocalRing`, `IsNoetherianRing`, maximal-ideal
  `IsAdicComplete`, and the specified residue-field k-algebra equivalence.
- `η : ClassicalClassMap D B` is a family of maps on exactly `LocalMap B A`, together
  with naturality for every commuting triangle. This is the usual natural map
  h_B → F written componentwise. Local maps are automatically continuous: their
  images of powers of the source maximal ideal lie in the same powers of the target
  maximal ideal; one target power is zero, and hence the inverse image of zero
  contains an open ideal. Conversely every local continuous marked map is included.
- `IsClassicalHull η` first quantifies over EVERY test surjection, then over every
  matching pair `(a,y)`, and produces a preimage `b` with both required equalities.
  This is precisely surjectivity onto the displayed fibre product, including identity
  surjections, not only small extensions.
- Its second clause existentially equips `LocalMap B (squareZeroTest k)` with vector
  structures satisfying `HasLocalMapTangentOperations B`, and gives a linear
  equivalence whose underlying map is exactly `η.app` at the dual numbers.
  The operations are fixed by the epsilon coefficient of every value on every
  element of B. The first coefficient is already forced by the marking. Thus these
  structures cannot be arbitrary transports of vector structures across a bijection.
- `classicalZeroArrow` is the actual scalar arrow `k → k[epsilon]`, built from
  `Algebra.ofId`. For each `x₀` the implication assumes `Subsingleton (Aut ...)`
  of its pushforward. A group is trivial exactly when its carrier is subsingleton.
  The theorem quantifies over the residue object, so it includes any chosen x₀;
  it does not require simultaneous triviality for all residue objects as an extra
  premise. They are in any event uniquely isomorphic by `hpre`.
- The consequent quantifies over EVERY complete marked B and EVERY map η satisfying
  `IsClassicalHull`. `IsClassicalClassIso η` gives component inverses, both inverse
  identities, and the explicit naturality equation for those inverses. This is
  precisely the final natural-isomorphism conclusion.

Dependencies read and reused:

- `Field`: Mathlib.Algebra.Field.Defs, line 180, extending CommRing and DivisionRing.
- `CategoryTheory.Category`: Mathlib.CategoryTheory.Category.Basic, line 234;
  the full signature and identity/associativity laws were read.
- `IsNoetherianRing`, `isNoetherianRing_iff`:
  Mathlib.RingTheory.Noetherian.Defs, lines 196–200, ideals finitely generated.
- `AdicCompletion`, `IsAdicComplete`: Mathlib.RingTheory.AdicCompletion.Basic,
  lines 171 and 56. These are used through `CompleteLocalAlgebra.complete`.
- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`, namespace
  `AlgebraicGeometry.ArtinDeformation`: `TestCategory`, `CofibredGroupoids`, `fibre`,
  `push`, `IsPredeformation`, `IsRimSchlessinger`, `isoClasses`, `tangentSet`,
  `squareZeroTest`, `CompleteLocalAlgebra`, `LocalMap`, `residueTest`, and `ring`.
  Read the entire module, including canonical comparisons and formal evaluation.
- `Sheaf.AlgebraicGeometry.ArtinRSTangentTensor`: `squareZeroMap`, `isoClassesMap`,
  and `artinRS_tangent_tensor`. The construction and full tangent-tensor signature
  were read. The first two are directly used; the theorem is proof input.

The main module imports the recorded modules of all stated proof dependencies,
including completed polynomial tests, least liftable ideals, complete quotients,
descending ideal topology, local test algebra factorization, essential small
extensions, and the tangent-ring-lift criterion. At preparation time
`lem-sfb-artin-formal-filtration-comparison`,
`lem-sfb-schlessinger-automorphism-kernel`, and
`lem-sfb-deformation-marked-lift-torsor` had no Lean records, so their imports
are omitted, with their precise uses retained in the proof docstring.

Sources read: formal-defos.tex at 06J7, 06IX (including the classical-case paragraph),
06IY (definition of hull), 06IZ, 06JL (full induction), and 06K0 (setoid reduction).
The current blueprint unit at literature/blueprint/latest was read. This is a
supporting node, not a change of the six-functor unit statement.

Edge cases checked before implementation: d=0 (ring k can be the hull, and all
coefficient operations remain meaningful); A=k; identity surjections and zero kernel;
nontrivial automorphism examples (the rigidity conclusion remains conditional);
any characteristic; non-skeletal terminal residue groupoid; arbitrary fibre universes;
the zero ring is excluded automatically by its specified residue field k.
The continuity omission from the LocalMap data is an equivalence, not an added or
dropped case. The linearity condition is not replaced by a bare tangent bijection.

Searches actually run through msearch.py:

- LeanFinder: `Schlessinger criterion deformation groupoid hull finite dimensional
  tangent space prorepresentable`: eight results about formal smoothness and cotangent
  objects; none is this statement.
- Loogle: `"Schlessinger"`: zero hits.
- Mathlib grep: `Schlessinger|IsHull|miniversal|CofibredGroupoids`: zero hits.
- LeanSearch: `deformation functor hull Schlessinger prorepresentability`: eight
  general representability declarations, none this hull criterion.
- For the missing hull definition, LeanFinder and LeanSearch with query
  `Hull natural map from local hom functor of complete local algebra to isomorphism
  classes of deformation groupoid tangent isomorphism`: eight unrelated ring/map
  results each. Their complete outputs are recorded in the new node.
- Mathlib grep: `ClassicalClassMap|IsClassicalHull|HasClassicalTangentOperations|deformation.*hull`:
  zero hits. Direct rg of lean/Sheaf and lean/WeilConjectures for those same terms
  returned no matches. Broader searches for Schlessinger, ArtinDeformation, and Hull
  located the reused Artin framework but no hull interface or exact criterion.
- Direct node-id search of lean/WeilConjectures and dag/lean_names_upstream.json:
  no occurrence. DAG searches found the target and its consumers but no definition
  of a classical deformation hull. `blueprint_refs.py search hull` found two unrelated
  localizing-hull nodes; `search deformation` found deformation-to-the-normal-cone
  nodes. `ancestor` reported null, as in the inherited blueprint record.

Validation: both delivered modules compiled individually through scompile.py in
one dependency-ordered call, cleanly. `autoImplicit false` is set in both modules.
The expected sorry proof is the only postponed declaration in this delivery.
No node fault or STATEMENT-DISPUTED issue was found.

## New nodes

`def-sfb-artin-square-zero-transport` records the existing plain definitions
`AlgebraicGeometry.ArtinDeformation.squareZeroMap` and
`AlgebraicGeometry.ArtinDeformation.isoClassesMap`. It owns their definition-node
interface via the reviewer's `existing: true` option, with no new module or duplicate.
The former quantifies over the Noetherian coefficient ring R, finite-type residue
field k, finite-dimensional V and W, and linear map f, and constructs the marked
arrow `(a,v) ↦ (a,f v)`. The latter quantifies over any groupoid pseudofunctor and
any test arrow, and sends the actual isomorphism class `[x]` to `[g_*x]` by
`Quotient.map`. Neither assumes predeformation, (RS), or any tangent-tensor result.
The two full signatures, docstrings, and implementations were read. Their existing
module imports Mathlib's square-zero and quotient machinery and the recorded test
category definitions. The new node cites those definition prerequisites, and both
consumers cite this node. The old theorem record requires no §1(B) change because
nothing is moved: the return expressly allowed this existing-record alternative.

Searches for the transport node were run during this repair: LeanSearch and
LeanFinder queried `linear map induces map on square zero algebras and functor
induces map on isomorphism classes`; each returned eight hits. LeanSearch found
`TrivSqZeroExt.map`; LeanFinder found square-zero extension and unrelated linear
maps. Mathlib grep `squareZeroMap|isoClassesMap|TrivSqZeroExt.map|isIsomorphicSetoid`
returned eleven hits, including `isIsomorphicSetoid` and uses of `TrivSqZeroExt.map`.
These Mathlib primitives are already used by the exact project definitions, so the
record reuses the latter. Project rg found the exact two definitions at lines 35
and 65 of ArtinRSTangentTensor, no upstream WeilConjectures counterparts. DAG rg
found the theorem record and specialized geometric/marked-stack maps, but no
abstract definition node for both transport operations. `blueprint_refs.py search
square-zero` found only an unrelated disjointness setup; `ancestor` again returned
null. The complete tool outputs are included in the new node's mathlib_searches.
Source read: formal-defos.tex, square-zero paragraph preceding definition-S1-S2,
section-tangent-spaces-functors, remark-predeformation-functor, and 06IG. Edge cases:
zero V or W, zero and identity f, empty groupoid fibres, arbitrary g and arbitrary
characteristic all remain included in the existing definitions.


`def-sfb-classical-deformation-hull` defines the natural map h_B → π₀ D, its hull
property, its natural inverse, the two canonical tangent-operation predicates, and
the canonical zero-section arrow. It builds on the existing test-category and tangent
transport nodes; it does not redefine either. The source is Stacks formal-defos,
06HC/06HR/06IG/06IC/06IY/06IZ/06JL and the infinitesimal-automorphism section.
The three search kinds and project/DAG/blueprint searches above found no existing
hull interface. The blueprint ancestor is null with the full inherited via chain.

## Second reading by Q37

Repair rereading for H2/H12 checked both JSON statement-dependency lists and the
existing two helper definitions. The item has its original four dependencies plus
the Artin test definition, square-zero transport definition, and hull definition.
The hull node cites the square-zero transport definition instead of the theorem.
There is no statement-dependency edge to the tangent-tensor theorem in either node.
The item's proof dependency on that theorem is retained. The added transport node's
Lean record names exactly the two existing definitions, and its TeX describes
exactly their inputs and constructions, including all finite-dimensional parameter
spaces and arbitrary fibre groupoids. The Lean files are unchanged because the
return found all mathematical clauses correct. The following earlier clause review
continues to apply; this repair supplies the missing DAG ownership rather than
altering the statements.


A separate clause-by-clause rereading of the node and both final files checked the
field and test category, pseudofunctor coherence, terminal residue groupoid, full
(RS), quotient tangent set, canonical scalar and addition operations, finite
dimension, complete Noetherian marked ring, naturality, every-surjection lifting,
linear tangent equivalence, the actual zero-section pushforward, and universal
quantification over hulls. No mathematical mismatch was found. The source references
for the definition of a hull were corrected from 06IX to 06IY, and the zero-section
source now names the infinitesimal-automorphism section rather than mislabelling
06JZ as a definition. The compiler required explicit addition on the named tangent
carrier because isoClasses unfolds its abbreviation; this changes no operation.
This reading was performed by the same dispatcher-started worker: the brief
explicitly prohibits starting another agent, so no independent reader is claimed.
The maintainer's independent review remains required.
