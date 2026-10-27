## Worker report

The delivery states `AlgebraicGeometry.induced_composition_linkage` in
`Sheaf.AlgebraicGeometry.GroupScheme.InducedCompositionLinkage`. Its only theorem
has proof `by sorry`. Its docstring records all thirteen proof steps of the DAG,
including the double induction and the explicit change of Borel. Two helper
notions belong to this statement: `dominantInducedModule` is the actual existing
regular-function subspace with inverse right character, and
`IsRegularLeftTranslation` pins its coaction by evaluation over every algebra.
Neither constructs data using an existence assertion or a postponed proof.

Hypothesis and clause correspondence:

- Algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`.
- Semisimple simply connected group scheme: `S : Grp (Over (Spec (.of F)))`,
  `hS : IsSemisimpleGroupScheme S.X`, and `hsc`. The latter quantifies over every
  semisimple source and every surjective group-scheme homomorphism with finite
  kernel commuting with all source points over every commutative F-algebra,
  and concludes `IsIso f`. This is the exact form used by the rho dependency.
- The split maximal torus, Borel and inclusions: `T`, `B`, `iT`, `iB`, `j`,
  and `hTB : IsRhoBorelPair iT iB j`. The predicate includes maximality,
  a split-torus isomorphism (allowing rank zero), Borel and commuting inclusions.
- Unipotent radical: `U`, `iU`, `hUclosed`, `hUnormal`, `hUsmooth`,
  `hUconnected`, `hUunipotent`, and `hUmax`. These say precisely that it is
  the largest smooth connected normal unipotent closed subgroup. `pB`, `hpB`
  and `hker` give the B-to-T projection, its identity restriction, and its kernel.
  All are the objects from the recorded reductive-Borel structure conclusion.
- Character and cocharacter lattices: the actual additive group-scheme Hom
  groups in `P : RootDatum ...`; `b : P.Base` gives the simple-root set.
  `hconjS` and `hconjB` pin the tangent actions to conjugation; `hroot`,
  `hpair`, `hweights`, `hpos` pin roots, integer pairing, full root set and
  positive roots to the recorded geometric definitions. `[P.IsReduced]` is
  the reducedness of that datum. The commutativity instances expose the usual
  pointwise character group; they do not select a different lattice.
- Integral half-sum: `ρ` is an actual character and `hρ` says `2 • ρ` is the
  sum of all positive roots. There is no division in F, including for p=2.
- Positive characteristic: `(p : ℕ) [Fact p.Prime] [CharP F p]`, with no bound
  or root-system restriction.
- W: `RankOneRoots.Weyl iT` is the existing rational normalizer quotient.
  `act` and `hact` pin its torus automorphisms to conjugation over every algebra;
  `AffineWeight.characterAction` pulls characters back by the inverse, exactly
  the node's `chi(n inverse t n)`. `w₀` and `hlongest` reverse positive roots.
- Dominant input eta is named `lam` in Lean: `hlam` makes every simple-coroot
  pairing nonnegative. Scoped group-object notation reserves the token eta.
- I(eta): `dominantInducedModule S T B iB pB (act w₀) lam.toMul` unfolds to
  `RhoSection.sectionModule S B iB ((pB ≫ (act w₀).inv ≫ lam.toMul)⁻¹) 1`.
  Thus f(gb)=(w0 eta)(pB(b)) inverse times f(g), after every F-algebra extension.
  This is a submodule of actual global regular functions, not an abstract model.
- Nonzero and finite dimensional: `Nontrivial` and `Module.Finite F` on that
  very subspace. The affine instances for S, T, U only expose properties already
  implied by the geometric hypotheses, for the coordinate-algebra interfaces.
- Rational left action: the existential `c` satisfies the existing coassociativity
  and counit predicates and `IsRegularLeftTranslation S _ c`. In every finite
  tensor presentation c(f)=sum fi tensor hi the latter says
  f(s inverse g)=sum fi(g)hi(s), over all test algebras. The universal point pins
  the coaction, so this is not a free choice of an unrelated action.
- Composition-series existence: `Nonempty (RationalCompositionSeries c)`.
  The new definition uses strictly increasing actual subspaces from bottom to
  top, and the actual subspace quotients with induced nonzero simple coactions.
- Every series: `∀ q : RationalCompositionSeries c`. Exactly one quotient with
  highest weight eta is the `∃! k : Fin q.length` clause using the recorded
  `RationalHighestWeight.HasHighestWeight`, which means a one-dimensional
  U-invariant line and the stated character coaction on that line.
- Every other factor: each `k` for which that highest-weight predicate fails
  has a character `mu`, its highest-weight predicate, nonnegative simple-coroot
  pairings, and `AffineWeight.LT P b mu lam`. The latter is the nonnegative
  integral simple-root cone plus inequality, not a rational or field-valued order.
- Linkage: `∃ (w : RankOneRoots.Weyl iT) (gamma : P.rootSpan ℤ), ...` asserts
  `mu + ρ = w(lam + ρ) + (p : ℤ) • gamma.val`. Mathlib's integral root span is
  exactly Q, the integral span of all roots. Equality is in the character lattice.

Dependency declarations read and used:

- Mathlib `Field` (`Algebra.Field.Defs`), `IsAlgClosed`
  (`FieldTheory.IsAlgClosed.Basic`), `CategoryTheory.GrpObj`
  (`CategoryTheory.Monoidal.Grp`), with the existing scheme group-object setup.
- `Sheaf.AlgebraicGeometry.RhoSectionModules`:
  `AlgebraicGeometry.IsRhoBorelPair`, `exists_rho_section_modules`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `reductive_borel_pair_structure`, `semisimpleGroupScheme_isReductive`;
  the full signature gives the radical, projection, roots and pairing used here.
- `Sheaf.AlgebraicGeometry.RhoSectionModuleData`:
  `RhoSection.Coordinate`, `evaluate`, `characterValue`, `sectionModule`.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`:
  `coordinateAlgebra`, canonical coordinate Hopf structure, `IsStable`, `IsSimple`,
  `invariants`, `characterElement`, `HasHighestWeight`. Rationality uses the
  existing `HopfAction.Coassociative` and `HopfAction.Counital` predicates.
- `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`:
  `normalizer`, `torusInNormalizer`, `Weyl`.
- `Sheaf.AlgebraicGeometry.GroupScheme.AffineWeightOrderAction`:
  `AffineWeight.LE`, `LT`, `characterAction`, now owned by the new definition node
  `def-sfb-affine-weight-order-action`. The existing definitions move verbatim
  from the descent theorem module, whose public import preserves its interface.
- The available proof dependencies are imported without `public`:
  `RhoRegularWeylOrbit`, `SimpleModuleDualHighestWeight`,
  `SimplyConnectedCharacterLattice`, and `AffineReflectionDominantDescent`;
  the remaining proof nodes currently have
  no Lean attachment, so have no import to add yet. The Borel structure is also a statement dependency and a public import.
  Affine descent is used only by the proof and is now an ordinary import.

Searches (all via prescribed msearch.py unless stated):

- LeanFinder, “composition factors of dominant induced rational representations
  of semisimple algebraic groups have highest weights in the affine Weyl orbit
  linkage principle”: eight generalized Lie-weight results; no exact statement.
- LeanSearch, “Rational algebraic group induced module composition series linkage
  highest weight”: eight results including Representation.IndV, invariants and
  Lie weights. Abstract-group induction does not define the regular-function
  rational induced module in this node.
- Loogle, “CompositionSeries, RootPairing, Bialgebra.Comodule, Representation”:
  zero hits, unknown Bialgebra.Comodule. Follow-up “CompositionSeries, Coalgebra”:
  zero hits.
- Mathlib grep “CompositionSeries|HighestWeight|linkage|inducedModule” in
  RepresentationTheory: zero hits from the prescribed service. Source rg found
  the upstream abstract-group `Representation.CompositionSeries`; its full
  defining module was read. It is not a series of rational coaction subobjects.
- LeanFinder for rational composition-series subspaces and simple quotient
  comodules: eight FDRep/abstract-representation hits; no coaction definition.
- LeanSearch for composition series of coalgebra comodules: eight results on
  ordinary module finite length, Coalgebra.Repr and abstract coinvariants.
- Mathlib grep “Coaction|Comodule|CompositionSeries” in RingTheory/Coalgebra:
  zero hits. A direct rg of the Mathlib coalgebra/bialgebra directories likewise
  found no Comodule interface to reuse.
- Direct rg in lean/WeilConjectures and lean/Sheaf, plus dag/lean_names_upstream.json,
  found the existing rational highest-weight data and no rational composition
  series, dominantInducedModule or IsRegularLeftTranslation. Searching for the
  assigned node id in the upstream Lean found no existing declaration.
- DAG grep for composition-series/rational-filtration notions and
  `tools/blueprint_refs.py search 'rational composition'` (zero blueprint hits)
  found the assigned statement and the separate Weil-representation series
  definition, not this rational-comodule notion. The other rational-filtration
  matches concern jet diagrams and projective-cone sections.

Sources read: local Milne printed pp.467--470 (22.17--22.27), the node's full
proof and dependency statements, and the online corroboration explicitly cited
by the node: Andersen (2017), sections 2.2 and 2.8
(https://arxiv.org/pdf/1706.00590), and Williamson (2016), section 1.9
(https://arxiv.org/pdf/1610.06261). These fix the highest-weight and affine-root
translation conventions; no stronger linkage conclusion was substituted.

Edge cases checked before writing: the zero module permits a length-zero series
in the helper but is excluded by the theorem's nonzero conclusion. Quotients are
N_(i+1)/(N_i intersect N_(i+1)); strict monotonicity makes the denominator exactly
N_i inside the numerator. For the trivial semisimple group the root and simple
sets are empty, rho and the unique dominant character are zero, I(0)=F, the
series has one factor, and the other-factor clause is empty. Reducible root
systems have no irreducibility binder; p=2 and every positive prime are allowed.
For eta=0 the induced constants give the unique highest factor with no lower
factor. All dimensions in HasHighestWeight are natural-number finranks rather
than elements of F. Algebra-valued identities include nonreduced algebras and
use the base field's universe, so the universal coordinate point is included.

No statement correction or disputed statement was needed. The item's original
statement, proof and proof dependencies are preserved. Added existing statement
helper nodes and the two definition nodes to stmt_deps only. The affine-descent
  theorem node is retained only in proof_deps, as requested by the return.

## New nodes

`def-sfb-rational-composition-series` defines a finite strictly increasing chain
of rational subspaces from zero to the module, with actual nonzero simple
successive quotients. Its source is Milne Sections 4a--4b (subrepresentations and
quotients), in the composition-series usage of Jantzen II.2 and II.6. It reuses
`def-sfb-rational-highest-weight-data` rather than copying rationality or
simplicity. Both the restriction coaction and the quotient coaction are pinned
by canonical-map squares; over a field the tensor inclusion is injective and
the quotient projection surjective, so these data are unique. The searches above,
recorded also in the new node's mathlib_searches, found no existing rational
coaction composition-series definition. No definition contains sorry.

`def-sfb-affine-weight-order-action` owns the eight existing definitions
`AffineWeight.LE`, `LT`, `Dominant`, `reflectionDot`, `Edge`, `Linked`, `dot`,
and `characterAction`. Its module is `AffineWeightOrderAction`. It imports the
existing root-datum base and actual normalizer quotient; all eight declaration
signatures and bodies are moved verbatim from the base descent module. Only
their blueprint docstrings are relabeled to their new owner. The new node states
the cone order, strict order, shifted chamber, shifted reflections, affine lowering
edges, their reflexive transitive closure, shifted action, and inverse pullback
of characters. Sources are Andersen (1980), Definition 1, p.54, and Milne 21.1--21.2.
LeanSearch for root-lattice dominance and shifted character action returned eight
Lie-weight/Weyl-action results; Loogle `RootPairing.Base, AddSubmonoid.closure`
returned four root-base cone results; Mathlib grep for the moved definition names
returned zero hits. Direct project grep found exactly the original theorem module,
and DAG/blueprint searches found no definition owner. These actual search results
are recorded in the new node; the existing Mathlib building blocks are reused.

## Dependency modules

`lem-sfb-affine-reflection-dominant-descent` receives the explicitly requested
section 1(B) interface repair. Its earlier `lean` record listed plain definitions
inside a theorem module, without a definition node, so a consumer needing only
LT and characterAction could not cite their owning definition node. The repaired
module publicly imports `AffineWeightOrderAction` and removes its eight local
definitions. Its exact theorem signature, natural-language proof and `by sorry`
proof are unchanged. The dependency node changes only in `lean`, with a note
explaining the repair, and now lists only its own theorem declaration. Its public
interface still exposes the moved definitions through the import. No landed proof
is erased: the live server source was read via `scompile.py --source` and the
only theorem proof was and remains sorry. No duplicate names remain.

## Second reading by Q38

Author's second reading, as required for dispatcher direct delivery; no separate
agent was started. Reopened the item, the dependency node and all four Lean files. Checked every binder
against the clause list above. In particular rechecked (1) the inverse right
character, since the source uses a positive Borel; (2) the inverse normalizer
pullback in characterAction; (3) the quotient factor is an actual subquotient
with a uniquely specified coaction; (4) every series is quantified over, not
merely one chosen series; (5) gamma is integral root-span data; (6) simplicity
means nonzero plus only trivial rational subspaces; and (7) the highest-weight
predicate is reused on the same quotient coaction. The first compiler pass
exposed reserved eta/mu/gamma notation and the need to expose commutativity of the
multiplicative target for character inversion; these were repaired without
changing the statement. Rank zero, reducible roots and p=2 remain included.
The helper's length-zero case is allowed. No mathematical mismatch found.
For this repair I additionally compared the eight moved signatures and bodies
against the live source and checked both import paths expose the same declarations.
The item theorem signature is unchanged. The affine-descent theorem, its proof
docstring and proof are byte-identical after the move. Its theorem is now solely
a proof dependency of the item; the new definition node owns all statement notions.

## Validation

All four modules are compiled separately in dependency order through scompile.py.
The required deliver2.py dry run and final delivery are recorded by the delivery
wrapper; the final theorem retains only the expected sorry warning.

## Returned H2 repaired

The return on head 31cd5850750 identified a theorem-only statement dependency
added for plain definitions. This is repaired by the new definition owner
`def-sfb-affine-weight-order-action`, replacing the theorem in the item stmt_deps.
The descent module publicly imports the new module under section 1(B), with a
lean.note and no duplicates. It remains an ordinary proof import of the item.
This performs the requested definition extraction rather than an unchanged re-push.
The dependency copy is taken from current main; the original item and composition
series are retained, with only the reviewed import/dependency ownership repaired.

## Reviewer fix (landing, 2026-10-24)

The delivered move of the eight `AffineWeight.*` definitions from
`AffineReflectionDominantDescent` into the new module `AffineWeightOrderAction` is correct
in substance, but the landing index (tools/nt_parallel2.py Preparation with import_prune_check
check 3) still keeps the names under the old module and refuses any intra-delivery move
("declares names that other modules already declare"). The fix therefore keeps the same
ownership without moving text:

- `AffineReflectionDominantDescent.lean` is the published live text, byte-identical.
- `AffineWeightOrderAction.lean` publicly re-exports that module and adds one transparent
  alias, `AffineWeight.normalizerCharacterAction := characterAction`, with source and
  blueprint docstrings for def-sfb-affine-weight-order-action.
- The record of def-sfb-affine-weight-order-action has that alias as primary declaration
  and lists the eight re-exported names.

The item module, the item record and its stmt_deps are unchanged. The item still states
its theorem on `AffineWeight.LT` and `AffineWeight.characterAction`, owned by the
definition node. The delivered dependency record of lem-sfb-affine-reflection-dominant-descent
(declarations reduced to the theorem; note describing the move) no longer matches the
unchanged module. Land with `--revert-nodes lem-sfb-affine-reflection-dominant-descent`
to keep the live record.
