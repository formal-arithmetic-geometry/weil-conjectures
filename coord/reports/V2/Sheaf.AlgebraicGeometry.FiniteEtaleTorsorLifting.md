## What changed

The target theorem is assembled from three named intermediate theorems. `FiniteEtaleSchemeTorsorLift`
lifts the representing finite étale scheme torsor and its action. `SchemeTorsorPullbackCompatible`
constructs the unit-compatible representable comparison. `EtaleTorsorUnitActionUnique` records the
sheaf-level action uniqueness step, now proved by adjunction injectivity and binary-product comparisons. The target module imports these proof-only modules. The geometric intermediate includes
representation of the downstairs constant torsor.

## Proved and sorry left

This is a decomposition, not a complete proof free of intermediate holes. The original hole
`AlgebraicGeometry.Etale.finiteEtale_lifts_torsor_transport` is closed by its real Lean assembly.
The new `AlgebraicGeometry.Etale.etale_torsor_unit_action_unique` is proved with no direct hole,
using the existing abelian inverse-image hom comparison. Two new named holes remain:

- `AlgebraicGeometry.Etale.finiteEtale_lifts_scheme_torsor`, node
  `lem-weil-pbc-finite-etale-scheme-torsor-lift`.
- `AlgebraicGeometry.Etale.scheme_torsor_pullback_compatible`, node
  `lem-weil-pbc-scheme-torsor-pullback-compatible`.

The item itself has no remaining direct holes. Closing one original hole and adding two is net
minus one before accounting for newly imported existing dependencies; no net proof progress is
claimed. Both new holes are strictly components: one returns equivariant scheme representatives and knows
neither sheaf inverse-image comparisons nor hτ; the other assumes an equivariant representative and knows neither
finite étale equivalence nor a transport function.

## No longer needed

All three original public imports are retained for the unchanged signature. The target
removes these proof-only imports: `Sheaf.AlgebraicGeometry.FiniteLocallyConstantSetsRepresentability`,
`Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable`, and
`WeilConjectures.ConstructibleSheaf.Defs`. The first two are now imported privately by
the corresponding geometric intermediate; the third is available through the representability
interface. No globally unreachable module is claimed as pruned.
The original node's direct proof dependencies
`lem-weil-pbc-finite-locally-constant-sets-representability`,
`lem-galois-inverse-image-representable`, `def-weil-pbc-finite-etale-category`,
`lem-weil-pbc-flat-lfp-open`, and `lem-weil-pbc-finite-proper` are replaced by the intermediate
interfaces; they remain needed within those interfaces and are not globally pruned.
The import `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent` was removed from
the exploratory proof: it reaches the item through `HenselianFiniteEtale` and
`FiniteEtaleEquivalenceH1`, closing an import cycle despite compiling against cached modules.
The representation step now belongs to the geometric lifting intermediate, whose lower interfaces
include `FiniteLocallyConstantSetsRepresentability`; no source module is adapted.
Action uniqueness needs only `EtaleInverseImageAbelianLiftHom` and direct Mathlib instances for
finite-limit preservation. It does not require `EtaleInverseImageAlgebraicStructures`,
`EtaleInverseImageAbelianLift`, their ring-lift dependencies, or the operation-comparison lemma
`lem-weil-pbc-etale-inverse-image-abelian-lift-ops`. These were exploratory imports only,
so no whole-library pruning count is claimed.

## Where the brief, the DAG or earlier work was wrong

An import-direction audit discovered the above cycle in the proposed shortest-route dependency.
The final delivery has no import of EtaleTorsorDescent and no existing source-module adaptation.
The original dependency signatures alone do not expose scheme action lifting or the unit equations
for an equivariant representative. Those two missing interfaces are isolated explicitly. Action
uniqueness is not an additional black box: it is now proved, deriving the unit comparison from the
existing hom-set comparison and cancelling an invertible product comparison. The stage-3 route
retains the unit's steps and makes no connectedness or point assumptions.

Edge cases checked mathematically: the empty base yields the unique empty representative; for the
trivial group the simply transitive scheme is the base; a non-surjective i is handled by reflecting
the clopen image inclusion, not by assuming that pullback detects surjectivity in general. The
compatibility theorem assumes an actual equivariant scheme isomorphism, so it has no unsupported
reflection premise. The action uniqueness proof applies to arbitrary abelian G, including zero G,
and uses no finite or nonempty assumption.

## New nodes

`lem-weil-pbc-finite-etale-scheme-torsor-lift` records the representation and finite étale scheme torsor lifting step.
`lem-weil-pbc-scheme-torsor-pullback-compatible` records its representable sheaf comparison and
unit equations. `lem-weil-pbc-etale-torsor-unit-action-unique` records the strict sheaf action
uniqueness argument (proved in this delivery).

## Second reading by V2

1. Compared the delivered target module against the repository with `diff -u`: the
   existing theorem signature and docstring are byte-for-byte unchanged. Only its
   proof and private imports differ. The other three modules are new; no definitions
   or existing source modules change and no statement change record is needed.
2. Compiled all four modules in import order with `lcompile.py --all`; no errors or
   warnings. A scratch copy printed axioms for all four public theorems: only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter remains
   in the two listed geometric holes and in the existing abelian hom comparison
   used by action uniqueness. There are exactly two new direct `sorry`s, both named
   public theorems; the private action definition is constructed explicitly. No
   forbidden declarations or arbitrary existence-witness definitions occur.
3. Read both split statements, their full proof docstrings, and their nodes. They
   are strictly smaller components: geometric representative/action lifting and
   compatibility for a given representative. Neither restates arbitrary transport
   essential surjectivity. Checked empty bases, the trivial group, and nonsurjective
   i; surjectivity is reflected through the clopen image, not through points of i.
   Independently searched LeanFinder for reflection/lifting of finite-cover actions,
   Loogle for adjunction hom equivalences, Mathlib Sites by grep for representable
   pullback/torsors, and repository sources. No duplicate of either split statement
   was found. EtaleTorsorDescent provides the representation substep but creates the
   documented cycle; fundamental-group TorsorPullback assumes connectedness.
   Sources checked online: [0A5G](https://stacks.math.columbia.edu/tag/0A5G),
   [03RV](https://stacks.math.columbia.edu/tag/03RV), and
   [03Q1](https://stacks.math.columbia.edu/tag/03Q1). The two geometric holes require
   substantial formal construction; neither has a short existing proof to apply.
4. Read the assembly and action-uniqueness proof from the top down. The latter uses
   the actual hom-set comparison, finite-limit instances, unit naturality, product
   projections, and cancellation; it has no new action-uniqueness hole. All newly
   introduced proof imports are private. The unit `sk-thm-p1` and its `realized`
   route remain unchanged: the finite-etale/torsor comparison step is retained.
   Corrected the pruning report to name all three removed target imports. No
   whole-library module pruning or net hole reduction is claimed.
5. Checked all four node records against the Lean signatures and proof route:
   the target's three assembly steps match its calls, the action node records the
   abelian hom comparison, and both geometric nodes contain sources, search records,
   creation/blueprint metadata, complete plans and Lean records. Restored private
   imports of the lower representability, openness/properness, representable inverse
   image and locally constant-section interfaces to their new modules, so these
   open theorem plans retain access to the dependencies their nodes name.

Second reading changed only the missing lower proof-dependency imports and the
report (explicit import removals and this review). It closed no additional holes.
The original hole is closed by decomposition into two new holes; action uniqueness
is proved relative to existing open dependencies, not axiom-free yet.
