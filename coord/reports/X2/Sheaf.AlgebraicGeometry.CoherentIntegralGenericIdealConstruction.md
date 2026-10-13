## What changed

The unchanged theorem `AlgebraicGeometry.Scheme.Modules.coherent_integral_generic_ideal_construction`
now obtains a finite free map near the generic point, extends that specific map from an ideal
lattice with the same rank, proves coherence of its finite coproduct, and assembles the witnesses.
Its original `sorry` is removed. This is a decomposition, not an axiom-free proof of the geometry.

Three new modules contain the two geometric steps and the fully proved finite-coproduct
coherence result. In `coherent_sigma_of_coherent_ideal`, the locally Noetherian criterion supplies
quasi-coherence and finite type for the ideal. Quasi-coherent coproduct closure, explicit local
finite generating families, and reindexing through `ULift (Fin r)` prove the required coherence.
The explicit `IsFiniteType.mk (R := Z.ringCatSheaf)` fixes the earlier universe inference error.

Read Stacks Project Tag 01YE at https://stacks.math.columbia.edu/tag/01YE (the cited local
literature file is absent on this machine). The two new geometric statements isolate its two
integral-case paragraphs. The finite free neighbourhood only asserts invertibility at the
specified stalk; shrinking to an isomorphism on the whole open is unnecessary. Both remaining
holes have complete proof descriptions and matching nodes. No existing signature, definition,
or visibility changed; no forced adaptations.

## Proved and sorry left

Original holes closed: 1 of 1, in
`AlgebraicGeometry.Scheme.Modules.coherent_integral_generic_ideal_construction`
(node `lem-weil-pbc-coherent-integral-generic-ideal-map-construction`).

New holes added: 2, both strictly parts of the geometric argument:

- `AlgebraicGeometry.Scheme.Modules.exists_generic_free_neighbourhood`, in
  `Sheaf.AlgebraicGeometry.CoherentIntegralGenericFreeNeighbourhood`, node
  `lem-weil-pbc-coherent-integral-generic-free-neighbourhood`.
- `AlgebraicGeometry.Scheme.Modules.exists_generic_ideal_extension`, in
  `Sheaf.AlgebraicGeometry.CoherentIntegralGenericLatticeExtension`, node
  `lem-weil-pbc-coherent-integral-generic-lattice-extension`.

The new theorem `AlgebraicGeometry.Scheme.Modules.coherent_sigma_of_coherent_ideal` has a
complete Lean proof and no local hole (node
`lem-weil-pbc-coherent-integral-generic-ideal-sigma-coherent`). There are no other holes in the
delivered files. Thus this delivery decomposes one upper hole into two lower holes, net -1;
it does not claim net sorry reduction. The first lower theorem constructs only a local map
from a free module. The second fixes that map and rank and performs only the ideal extension;
neither repeats the original statement. The main theorem combines them with the proved
coherence result in Lean.

Edge cases checked mathematically: rank zero uses the empty basis and empty coproduct; zero
generic stalk is permitted even when the sheaf has torsion elsewhere. The given stalk
isomorphism in the extension theorem is retained, so an arbitrary noninvertible local map
cannot be used. Exponent zero uses the unit ideal. U may be all of Z, when the complement
ideal is the unit ideal. Integral schemes are nonempty, so no undefined generic point case
occurs. No ideal nonzero hypothesis is needed in the conclusion.

## No longer needed

Removed these original proof-only imports from the assigned module (all public imports stay):

- `Sheaf.AlgebraicGeometry.CoherentStalkMapExtends`
- `Sheaf.AlgebraicGeometry.CoherentLocalIsomorphism`
- `Sheaf.AlgebraicGeometry.CoherentHomsOverOpen`
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk`
- `Sheaf.Algebra.Homology.ModuleStalkExact`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`

The basis and extension modules retain the relevant original geometric dependencies as their
stated proof plans; the finite-sum module uses the coherence criterion and existing source
library coproduct/generator results. The node `lem-weil-pbc-coherent-local-isomorphism` and its
module are not needed for this construction: the target only asks for an isomorphism of one
stalk. `IntegralIdealGenericStalk`, `ModuleStalkExact` and the tensor-product module are not
direct dependencies of this reduction. The generic field is supplied by Mathlib's
`AlgebraicGeometry.FunctionField`. All seven original proof-dependency nodes are accounted for: the stalk-map extension and
finite-type criterion are used by the generic-basis node; the reduced closed subscheme,
Homs-over-open, ideal-product affine sections, and kernel/cokernel nodes are used by the
lattice-extension node. Only `lem-weil-pbc-coherent-local-isomorphism` is bypassed outright.
The new generic-basis module also omits the unnecessary public ideal-sheaf-module import.
Some removed imports remain transitively reachable through
other geometric dependencies; no claim is made that they leave the whole targets' closure.

Removed the earlier sandbox-only `CoherentIntegralGenericIdealCore` module and node
`lem-weil-pbc-coherent-integral-generic-ideal-core`: it merely packaged nearly the entire
original construction. The main theorem now combines the two real geometric steps directly.
No unit-level statement or proof step in `dag/units/sk-thm-p1.json` is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report described its core and finite-sum lemmas as two remaining holes,
but the files had subsequently been changed: the finite-sum lemma contained a proof with a
universe error, and the core imported two additional holed modules with no nodes. This repair
fixes the proof, supplies the two missing nodes, removes the redundant core wrapper, and
updates the route metadata and this report to match the actual files.

The earlier report also claimed the worker dry run could not pass without writing a second
reading. The current delivery tool explicitly allows that sole preflight exception for the
worker's `--no-push` run. This worker has not written a second reading and will not push.

## New nodes

`lem-weil-pbc-coherent-integral-generic-free-neighbourhood`: finite generic basis and its
extension to a local finite free map, with the restriction-stalk invertibility conclusion.
Source: Stacks Tag 01YE, generic-basis paragraph, using 01Y4. Remaining `sorry`.

`lem-weil-pbc-coherent-integral-generic-lattice-extension`: extension of a fixed local map
from a power of the complement ideal and conversion to a finite ideal coproduct. Source:
Stacks Tag 01YE, final paragraph, using 01J3 and 01YB. Remaining `sorry`.

`lem-weil-pbc-coherent-integral-generic-ideal-sigma-coherent`: coherence of finite coproducts
of one coherent ideal, proved using the local Noetherian criterion, quasi-coherent coproduct
closure, and explicit finite local generators. No `sorry`. Source: Tag 01YE and 01XZ.

No change record is required: all existing interfaces are unchanged.

## Second reading by X2

1. PASS: diffed every delivered module against the repository. The construction module is
   the only existing file; its theorem signature is now byte for byte identical, including
   whitespace. Its public imports and visibility are unchanged. The other three modules
   and their nodes are new. There are no changed definitions or forced adaptations.
2. PASS: compiled all four modules locally in import order, with no errors or warnings.
   The only two literal `sorry`s are the named geometric theorems listed above; no data
   definition, axiom, unsafe, opaque, extern or implemented_by declaration is added.
   A scratch module printing axioms of all four declarations compiled. The main theorem
   and the two open lemmas use only propext, Classical.choice, Quot.sound and sorryAx;
   coherent_sigma_of_coherent_ideal uses only the three permitted axioms, with no sorryAx.
3. PASS: independently read both geometric statements and their complete docstring proofs
   against [Stacks Tag 01YE](https://stacks.math.columbia.edu/tag/01YE), integral case.
   Finite-dimensionality and extension of a fixed-rank local map are strictly separate
   parts of the argument. Checked zero rank, a zero generic stalk with torsion elsewhere,
   U equal to the whole scheme, and exponent zero. No arbitrary existence witness is
   selected into a definition. Repeated searches with different terminology using
   leanfinder, loogle and grep (recorded in searches.jsonl and the new nodes), and searched
   both source roots plus Mathlib locally. Free-locus results concern localized algebraic
   modules; local fraction results do not supply the sheaf extension. No existing exact
   result closes either open geometric lemma in a short pass.
4. PASS: the main proof directly combines the local free map, same-rank ideal extension,
   and finite-sum coherence. Read the upstream quasi-coherent coproduct theorem, finite
   presentation coproduct theorem, and finite generator sigma API. The latter is used;
   the finite-presentation alternative needs additional conversion and does not shorten
   this proof. All removed imports and the disposition of every original proof_deps node
   are listed above. The unit sk-thm-p1 realized record does not contain any bypassed node;
   no unit statement, step or realization is altered.
5. PASS: checked the new nodes' required fields, exact Lean statements, sources, docstring
   blueprint ids and proof routes. Each proof_deps is the union of its steps' uses. The
   construction's three dependencies are exactly its three lemma applications; the
   finite-sum node describes its proved quasi-coherence and local-generator argument.

Second reading changed the existing signature's line wrapping back to its exact original
text, removed an unused public ideal-sheaf import from the new generic-basis module,
recorded independent searches, and completed pruning accounting. No proof repair was
needed and no additional hole was closed. The delivery remains a decomposition of one
original hole into two true lower statements, net -1; finite-sum coherence is axiom-free.
