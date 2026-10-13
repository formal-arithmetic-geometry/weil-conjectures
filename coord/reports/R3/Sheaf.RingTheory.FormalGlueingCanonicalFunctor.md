## What changed

The item now assembles a functor from two separate construction steps, matching the
original node's object and morphism steps. The original signature, visibility and
docstring of `FormalGlueing.exists_canonical_functor` are unchanged.

The two new modules are `Sheaf.RingTheory.FormalGlueingCanonicalFunctorObjects` and
`Sheaf.RingTheory.FormalGlueingCanonicalFunctorMaps`. The first constructs one
canonical glueing object for one module. The second takes an object assignment
with those prescribed fields and constructs its canonical morphism assignment,
including identity and composition laws. The item chooses the prescribed objects,
obtains these maps and laws, and fills the fields of `CategoryTheory.Functor`.

All imports needed only by proofs are plain imports. Each new module publicly
imports only `FormalGlueingData`, which its statement needs. Both import
`Sheaf.Paper.FormalGlueingCanonicalMaps` privately for their planned proofs.
The item privately imports both construction modules.

## Proved and sorry left

Closed the original hole in `FormalGlueing.exists_canonical_functor` (1 of 1
original holes), conditional on the two construction lemmas. Added two holes:

- `FormalGlueing.exists_canonical_functor_objects`, node
  `lem-weil-pbc-formal-glueing-canonical-functor-objects`.
- `FormalGlueing.canonical_functor_maps`, node
  `lem-weil-pbc-formal-glueing-canonical-functor-maps`.

This is a decomposition, not a completed proof: one upper hole closed, two lower
holes added, a local net of -1. Both lower statements are strictly parts of the
original argument. The object statement contains no functor or map assignment;
the morphism statement assumes objects and does not construct them. Neither is a
renamed copy of the target. There are no other local holes or definitions.

All three modules compile individually in dependency order via lcompile.py.
The three declarations' axiom checks show `propext`, `Classical.choice`,
`Quot.sound` and `sorryAx`; there are no nonstandard axioms beyond the open proofs.
The delivery tool repeats its exhaustive declaration probe.

## No longer needed

The item's direct proof import `Sheaf.Paper.FormalGlueingCanonicalMaps` is replaced
by the two construction imports. Its module is still reached through both new
modules and is not pruned.

The old direct proof dependencies no longer cited by the assembly are
`lem-weil-pbc-formal-glueing-canonical-maps`, `def-weil-module-base-change`,
`def-weil-pbc-module-localization-away`, and `def-weil-pbc-module-localization`.
Their mathematical content remains in the lower construction steps or in the
imported definitions. `def-weil-pbc-formal-glueing-data` remains a direct dependency
for packaging the functor into Data. No unit step or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's `canonical_functor_maps` incorrectly claimed that every functor
with the specified object values has the canonical morphism values. This is false.
For t = 0 and R = S = Q with the identity ring map, there are no chart or structural
conditions. Starting with the canonical tensor functor, conjugate each map by an
automorphism of its source and target object. Choose minus identity at the
one-dimensional Q-module and identity at a two-dimensional Q-module. A nonzero
inclusion between these modules changes sign. The object data and functor laws
stay the same, but the map is not the prescribed tensor map. Morphism compatibility
does not assert uniqueness without specifying the components.

The object lemma also previously supplied an entire functor, leaving nearly all
construction work in that hole. It now supplies only one object. The false map
lemma is replaced with existence of the actual canonical morphism assignment and
its laws, conditional on the object construction. Both docstrings now give the
fraction calculations and precise construction, not an appeal to unspecified
uniqueness. The new nodes' earlier abbreviated statements and stale recorded
signatures were replaced by self-contained statements and verbatim Lean signatures.

## New nodes

`lem-weil-pbc-formal-glueing-canonical-functor-objects` realizes only the object
construction: scalar extension, chart localization, bijective comparison and swap,
and the square and cocycle equations. Its complete docstring proof uses
`compare_properties`, `swap_properties` and `compare_smul`.

`lem-weil-pbc-formal-glueing-canonical-functor-maps` realizes only the morphism
construction for prescribed objects. Its proof specifies both Hom compatibility
equations and derives the laws from base change and localization functoriality.
There are no changes to existing statements or definitions and no change records.

## Second reading by R3

1. Compared the item with the repository by diff. The only changes are proof imports
   and its proof body; its existing declaration signature is byte for byte identical.
   No target statement or existing definition is changed. The other two modules and
   nodes are new. Verdict: unchanged existing interface.
2. Compiled all three modules via lcompile.py, and checked #print axioms for all
   three public declarations in a scratch copy. Only the two listed named theorems
   have sorry. There is no axiom, unsafe, opaque, implemented_by, extern, hollow
   definition or hidden proof hole. Verdict: valid conditional assembly, with the
   two explicitly reported open construction steps.
3. Read the split statements from their full Lean types. Rejected the old universal
   map-identification claim by the empty-chart conjugation counterexample above.
   The replacement constructs maps with fixed components and is true. Checked t=0,
   zero modules, f i=0, f i=1 and repeated generators: all formula arguments still
   hold, including zero localizations. LeanSearch returned an Internal Server Error (recorded as unavailable, not as
   evidence of absence). Searched LeanFinder, Loogle, Mathlib grep and
   both library roots using different terminology (object assignment, compatible
   morphisms, identity/composition). Functor.of only packages existing data; no
   duplicate construction theorem was found. Existing canonical-map lemmas supply
   the formulas but not Data.square, Data.cocycle or the two Hom equations.
   Verdict: two genuine construction steps; neither can be closed by one of the
   searched packaging or canonical-map lemmas alone.
4. Read the original node's two construction steps and dag/units/sk-thm-p1.json
   realized fields. This lower decomposition keeps both steps and changes no unit
   route. Imports expose only statement dependencies. All obsolete direct proof
   dependencies are listed above; no module becomes unreachable. Choice here is
   not an arbitrary existence witness: the object specifications determine all
   data fields up to equality (a linear equivalence is fixed by its forward map),
   and Hom values are fixed by their prime and chart components. The remaining
   fields are proofs. No new data definition is introduced. Verdict: valid
   decomposition with accurately reported negative local hole net.
5. Checked each node's proof, proof_deps, proof_origin, source, unit, chapter,
   created record, required search kinds plus Loogle, and lean record against the modules. Corrected
   the two new node statements and recorded signatures. The original node now
   describes choosing prescribed objects and explicitly assembling the functor
   from maps and laws. Verdict: DAG and Lean agree.

Changed during second reading: replaced the false map claim, narrowed object
existence to a single object, rewrote only the resulting assembly proof, fixed
proof-only import visibility in the map module, completed the split docstrings,
corrected node signatures and proofs, and replaced the misleading progress report.
