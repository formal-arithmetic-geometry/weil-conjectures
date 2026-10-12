## What changed

Reduced `AlgebraicGeometry.RingedSpace.module_mayerVietoris` without changing its statement.
Its proof constructs the underived square of additive section functors, proves its
injectivity and exactness using Mathlib's two-open sheaf condition, and obtains
surjectivity on injectives from the existing `injective_restriction_surjective`.
The four restriction faces are proved from presheaf composition and uniqueness of
morphisms of opens. Deriving these maps gives `openModuleCohomologyRestriction` by
definitional equality, including the final restriction square.

Added three modules under `Sheaf.CategoryTheory.Abelian.RightDerived`:

- `InjectivelyExactSquare`: bundles the underived square and its three hypotheses on
  injectives; implements the actual Cartesian-product functor, diagonal, difference,
  and their maps on a chosen injective resolution; PROVES short exactness of that
  sequence of complexes by the degreewise Mathlib criterion; and DEFINES `boundary`
  by composing resolution comparison, Mathlib's complex connecting map, and inverse
  comparison. All of this module is proved/defined without `sorry`.
- `InjectivelyExactSquareBoundaryExact`: the remaining exactness transport and initial
  degree-zero injection for that explicitly defined boundary.
- `InjectivelyExactSquareBoundaryNaturality`: the remaining object-variable and
  square-variable naturality for that same explicitly defined boundary.

The main theorem constructs its natural connecting transformations from the object
naturality clause, uses the separate exactness theorem, then constructs the restriction
morphism of section squares and uses the square-naturality clause componentwise. The two
unfinished results are separate steps about a concrete map; there is no new existential
Mayer--Vietoris statement taking over the original theorem.

Updated the original node's proof, dependencies and origin to describe this implementation.
No target, existing definition, theorem signature, public import or unit record was changed.
The four Lean modules compile cleanly in import order. The Stacks source was checked at
https://stacks.math.columbia.edu/tag/01EB; its injective section-complex route is retained.
The referenced local `literature/stacks-project/cohomology.tex` is absent on this machine.

## Proved and sorry left

`AlgebraicGeometry.RingedSpace.module_mayerVietoris`: its one local `sorry` is removed,
with its original statement proved from the named dependencies. This is a reduction,
not a claim that its transitive axioms are already free of `sorryAx`.

New proved theorem:
`CategoryTheory.InjectivelyExactSquare.resolutionSequence_shortExact`, node
`lem-sc-injectively-exact-square-resolution-short-exact`. The supporting diagonal/difference
commutation theorem and every private helper are also proved.

The only sorries in the delivered Lean files are:

- `CategoryTheory.InjectivelyExactSquare.boundary_exact`, node
  `lem-sc-injectively-exact-square-boundary-exact`.
- `CategoryTheory.InjectivelyExactSquare.boundary_naturality`, node
  `lem-sc-injectively-exact-square-boundary-naturality`.

Each is exactly `:= by sorry`, with a complete mathematical proof in its docstring and
node. No definition contains `sorry`; the boundary's data is a composition of existing
isomorphisms and Mathlib's connecting map, and its required short-exactness proof is proved.

The existing `AlgebraicGeometry.injective_restriction_surjective` and
`AlgebraicGeometry.RingedSpace.moduleSheaves_abelian_enoughInjectives` are used as stated;
their existing sorries are not modified by this delivery.

## No longer needed

Removed proof imports `Sheaf.Topology.RestrictInjectiveResolution` and
`Sheaf.Topology.RingedSpaceModuleCohomology`.

The direct branch through `lem-sc-ringed-space-restrict-injective-resolution` /
`Sheaf.Topology.RestrictInjectiveResolution` is unnecessary here. `openModuleCohomology`
already computes every open's cohomology by deriving sections on the module category
on X; the argument uses that same resolution on X. There is no separate restricted
resolution to compare.

`def-sc-ringed-space-module-cohomology` is removed from the node's direct proof dependencies.
`moduleCohomology_iso_resolution` and `moduleCohomology_independent` are not used in this
proof. Their module `Sheaf.Topology.RingedSpaceModuleCohomology` remains a transitive public
import of `OpenModuleCohomology`, so removing its redundant proof import does not make
that whole module globally unreachable.

The three original generic nodes for complex long exact sequences, derived maps via
lifts, and complex-sequence naturality remain needed below the new exactness/naturality
nodes. They are moved to those dependencies rather than claimed as pruned. Injective
restriction surjectivity remains needed. No other node/module is claimed unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original mathematical route is sound. Its existing Lean interfaces do not provide
the passage from a sequence of additive functors exact on injectives to a natural
sequence of derived functors. The object-variable right-derived sequence in the source
library does not supply this functor-variable construction. The delivery implements
its resolution-sequence and boundary construction, leaving only the two comparison
arguments as explicitly named steps.

Searches: LeanFinder returned Ext exact-functor and localizer exactness lemmas, not this
bridge; Loogle did not recognize the indexed `NatTrans.rightDerived` identifier; LeanSearch
returned an internal-server error. Local inspection of Mathlib's RightDerived,
HomologySequence, HomologySequenceLemmas and HomologicalComplexAbelian supplied the
resolution comparison, complex boundary, naturality, and degreewise short-exactness
criterion. The latter is actually applied in the new proved module. No assembled theorem
for these functor-variable squares was found. Blueprint and DAG searches found no duplicate.
The searches are recorded in the new nodes.

The unit `sk-thm-curveestimate` has this lemma below its realized statement, and no realized
step is bypassed. The implementation retains the injective-resolution/section-SES route.
No statement dispute or change record is needed.

## New nodes

`lem-sc-injectively-exact-square-resolution-short-exact`, in
`dag/nodes/sec-curve-estimates/lem-sc-injectively-exact-square-resolution-short-exact.json`,
records the proved generic degreewise short exactness in
`lean/Sheaf/CategoryTheory/Abelian/RightDerived/InjectivelyExactSquare.lean`. It also records
the explicit input square, product functor, resolution sequence and transported boundary
formula. The underived hypotheses are discharged for section squares in the main module.

`lem-sc-injectively-exact-square-boundary-exact`, in
`dag/nodes/sec-curve-estimates/lem-sc-injectively-exact-square-boundary-exact.json`, states
the transport of the three complex homology exactness positions and initial injection
for the explicit boundary, in
`lean/Sheaf/CategoryTheory/Abelian/RightDerived/InjectivelyExactSquareBoundaryExact.lean`.
Its proof uses the existing complex long-exact-sequence and resolution-comparison nodes;
the remaining middle-product homology comparison is described coordinatewise in full.

`lem-sc-injectively-exact-square-boundary-naturality`, in
`dag/nodes/sec-curve-estimates/lem-sc-injectively-exact-square-boundary-naturality.json`,
states the two functoriality arguments for that explicit boundary, in
`lean/Sheaf/CategoryTheory/Abelian/RightDerived/InjectivelyExactSquareBoundaryNaturality.lean`.
Its proof uses the existing complex-sequence naturality and resolution-lift/comparison nodes.
The same chosen resolution is used for all squares at a fixed object, so restriction
compatibility does not rely on unrelated choices of connecting maps.

Edge cases checked for these new statements: zero groups or zero functors; degree zero,
where natural-number indexing gives no incoming boundaries; and arbitrary squares without
assuming the four functors are left exact. For the section specialization this includes
coincident opens, empty opens and arbitrary W, without requiring W to lie in the union.
No change-record files are needed.

## Second reading by V2

1. **Visible statements:** Compared the delivered module with the repository version. The
   existing `module_mayerVietoris` signature is byte-for-byte unchanged; the three added
   declarations are new split nodes with their signatures recorded in matching DAG files.
   Verdict: pass.
2. **Proof validity:** Compiled all four delivered modules with `lcompile.py --all`.
   There are no errors, forbidden declarations, or hollow definitions. The only remaining
   `sorry`s are exactly `boundary_exact` and `boundary_naturality`, each named in the
   report and matched to a split node. Verdict: pass.
3. **New statements:** Checked the edge cases documented for zero functors/groups,
   degree zero, coincident or empty opens, and unrestricted W. Searches and local source
   inspection found no duplicate Mathlib or library declarations. Verdict: pass.
4. **Pruning and route:** The proof uses the explicit injective-resolution square route;
   the unit's realized statement and route are retained. Removed imports and old direct
   dependencies are listed under “No longer needed”; all retained imports are used. The imports of `HomologicalComplexAbelian` and
   `ShortComplex.Ab` in the new square module were corrected from public to proof-only.
   Verdict: pass.
5. **DAG agreement:** Verified that each node's Lean declaration, proof steps,
   dependencies, origin, and split status match the delivered code and report. Verdict:
   pass.

Changed the two proof-only imports in the new `InjectivelyExactSquare` module from
`public import` to `import`, and added this review. No Lean signatures or definitions
were changed. Recompiled all four modules after that correction.

Independent `#print axioms` checks on scratch copies show only `propext`,
`Classical.choice`, and `Quot.sound` for `resolutionSequence_shortExact`, `boundary`,
and `diagonal_difference`. The two split theorems and `module_mayerVietoris` additionally
use `sorryAx`, as expected from the open dependencies; no other axiom appears.
The second reader's new LeanFinder query was “Homology of a short exact sequence of
additive functors evaluated on an injective resolution with natural connecting maps”;
it returned resolution/derived-zero comparison lemmas, no assembled bridge.
A fresh grep search and inspection of the upstream RightDerived extension and the
library's FullLongExactSequence found only object-variable sequences, not these
functor-variable steps. Both remaining statements require substantial transport and
comparison arguments rather than an immediate application of an existing theorem.

The existing main theorem docstring still describes the older restricted-resolution
route; its replacement proof and DAG instead derive sections on the single module
category on X. This historical documentation discrepancy does not change its statement.
The unit record has realized statement `thm-sc-proper-cohomology` and no realized steps;
no part of that route was removed.
