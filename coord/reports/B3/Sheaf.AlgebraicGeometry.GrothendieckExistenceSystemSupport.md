## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport`
with a complete Lean reduction, retaining its public signature and all public imports.
Two proved private helpers implement the categorical Serre argument and maximal
failing-ideal induction. The public proof constructs the thickening-system object,
uses the dictionary's proper-support equivalence, obtains a proper closed subscheme,
and transports sectionwise annihilation through the coherent closed-immersion
equivalence and the dictionary evaluation isomorphisms.

Added `Sheaf.AlgebraicGeometry.GrothendieckExistenceChowComparison` for the remaining
geometric comparison on a closed quotient. It states the output of paragraphs 2--4
of Stacks 088E before the induction conclusion: a morphism to a properly supported
formal module with kernel killed by an ideal strictly larger than the original
annihilator. It asserts neither proper support for the kernel nor the original
system, and assumes no induction hypothesis. The main module performs those steps.
Updated both DAG proof records to match the Lean route.

## Proved and sorry left

Closed: `AlgebraicGeometry.grothendieckExistence_system_support`
(node `lem-weil-pbc-grothendieck-existence-system-support`), 1 of 1 original holes.
No sorry remains in the item's module or its private helpers.

Added and left: `AlgebraicGeometry.grothendieckExistence_chow_comparison`
(node `lem-weil-pbc-grothendieck-existence-chow-comparison`), exactly one named
public theorem in a new module, with source and complete proof in its docstring.
This is a decomposition: one hole closed and one hole added, net zero;
it is not an axiom-free proof of the target. Existing named dependencies remain
as stated, including their existing sorries.

Compilation of both sandbox modules passes through lcompile.py. The complete
main proof uses maximality and Serre closure, not a single application of a
renamed version of the original assertion. The dictionary and geometric
witnesses are used only inside theorem proofs; no definition chooses arbitrary
objects from unproved existence statements.

Edge cases checked for the new comparison: an empty X, K equal to the unit
ideal, a zero formal module, or an empty V(K) cannot satisfy its hypothesis
that no proper closed support exists. The empty closed subscheme supports the
zero system. For nonempty V(K), the dense open U is nonempty and the ideal
power restricts to the unit ideal there, which justifies strict inclusion
K < J. Nilpotent and zero adic ideals are allowed; no assumption that I is
nonzero or that X is reduced has been added.

## No longer needed

The cokernel branch of the original proof is unnecessary. From the kernel's
proper support and the comparison target's proper support, the Serre-class
lemma for the exact sequence `kernel alpha -> T -> N` gives proper support
of T directly. No new cokernel-support lemma or node is introduced.

Removed direct proof imports from the item:
`CoherentFormalModulesAbelian`, `GrothendieckExistenceProjective`,
`FormalSystemsPushPull`, `FormalSystemsPullback`,
`FiniteTypeModuleSupportPullback`, `PushforwardCoherentOnOpen`,
`ReducedInducedClosedSubscheme`, `ModuleSupportProperOverBase`,
`ClosedSubsetProperOverBaseProperties`, `ClosedSubsetProperOverBaseUnionPreimage`,
`WeilConjectures.AlgebraicGeometry.ChowLemma`,
`WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel`, and
`CoherentFormalModule` (Sheaf.AlgebraicGeometry prefix on unqualified names).
Except for the unnecessary direct ClosedModel dependency, these are retained
where needed by the new geometric comparison's statement or proof plan.

`lem-chow-closed-model` is no longer an independent compactification dependency
of this proof. The quasi-compact immersion's scheme-theoretic image directly
provides the compactification using Mathlib's `Hom.toImage` and `Hom.imageι`.
ClosedModel remains transitively used inside the established Chow lemma;
therefore no entire module is claimed to leave the targets' import closure.
Other geometric nodes are relocated under the new comparison node, not pruned.
No unit statement or realized unit step is bypassed.

For completeness, every original `proof_deps` entry absent from the new main
node's direct proof is listed here:

- `def-weil-proper-morphism`: remains a statement dependency; no separate proof use.
- `lem-chow-closed-model`: removed as a direct proof dependency, as explained above.
- `lem-weil-pbc-adic-complete-jacobson-radical`
- `lem-weil-pbc-chow-noetherian`
- `lem-weil-pbc-closed-subset-proper-over-base-properties`
- `lem-weil-pbc-closed-subset-proper-over-base-union-preimage`
- `lem-weil-pbc-coherent-formal-modules-abelian`
- `lem-weil-pbc-formal-systems-pullback`
- `lem-weil-pbc-formal-systems-push-pull`
- `lem-weil-pbc-grothendieck-existence-projective`
- `lem-weil-pbc-module-support-proper-over-base`
- `lem-weil-pbc-pushforward-coherent-on-open`
- `lem-weil-pbc-reduced-induced-closed-subscheme`
- `lem-weil-pbc-support-pullback-finite-type`

The last twelve entries are dependencies of the new comparison node. None is
claimed to be removed from the target closure.

## Where the brief, the DAG or earlier work was wrong

The original plan applies `ProperClosedModel` to the Chow modification Y, but
its actual theorem requires an affine source. Y need not be affine. The
scheme-theoretic image of the Chow immersion gives the needed compactification
without that hypothesis, via the already established Mathlib instance for
quasi-compact immersions. The new node records this route explicitly.

The original imports have no declaration assembling the closed-quotient Chow
comparison and the inverse-image annihilator J strictly larger than K. This
geometric assembly is the single new statement, rather than another copy of
the complete support assertion.

The formal category's inherited zero morphisms and the chosen Abelian
structure's zero morphisms need not be definitionally identical. The proved
private categorical helper uses uniqueness of HasZeroMorphisms to normalize
them before applying Mathlib's exact-sequence lemma; no interface was changed.

The cited `literature/stacks-project/coherent.tex` is absent in this local clone.
The full proof of Stacks 088E was read at
https://stacks.math.columbia.edu/tag/088E and checked against the supplied node.
LeanSearch returned Internal Server Error; LeanFinder, Loogle, and source
searches completed, and the unavailable service is recorded without claiming
it established absence of a result.

## New nodes

`lem-weil-pbc-grothendieck-existence-chow-comparison` records the geometric
comparison on V(K), including compactification by scheme-theoretic image,
projective existence, the Jacobson-radical support argument, proper pushforward,
and exact closed-pushforward kernel transport. Its Lean declaration is
`AlgebraicGeometry.grothendieckExistence_chow_comparison` in
`lean/Sheaf/AlgebraicGeometry/GrothendieckExistenceChowComparison.lean`.
All natural-language proof steps carry their existing dependency nodes.
No existing signature, definition, visibility, or downstream module is changed;
there are no change records or forced adaptations.


## Second reading by B3

1. **Interfaces — pass.** Compared the delivered main module with its repository
   version using `diff`, then compared the substring from the existing theorem
   keyword to `:= by` byte for byte: identical. All existing public imports and
   visibility are unchanged. Only two private proved helpers and proof imports
   were added. No definition or downstream module is changed; no change record
   is needed. The new public statement lives in its own module.
2. **Proof and axioms — pass as a decomposition.** Compiled both modules together
   in import order through `lcompile.py`, without errors or warnings. Scanned
   both files: the only textual sorry is the named comparison theorem, with its
   source, proof docstring, and matching node. There are no forbidden declarations
   or hollow definitions. Scratch copies with `#print axioms` checked the public
   declarations and both private helpers: the categorical helper uses only
   `propext`, `Classical.choice`, and `Quot.sound`; the other declarations also
   use `sorryAx` from the reported comparison or existing open dependencies.
   The scratch copies were removed. No arbitrary witness from an unproved
   existence theorem is stored in a definition.
3. **Split statement — pass.** Read the geometric construction independently
   against https://stacks.math.columbia.edu/tag/088E, stopping before its induction
   conclusion, and checked the types of the closed-immersion equivalence and
   proper push-pull theorem. The comparison does not assert proper support of
   its kernel or of the input. The main proof supplies maximality, subobject
   closure, and the exact-sequence argument. For K equal to the unit ideal,
   an empty quotient, an empty X, or a zero system, the no-proper-support
   hypothesis is false. Zero and nilpotent adic ideals cause no extra hypothesis.
   On a nonempty dense open of V(K), the complement ideal and each positive power
   are the unit ideal, so their inverse images strictly contain K. Kernels are
   transported by their universal properties, independent of the chosen Abelian
   structure. Repeated LeanFinder, Loogle, Mathlib grep and library searches with
   different terminology; found no existing geometric comparison. Closing this
   remaining hole is a substantial geometric formalization, not a short repair.
4. **Route and pruning — pass, accounting repaired.** The maximal failing-ideal
   argument is a real reduction, followed by dictionary and sectionwise scalar
   transport. Mathlib's kernel-sequence exactness already gives the shortest
   Serre conclusion without the cokernel branch. Checked the Mathlib instance
   `IsImmersion.instIsOpenImmersionToImageOfQuasiCompact` supporting the
   compactification repair. Existing unit `sk-thm-p1` and its `realized` steps
   are unchanged; this is below those steps. Statement imports are public and
   proof imports private. Added the exhaustive list above of original direct
   proof dependencies absent from the new main proof, distinguishing relocation
   from pruning. No entire module leaves the target import closure.
5. **Nodes — pass.** For both nodes, `proof_deps` equals the union of step `uses`.
   The main node differs only in `proof`, `proof_deps`, and `proof_origin`.
   The new node has source, complete steps, searches, creation provenance,
   blueprint ancestry, chapter/unit, and a Lean record matching its statement.
   Each dependency names an existing node and declaration or a Mathlib match.

Second reading changed the report's exhaustive dependency accounting and added
this review record. The proof and the new statement required no repair.
The result remains one hole closed and one hole added, net zero, with no module
pruned from the target closure.
