## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.Modules.proper_flat_cohomology_model_properties` by a complete
Lean reduction. Its signature and original docstring remain unchanged, as do all public
imports. Added two proof-only imports and two new statement modules:

- `Sheaf.AlgebraicGeometry.ProperFlatFinitePresentationModel`: constructs a bounded
  finite-presentation flat quasi-coherent cohomology model on the specified affine U,
  with an unspecified upper bound b and no input complex C.
- `Sheaf.AlgebraicGeometry.AffineFinitePresentationFlatShortening`: shortens such a complex
  using residue-field vanishing, with no proper morphism or coefficient sheaf.

The actual proof composes both cohomology comparisons over the standard fibre product,
registers its Grothendieck-abelian instance to obtain injective resolutions, proves
residue-field vanishing from the zero degree-q term of C for q>d, applies shortening,
and composes the resulting comparisons for every scheme base change. No choices occur
inside definitions. The supplied comparison and upper bound of C suffice: ht, hCge,
hCflat and hCqc are unnecessary for this argument. The unused-variable linter is disabled
only for this declaration to retain the original signature without artificial uses.

The original node now records the actual two-part route. The geometric lemma still
follows the unit's Noetherian-approximation/proper-coherence/perfect-model argument;
the algebraic lemma spells out top-degree cancellation on the same affine open.
No unit statement or realized step was changed (the unit's realized lists are empty).

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.proper_flat_cohomology_model_properties`
(node `lem-pc-proper-flat-cohomology-model-properties`). There are no direct sorries
left in the assigned module.

Added exactly these two holes, each the entire proof of a public theorem:

- `AlgebraicGeometry.Scheme.Modules.exists_proper_flat_finitePresentation_model`
  (`lem-pc-proper-flat-finite-presentation-model`).
- `AlgebraicGeometry.Scheme.Modules.exists_affine_finitePresentation_flat_shortening`
  (`lem-pc-affine-finite-presentation-flat-shortening`).

This is a decomposition: one upper hole closed, two lower holes added, not a complete
axiom-free proof of the geometry. The delivery's local direct-hole net is -1; the
maintainer's pinned sorry ledger decides the targets-closure net. All three modules
compile together in import order without warnings, each below the 60-second limit.
The new modules have no definitions, private holes, or axioms.

The two lower statements are strictly parts of the argument. The first has no C or
prescribed d, gives no D-versus-C comparison or pseudo-coherence conclusion, and
produces finite-presentation terms at an unspecified bound. The second starts with
such a complex and has no f,F or higher direct image. The upper theorem proves the
vanishing hypothesis of the second and the comparisons linking its output to C.

Edge cases checked in the argument: empty U/empty inverse image uses zero in the
geometric construction; the zero ring uses zero in shortening; b<=d needs no
cancellation; d=0 yields a finite-projective module; projective terms need not be
globally free; nonaffine new bases are included in both comparisons. Top-degree
cancellation does not introduce negative terms since m>d>=0 implies m-1>=0.

## No longer needed

No existing import was removed: all four public imports support the unchanged
statement, and both added proof-only imports are used. No proof-only import is unused.

The new route does not need node `lem-weil-pbc-proper-noetherian-stage` or its module
`Sheaf.AlgebraicGeometry.ProperNoetherianStage`: the proper-support perfect direct-image
argument descends proper support and does not require a proper stage morphism. This is
pruning from this item's argument, not a claim that other targets no longer use it.

The other five former direct proof dependencies are replaced as direct dependencies
by the two new nodes, but remain below the geometric input's existing generic tools:
`lem-pc-flat-bounded-complex-descent`,
`lem-pc-noetherian-bounded-coherent-pseudo-coherent`, `lem-pc-coherent-hi`,
`lem-pc-noetherian-approximation-data`, and `lem-pc-rf-base-change-complex`.
Their modules are not claimed globally pruned.

The existing finite-free shortening theorems shrink U and therefore are not used:
`Sheaf.AlgebraicGeometry.FlatModelFiniteFreeShortening`,
`FlatModelFiniteFreeConstruction`, `FlatModelFiniteFreeComparison`,
`FlatModelFiniteFreeStructuralData`, and `FlatModelFiniteFreeQuasiIso`.
They were not imports or proof dependencies of this item originally.

## Where the brief, the DAG or earlier work was wrong

The stated proof dependencies do not expose the needed fixed-affine model followed by
shortening in the specified interval. In particular, the existing finite-free theorem
only works on a smaller neighbourhood, and its source module
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex` depends on
this item through ProperFlatCechModel, so importing it here would be circular.
The new geometric statement is an interface bridge to the proper-support perfect
image and affine representative theorems, not a second definition of perfectness.

Sources checked online: Stacks Tags 0B91(2), 0A1H and 068V. The repository lists the
Stacks source but has no literature/stacks-project checkout on this machine.
LeanSearch returned Internal Server Error; this is recorded as unavailable, not as
an absence result. LeanFinder, Loogle and actual Mathlib grep were also run and found
no exact result. The searches and their logged queries are attached to the new nodes.
Blueprint searches for proper flat perfect, 0B91 and 068V found no exact imported node.
An audit of the DAG with the delivery overlay found no missing dependency id and no
cycle through any delivered node. It did expose an already existing cycle below the
affine derived equivalence: `lem-pc-affine-derived-unit-isomorphism` and
`new-affine-derived-unit-homology-isIso` cite each other through proof/statement
edges. The baseline had other pre-existing cycles as well. These unowned nodes were
not edited; the maintainer should repair their metadata. The new shortening plan uses
the ordinary Mathlib tilde/global-sections equivalence directly, avoiding the derived
equivalence for this purely chain-level argument.

The blueprint ancestor helper could not follow created.item (which is a module name);
the explicit parent blueprint.from identifies lem-pc-coherent-hi and is used unchanged.

Generic tools of other units are named in the new nodes' plans:
proper-support perfect direct image (Noetherian approximation and proper coherence),
affine bounded-projective models and the Mathlib tilde/global-sections equivalence
(passage to section modules),
and the finite-free/flat-opcycle tools (nonnegative representatives). These serve
as algebraic interfaces and do not replace the coherence unit's route. The maintainer
can record their tool status if the unit-route review requires it.

## New nodes

`lem-pc-proper-flat-finite-presentation-model` corresponds to the new
ProperFlatFinitePresentationModel module and records the fixed-U geometric construction,
source, complete numbered proof, search results and exact Lean signature.

`lem-pc-affine-finite-presentation-flat-shortening` corresponds to the new
AffineFinitePresentationFlatShortening module and records the independent affine
cancellation argument, source, complete numbered proof, search results and exact signature.

No statement or definition was changed, no forced adaptation was needed, and no change
record is added.

## Second reading by G3

1. PASS: compared every delivered module to the repository. The sole existing
   declaration's complete signature is byte-for-byte identical, and its original
   docstring, visibility and four public imports are unchanged. Both added imports
   are proof-only. There are no changed definitions or target statements.
2. PASS: compiled all three modules together through lcompile.py in import order,
   without warnings (5.0, 4.5 and 5.8 seconds). A scratch copy with explicit
   `#print axioms` for all three declarations compiled: each uses only propext,
   Classical.choice, Quot.sound and sorryAx. The only direct holes are the two
   reported public theorem bodies; there are no definitions or forbidden features.
   The upper theorem is a proved reduction, not an axiom-free closure.
3. PASS: read both new signatures and their complete docstring arguments. Checked
   empty schemes/zero ring, b<=d, d=0, nonfree finite projectives, and arbitrary
   nonaffine base changes. Finitely presented sheaves are quasi-coherent in the
   library's convention. Properness plus local finite presentation gives the
   finite-presentation hypothesis of Stacks 0B91(2); 0A1H supplies the specified
   approximation route. The shortening argument uses finite cokernels, local
   Nakayama, a split surjection onto the top projective, and cancellation of a
   contractible pair. Its induction never introduces negative terms. Both lower
   statements are strictly separate parts, not a renamed copy of the item.
   Independent LeanFinder searches for contractible-summand cancellation and
   perfect base-change pushforward, Loogle `CochainComplex, HomotopyEquiv`, and
   Mathlib/library grep found generic tools but no exact theorem. Existing local
   finite-free shortening changes the open and cannot replace fixed-S shortening.
   Neither open lemma can be closed by a few-minute application of an existing
   result; both require substantial affine-model or complex constructions.
4. PASS: read the upper proof top down. It genuinely composes the two comparisons
   on the same standard fibre product, obtains injective resolutions from the
   Grothendieck-abelian instance, derives fibre vanishing from the zero C term,
   applies shortening, and composes D-to-B-to-C isomorphisms. All imports serve
   signatures or the proof. Checked all six old direct proof dependencies against
   the overlay DAG: only proper-Noetherian-stage is absent from the new proof
   closure, as the pruning section says; the other five remain below the new
   geometric input. Read sk-thm-picard-coherence.json: the approximation, proper
   coherence and degreewise Nakayama route is retained, and no realized field
   or unit statement is changed. Generic affine/projective tools do not replace
   its geometric step.
5. PASS: existing node changes are exactly proof, proof_deps and proof_origin.
   For each of the three nodes, proof_deps equals the union of the proof-step
   uses; the original node's steps match the actual Lean reduction. Both new
   nodes have their source, searches, creation and blueprint records, same unit
   and chapter, and signatures matching their separate theorem modules.

Second reading changed only this report by adding the independent review and
verification evidence. No Lean proof or statement repair was needed. This remains
a decomposition: one original hole closed and two lower holes added, local net -1.
