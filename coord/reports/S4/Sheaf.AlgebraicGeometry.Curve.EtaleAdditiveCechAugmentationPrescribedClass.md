## What changed

The signature of AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_augmentation_prescribed_class
is unchanged. Its proof now transports the source total cycles by a chain map, identifies the
prescribed target global class using injectivity of cY.globalEquiv, and applies the actual alpha
cochain map to that homology equality. Injectivity of iCycles identifies the transported alpha
cycle with the alpha image of the transferred global cycle. Homology projection naturality
then gives the required equality with the transported beta cycle.

Five new modules separate the argument. EtaleAdditiveCechAlphaMap proves the chain-map equation
for the explicit alpha: the two horizontal restrictions cancel, the vertical equation is
sheaf-map naturality, and the total sign in Cech degree zero is one.
EtaleAdditiveCechCanonicalCoefficientTransfer generalizes the proved pointwise transfer
calculation to an arbitrary coefficient morphism. Its two private terminal-adjunction lemmas
are adapted from EtaleResolutionSectionCanonicalGlobalTransferPointwise; the public proof
uses exactFunctor_resolution_cocycle and Ext associativity, and has no sorry.
EtaleAdditiveCechPullbackAugmentedTransfer constructs the comparison I -> g_*J directly:
g_* preserves injectives, and Injective.factorThru, exact₀.descToInjective,
exact_succ.descToInjective and CochainComplex.mkHom assemble its components.
EtaleAdditiveCechPullbackChainTransfer combines that lift with the proved canonical formula.
EtaleAdditiveCechPullbackTotalTransfer states only the remaining tuplewise double-complex
construction for a supplied augmented comparison. It assumes no prescribed global cycle,
canonical cohomology equivalence, or equality of total classes.

The sandbox compiled in import order through lcompile.py, with no compiler errors or warnings.
The deliver3.py --no-push dry run printed OK; no delivery was pushed.
The existing item node and the five new nodes record the actual Lean route. No definitions,
existing signatures, target statements, or modules held by other workers were changed.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_augmentation_prescribed_class
(lem-pbc-etale-additive-cech-augmentation-prescribed-class), by reduction to one smaller
construction theorem. This is a decomposition: one original hole closed and one lower hole
added, net zero holes. It is not a claim that the import closure is sorry-free.

Also proved the new public declarations:
- AlgebraicGeometry.Scheme.Modules.exists_additiveCech_alpha_map
  (lem-pbc-etale-additive-cech-alpha-map).
- AlgebraicGeometry.Etale.resolutionSection_canonical_coefficient_transfer
  (lem-pbc-etale-additive-cech-canonical-coefficient-transfer).
- AlgebraicGeometry.Scheme.Modules.exists_additiveCech_pullback_augmented_transfer
  (lem-pbc-etale-additive-cech-pullback-augmented-transfer).
- AlgebraicGeometry.Scheme.Modules.exists_additiveCech_pullback_chain_transfer
  (lem-pbc-etale-additive-cech-pullback-chain-transfer).

The only sorry left in the delivered files is
AlgebraicGeometry.Scheme.Modules.exists_additiveCech_pullback_total_transfer
(lem-pbc-etale-additive-cech-pullback-total-transfer). Its proof is exactly `:= by sorry`;
its docstring and node give the complete tuplewise construction and compatibility calculation.
There are no anonymous or private holes and no sorry inside data definitions.

## No longer needed

Removed the proof import Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalTransfer.
The assigned theorem no longer uses lem-weil-pbc-etale-resolution-section-canonical-transfer,
or its global/open transfer theorem branches (EtaleResolutionSectionCanonicalGlobalTransfer
and EtaleResolutionSectionCanonicalOpenTransfer). The new generalized global coefficient
calculation uses the exact-functor cocycle theorem directly and does not need the canonical
open-cohomology transfer. These are route-local pruning statements; other targets may still
reach those modules. The normalization and TopologicalInvariance public imports are retained
for the unchanged statement.

No affine-cover augmentation equivalence, injective Cech acyclicity, columnwise spectral
sequence comparison, or normalized edge inverse is needed. Their modules were inspected but
were not imported. No UNIT statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node grouped the comparison construction, total-complex naturality, canonical
class calculation, and replacement of the prescribed target representative into a single
proof step. The new route makes the last two steps real Lean proofs. For the resolution lift
it is simpler to use termwise injectivity of g_*J (right adjoint to mono-preserving inverse
image) than to lift from a possibly noninjective inverse-image resolution.

The existing augmentation-homology equivalence needs a separated scheme with an affine
cover, so it cannot be applied to this item's arbitrary open families. The existing
resolution-transfer theorem treats the identity scheme map and also does not give the
needed pullback/refinement total map. The canonical transfer theorem resolves precisely
g^*G on the target; this item instead resolves the additive structure sheaf and includes
an adjoint coefficient morphism. The proved generalized coefficient-transfer formula
handles that difference explicitly, rather than silently identifying the coefficients.

Edge cases checked in the argument: n=0 uses homology naturality without selecting a negative
boundary; an empty index type gives zero totals and zero augmentations; empty intersections
have zero structural functions; identity g and zero sections obey the same comparison
equations. Neither the remaining lemma nor its use introduces a covering assumption.

Mathlib searches were run through msearch.py (searches.jsonl): LeanFinder, Loogle and grep
returned generic adjunction, injective-resolution and homology naturality APIs. LeanSearch
returned HTTP 500 and is recorded as unavailable, not as a negative result. Blueprint
searches for augmentation, refinement, and double complex found no exact statement of
these explicit component equations. Stacks Tags 01EQ, 01FD, 01FB and 03P2 were read online;
the local literature checkout is absent on this machine.

## New nodes

lem-pbc-etale-additive-cech-alpha-map, module EtaleAdditiveCechAlphaMap: the explicit global
augmentation is a cochain map for any open family. Fully proved, including both component
calculations and the total sign; no cover or finiteness hypothesis is needed.

lem-pbc-etale-additive-cech-canonical-coefficient-transfer, module
EtaleAdditiveCechCanonicalCoefficientTransfer: a supplied augmented resolution comparison
computes inverse-image pullback followed by its adjoint coefficient map. Fully proved;
normalization is supplied by the canonical comparison fields and the existing exact-functor
resolution-cocycle theorem.

lem-pbc-etale-additive-cech-pullback-total-transfer, module EtaleAdditiveCechPullbackTotalTransfer:
the remaining construction of the total map from a supplied augmented comparison, with
only the alpha square and beta equation on cochains. This is strictly a part of the original
argument; it contains no global class comparison, prescribed cycle or equality of total
homology classes. It is the one new sorry.

lem-pbc-etale-additive-cech-pullback-augmented-transfer, module
EtaleAdditiveCechPullbackAugmentedTransfer: constructs the augmented structural resolution
comparison by injective extension and combines it with the total-transfer lemma. No local
sorry remains. The Mathlib leaf lem-sp-right-adjoint-preserves-injectives is used as a tool.

lem-pbc-etale-additive-cech-pullback-chain-transfer, module EtaleAdditiveCechPullbackChainTransfer:
combines the augmented maps with the proved canonical coefficient-transfer formula.
No local sorry remains. All new nodes have the same chapter/unit and inherited blueprint
ancestor as the item; there are no change records or forced adaptations.

## Second reading by S4

1. **Interfaces: pass.** Compared every delivered module with the repository.
   Only EtaleAdditiveCechAugmentationPrescribedClass existed there; its diff changes
   two proof imports and replaces the proof body. Its declaration signature and
   definitions are byte for byte unchanged. The other five modules are new.
   The existing node changes only proof, proof_deps and proof_origin. No change
   record or forced adaptation is required.

2. **Kernel checks: pass as a decomposition.** Compiled all six modules in import
   order through lcompile.py without errors or warnings. A scratch module printed
   axioms for all six public declarations. exists_additiveCech_alpha_map and
   resolutionSection_canonical_coefficient_transfer use only propext,
   Classical.choice and Quot.sound. The original declaration, augmented-transfer,
   chain-transfer and total-transfer declarations additionally use sorryAx.
   The sole local hole is exists_additiveCech_pullback_total_transfer, exactly a
   named public theorem with `:= by sorry`. No prohibited declaration or option,
   hollow definition, or data definition choosing an undetermined witness occurs.
   Resolution comparison witnesses are obtained inside proofs, not used to define
   data from the remaining existence hole. The scratch file was removed.

3. **Split statements: pass.** Read the actual constructions in Normalization,
   EtaleAdditiveStructureSheaf and EtaleResolutionSectionTransfer, and the public
   statements and proofs of all five new modules. Read Stacks
   [01EQ](https://stacks.math.columbia.edu/tag/01EQ),
   [01FD](https://stacks.math.columbia.edu/tag/01FD),
   [01FB](https://stacks.math.columbia.edu/tag/01FB), and
   [03P2](https://stacks.math.columbia.edu/tag/03P2).
   Their covering assumptions concern inversion or cohomology comparison, not the
   coordinate maps used here. The remaining theorem needs neither inversion nor
   acyclicity. Its supplied augmented comparison is exactly what beta naturality
   needs; its alpha equation is terminal restriction naturality. It assumes no
   cycles, canonical comparisons, prescribed class, or equality of total classes,
   so it is strictly smaller than the item. The generalized coefficient theorem
   has arbitrary H and an adjoint coefficient morphism, unlike the existing
   pointwise theorem resolving precisely g^*G. The lift uses injectivity of g_*J
   and exactness of I, not exactness of g_*J. Checked n=0, empty index types,
   empty intersections, identity pullback and zero cochains: all coordinate and
   sign equations still hold, and no negative degree or cover is introduced.
   Expanded the remaining theorem's docstring and node proof to specify k_y,
   the coordinate composite, deletion squares, total signs, and the structural
   section identification needed for beta.

   Independent msearch queries were LeanFinder “Cech complex functor map induced
   by natural transformation restriction of presheaves”, Loogle
   `"cechComplexFunctor"`, and grep
   `sectionTransfer|cechComplexFunctor_map|total_map`. Also searched lean/Sheaf,
   lean/WeilConjectures and the upstream WeilConjectures checkout. The relevant
   APIs are cechComplexFunctor and ιTotal_map; neither supplies this cross-site
   refinement or the lifted structural beta equation. AbelianCechBetaNaturality
   is for a fixed topological cover and coefficient universe; the existing
   CechComparison inverse-image compatibility assumes covers and concerns
   topological comparison systems. Neither closes this hole by application.
   Completing the remaining construction requires the actual tuple restriction
   map and beta identification, rather than a few-minute lemma application.

4. **Route and pruning: pass.** Read the proof from the item downward. The item
   uses chain-transfer and alpha-map; augmented-transfer constructs the resolution
   lift, while coefficient-transfer proves its canonical class formula directly
   with exactFunctor_resolution_cocycle. The imports needed only by proofs are
   plain imports; public imports supply names in public signatures. The sole
   removed import and its canonical-transfer node are already listed above.
   The other old proof dependency, def-pbc-etale-additive-cech-normalization,
   remains needed and publicly imported, not pruned: its definitions occur
   throughout the statement and proof. Checked sk-thm-p1.json realized: this
   item and its replaced dependency are not realized unit steps; the smooth-curve
   Artin-Schreier comparison remains the blueprint ancestor and route. No realized
   unit node or module is bypassed. Net hole reduction is zero, as reported.

5. **DAG: pass after metadata correction.** Matched every new lean.statement with
   its declaration and inspected statement dependencies, proof steps and their
   proof_deps unions, provenance, searches, created fields, chapter/unit and
   blueprint ancestry. The item records its homology-natural reduction; the
   wrappers cite exactly the two transfer constructions they apply. Corrected
   alpha-map proof_origin.document from Tag 01FD to Tag 01EQ to agree with its
   source place. Synchronized the total-transfer node proof with the expanded
   docstring. No Lean signature, proof term, definition or import changed during
   this second reading.
