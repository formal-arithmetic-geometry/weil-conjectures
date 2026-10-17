## What changed

Repaired the returned duplicate-theorem delivery against the current main source.
Removed the local `AlgebraicGeometry.ProEtale.relativeMapEquiv_target` and
`relativeMapEquiv` declarations, restored the existing proof-only
`import all Sheaf.Paper.ProEtalePointComponentsMaps`, and use its existing
correspondence and target-naturality theorem in `testProjection_natural`.
The duplicate has identical explicit binders and is not a different statement.
Compared every changed hunk with the current source; retained all unaffected code and the
unchanged public theorem signature. This is a construction and proof repair of the current
six active holes, rather than an unchanged re-push.

Completed `lean/Sheaf/Paper/GeometricFieldProfiniteDenseSubsite.lean` and repaired all
helpers disabled at the upstream sync. The public theorem and its hypotheses are unchanged.

Restored `TestLC.fromIntegers`, `TestLC.projection_toIntegers`, and `TestLC.to_from`
using the explicit first spectrum coordinate already constructed in this file. The local
coefficient/source/target universes are independent, so integer coefficients typecheck.

Reused the proved private `specMapEquiv`, `specMapEquiv_apply`,
`profiniteProjection_natural`, `relativeMapEquiv`, and `relativeMapEquiv_target`
from `Sheaf.Paper.ProEtalePointComponentsMaps`. Restored `testHomEquiv` by transporting
this existing spectrum correspondence along the explicit test-scheme isomorphism and
homeomorphism. Proved `testProjection_natural` and `testHomEquiv_map` from the imported
naturality laws. The second reading removed three duplicate declarations and their
now-unused local `TestLC.ringMapEquiv` construction.

Proved `affineClassification` by taking global sections, installing the algebra structure
from the structural scheme map, using the weakly-etale Spec/algebra criterion, and applying
the existing local `classification`. The isomorphism's structural equation is proved from
`AlgEquiv.commutes`, the pullback projection equation, and `Spec.map_preimage`.

Retained `import all Sheaf.Paper.ProEtalePointComponentsMaps` and added the proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`. The DAG proof and
dependencies now describe the actual argument. No consumer adaptation is needed: all changed
or added helper definitions are private, the public import is unchanged, and the sole public
theorem's signature is unchanged. The direct external consumer found by
`tools/downstream.py --uses geometricFieldProfiniteDenseSubsite` is
`Sheaf.Paper.GeometricFieldProEtaleEvaluation`; its use of the theorem remains identical.

Validation: the entire repaired module compiles cleanly through `lcompile.py` in under
six seconds. No `sorry` occurs in the delivered module. The proof includes empty profinite
spaces and zero target rings: the ring-map inverse laws use all-prime localization equality
and spectrum identities without a nonempty/nontrivial assumption. The final topology proof
retains empty covering families. The unit's fixed statement and realized steps are unchanged.

## Proved and sorry left

Closed all six active holes in the current main version:

- `TestLC.fromIntegers`: replaced the holed definition by the explicit
  `LocallyConstant.liftPrimeSpectrum` construction.
- `TestLC.from_to`: proved the scalar-extension inverse law by equality in all prime
  localizations.
- `TestLC.pushout`: constructed the pushout cocone universal property from the proved
  integer restriction/extension inverse laws.
- `AlgebraicGeometry.ProEtale.testFullyFaithful`: proved bijectivity of every map on Hom sets
  using the explicit Hom equivalence and its functor-map identity.
- `AlgebraicGeometry.ProEtale.affineClassification`: constructed the required isomorphism
  over Spec K from global sections and the weakly-etale algebra classification.
- `AlgebraicGeometry.ProEtale.geometricFieldProfiniteDenseSubsite`: assembled full
  faithfulness, cover density, and preservation/reflection of covering sieves.

All belong to node `lem-weil-pbc-geometric-field-profinite-dense-subsite`. Five theorem
holes proved and one holed definition repaired: six textual holes closed, zero holes added,
zero holes left. No split-off obligations. Also restored and proved the disabled private
`projection_toIntegers`, `to_from`, `testProjection_natural`, `testHomEquiv_map`, and
`testTopologyReflect` lemmas. These were commented out in current main and are not counted
as active holes. The final theorem uses the existing profinite test-object theorem as intended.

## No longer needed

No import or whole module is pruned. Retained the component-map module and its node
`lem-weil-pbc-proetale-point-components-maps`: its spectrum correspondence, relative-map correspondence,
and naturality helpers are now used directly. The previous claim that this dependency
was pruned is withdrawn.

Removed the unused private `testComponentsHomeo` and `testAffine` declarations.
The second reading also removed the duplicate local `specMapEquiv`, `specMapEquiv_apply`,
and `profiniteProjection_natural` and the now-unused `TestLC.ringMapEquiv`. The
connected-component equivalence, affine equivalence, and profinite-Hom helpers of the
imported module are unused by this route. All four imports are used by the statement or
proof. No DAG node is claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The upstream sync had commented out helper definitions while leaving their consumers active.
The item therefore initially failed to compile, with six active textual holes in current main.
The old proof depended on upstream APIs removed during the sync. The spectrum-coordinate and relative-pullback
correspondences and their naturality are reused through the retained proof import.
The current `Spec.homEquiv` already returns an ordinary ring-category morphism; the obsolete
opposite-category conversion is unnecessary.

The landing check correctly found that the previous delivery redeclared the existing
`relativeMapEquiv_target` word for word. This retry removes that duplicate and its local
`relativeMapEquiv`, restores their proof import, and restores the corresponding DAG edge.
No statement is disputed. The previous second-reading section was removed because this
changed delivery needs its own independent reader. No target, public signature, or unit route
changes. No new DAG
nodes, new sorries, public instances, or forced consumer adaptations are introduced.

Change record: `coord/changes/R2-geometric-field-profinite-private-helpers.md`.

## Second reading by R2

1. Signatures and visibility: PASS. Read the complete module and diff against the repository.
   All existing explicit declaration signatures are unchanged; the sole public theorem and
   the public imports are byte-for-byte unchanged. The private scalar-extension helpers have
   the independent coefficient universes declared in the change record. The five restored
   lemmas were commented out at the upstream sync. The two deleted existing declarations are
   private and unused. No consumer needs adaptation.
2. Proof and data: PASS. The final module compiles cleanly through `lcompile.py`. Checked
   `#print axioms` for all 27 declarations in a scratch copy. The scalar-extension, pushout,
   stalk, separation and algebra-classification arguments use only `propext`,
   `Classical.choice`, and `Quot.sound`. The final theorem and some scheme constructions also
   inherit `sorryAx` from imported obligations (the specified test functor already uses the
   open `weaklyEtale_toSpecZ_profiniteToScheme` instance). No declaration here has a local
   hole, forbidden axiom or trust bypass. Scalar extension is an explicit spectrum lift;
   classification uses an explicit algebra map and its proved bijectivity; the scheme
   isomorphism comes from the proved pullback universal property. No arbitrary data are
   selected from an unproved existence statement.
3. Split statements and edge cases: PASS. No split-off statements or new nodes. Rechecked
   the empty profinite space, singleton space, zero target ring and empty cover cases.
   Neither the localization inverse laws nor the finite-family arguments introduce a
   nonempty or nontrivial hypothesis. Searched the library by spectrum/map/coordinate
   terminology and compared the existing imported helpers; found and removed the three
   remaining duplicates instead of restating them.
4. Shortest route and pruning: PASS after repair. The existing imported spectrum and
   relative-map correspondences supply the Hom equivalence directly. Removed their local
   copies and the unused ring-map equivalence. All four imports are required: the public
   import supplies the functor in the statement, the component-map import supplies the
   correspondence, the affine comparison supplies the cover-dense basis and finite
   refinement, and the weakly-etale import supplies the Spec/algebra criterion. A scratch
   compile without the last import fails at that criterion, so it is retained as a plain
   proof import. No old proof dependency or whole module becomes unnecessary. Read
   `dag/units/sk-thm-properbasechange.json`; its statement and all realized steps remain
   unchanged and are not bypassed.
5. DAG and report: PASS after repair. The seven proof dependencies are unchanged and equal
   the union of the proof steps' `uses`. Updated step 2 and `proof_origin` to name the reused
   spectrum and naturality helpers. Preserved all other existing node metadata. The report
   lists all six original textual holes closed (five theorem holes and one definition
   repair), zero holes added, and the helper removals. The change record describes only
   private construction changes. No new nodes require review.

Second-reading changes: removed duplicate `specMapEquiv`, `specMapEquiv_apply`, and
`profiniteProjection_natural`, and the unused `TestLC.ringMapEquiv`; corrected this report,
the private-helper change record, and the DAG proof narrative. Retained the valid proofs.
