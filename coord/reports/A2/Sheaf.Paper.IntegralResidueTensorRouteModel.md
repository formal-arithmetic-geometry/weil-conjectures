## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorRoute_model`
with its original signature. The proof directly specializes the complete generic
counit-normalized calculation and the ordinary pullback braiding identity.

`Sheaf.Paper.IntegralResidueTensorRouteGeneric` proves the generic calculation.
The braiding calculation checks each Koszul tensor summand, passes through the homotopy
quotient, computes on K-flat-image representatives, and transports along resolutions.
The route then follows from presentation normalization, the tensor comparison's counit
equation, and counit naturality. The ordinary internal-module braiding calculation is
checked after the balanced tensor epimorphism and transported to ordinary pullback.

The new counit module, model and derived-monoidality modules expose proved defining/projection
equations. The existing explicit ordinary coefficient and canonical counit receive names
for this API. All original concrete definition bodies, declaration kinds and explicit
result types are retained. The model uses the existing canonical alias for its original
derived braiding. The generic derived monoidal constructor uses `Monoidal.copy` to
expose its tensor comparison without expensive reduction; all four copied fields have
`rfl` equality proofs, so its mathematical data are unchanged. Change record: `coord/changes/20261017-A2-residue-tensor-counit-api.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorRoute_model`
(node `new-integral-residue-tensor-route-model`). No new hole is added. This is a proof,
not a decomposition. There is no `sorry` in any delivered module. Split off: zero.

Also proved `residue_tensor_route_model_generic` and
`AlgebraicGeometry.ProEtale.CondensedRing.residue_ordinary_pull_braiding`
(node `new-integral-residue-tensor-route-generic`),
`CategoryTheory.Functor.derivedTensorPresentationIso_normalization`,
`CategoryTheory.Functor.residueDerivedMonoidal_δ`,
`CategoryTheory.Mod.residueDerivedTensorIso_eq`,
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangePullMonoidal_δ`,
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangeTensorCounit_isLeftDerivedFunctor`,
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangeTensorIso_eq`,
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangeTensorModelTarget_eq`, and
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangeTensorModelMap_eq`.
The counit, model and monoidality nodes list the corresponding declarations.
`IntegralResidueTensorPresentation` itself is unchanged; the counit API is in the new
`IntegralResidueTensorCounit` module to keep each file below the remote compiler limit.

The proposed hole `AlgebraicGeometry.ProEtale.CondensedRing.residue_tensor_route_concrete`
and its proposed node were removed. They only unfolded the target's wrappers and did not
constitute a proper split.

Validation: all five delivered modules, including the separate counit API, compiled
together in import order with
`lcompile.py --all`, including the direct Koszul calculation and concrete specialization.
A fresh scratch import with `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound` for the generic calculation and normalization theorem. The concrete target,
ordinary braiding specialization and existing concrete constructions additionally inherit
`sorryAx` from already-open coefficient/sheaf infrastructure; no other axiom occurs.
Before separating the counit API into its own module, unchanged copies of `IntegralResidueScalarRouteModel`, `IntegralResidueTensorGeometry`,
`IntegralResidueTensorSquare`, `IntegralResidueProjectionNormalization` and
`IntegralResidueComparisons` compiled against the equivalent five-module overlay. The separation preserves all declarations
and existing construction bodies; final delivery compilation and probes check the split.
A source import-closure audit shows that TargetsCheck adds only the proved generic helper
module and the proved counit API module and reaches no new existing hole. The item's own closure also reaches no new hole.
All existing declaration signatures were checked byte-for-byte and all DAG declaration
lists and proof-dependency unions checked mechanically. Before the compiler-limit module
split, dry run: `deliver3.py A2 Sheaf.Paper.IntegralResidueTensorRouteModel --no-push`
returned OK; compilation and preflight passed (dry-run commit `4e306762ab`). The delivery
command repeats these checks before pushing.

## No longer needed

Removed the item's redundant direct proof imports of
`Sheaf.Paper.IntegralResidueDerivedMonoidal`,
`Sheaf.Paper.IntegralResidueOrdinaryMonoidal` and
`Sheaf.Paper.IntegralResidueTensorPresentation`; the model publicly imports them already.
The generic module publicly imports only the model and privately imports the homotopy
braiding construction. The broad upstream Etale/Derived/UpperStarMonoidal/Braided module
is unnecessary: the needed identities are proved directly inside the generic calculation.
No public import was privatized or removed.

Every original proof dependency remains used: tensor presentation and its counit,
ordinary monoidality, derived monoidality and its comparison, and the explicit tensor model.
No old proof-dependency node or existing module is withdrawn. Pruned existing modules: none.

## Where the brief, the DAG or earlier work was wrong

The first report called the unproved concrete bridge strictly smaller than the target.
It had the same content after unfolding wrappers. The second reader removed it and proved
the target from the actual generic calculation rather than moving the hole.

The earlier wrapper changes dropped explicit result types, altered interface definitions,
and caused expensive conversions and a downstream mismatch. The second reader restored
all original concrete definition bodies and wrapper boundaries, then exposed proved APIs.
No target hypothesis, conclusion or coefficient object changed.

The earlier DAG listed a nonexistent `residueExchangeTensorIso_normalization`.
It now lists the actual generic normalization theorem and concrete defining equations.
The new node records the complete proved calculation rather than the deleted concrete hole.

The original broad upstream braiding import newly reached an unrelated open etale
localization theorem. An attempted extraction with a public re-export was refused by the
stage-3 upstream gate, which forbids removing those upstream declarations or changing their
public imports. The final delivery leaves every upstream file untouched and computes the
Koszul and isomorphism-transport identities inside the proof, as the gate permits. No
extracted module, relocated declaration, duplicate public theorem or associated node is
part of this delivery.

## New nodes

`new-integral-residue-tensor-route-generic` records the complete generic tensor-route
calculation and ordinary internal-module braiding specialization. Both are proved.
The coefficient and homotopy representative are arbitrary; no flatness hypothesis on either
is added. Actual LeanSearch, LeanFinder, Loogle and grep searches were run and recorded.
`new-integral-residue-tensor-counit` records the proved defining API for the existing
canonical tensor presentation, in its own module. It introduces no new mathematical
construction or hole. Existing narrow tensor, homotopy and derived-category constructions
are reused. The change
record above declares the new supporting API and its users.

## Second reading by A2

1. Compared all delivered existing modules with the shared repository. Every existing
signature is byte-for-byte unchanged; the original declaration kinds and concrete definition
bodies are retained. The pullback wrapper and coefficient interface are unchanged.
The generic monoidal constructor now exposes its fields through `Monoidal.copy`; four
`rfl` field equalities verify that the construction is the same, and this body change is
declared in the change record. The named counit and comparison equations are declared additions.
The generic braiding alias is the same construction by definition; the change record
reopens any affected definition review. No arbitrary witness of unproved existence supplies
data. Verdict: interfaces preserved and changes declared.

2. Read the ordinary tensor epimorphism proof, Koszul summand calculation, quotient descent,
K-flat representative calculation, naturality transport, cancellation, normalization and
counit naturality. Exactness supplies the pullback counit isomorphisms. K-flatness is used
only for auxiliary resolutions, never added to P or to the residue coefficient. All new
definitions contain concrete data, and no forbidden declaration or new hole remains.
Compile and axiom results are recorded above. Verdict: a complete proof of the original item.

3. Rejected the proposed restatement split. The remaining generic theorem and ordinary
braiding theorem are fully proved. Checked zero coefficient, zero representative and
identity-functor cases: all cancellations use actual isomorphisms or presentation epis,
without coefficient flatness. Searched for existing ingredients with different queries;
the direct component calculation avoids the unrelated holes of the broad upstream import.
Verdict: no split-off hole or duplicate public theorem.

4. Followed the proof from the target downwards. The original four proof dependencies are
all still used. Checked `dag/units/sk-thm-properbasechange.json`, including its realized
statements/steps: no unit route is changed. Removed redundant direct imports and the
unnecessary broad braiding dependency. Verdict: original route retained; no old dependency
node is unused.

5. Checked all nodes against the actual Lean declarations. Corrected proof steps, dependency
unions, origins and declaration lists; removed the nonexistent normalization name and
replaced the concrete restatement node with the proved generic node. Existing node
statements, statement dependencies, sources, units and chapters are unchanged. The proved
counit API is in its own module and node; the original presentation module is untouched. The new node
has source, actual searches, creation record, blueprint provenance, Lean statement and
declaration names. Verdict: records match the delivered proof.

Second-reading changes: closed the concrete specialization; removed the restatement hole;
restored all original interfaces and concrete construction bodies; exposed the generic
monoidal comparison with four reflexive field equalities; repaired normalization and
projection APIs; replaced the broad braiding import with a direct component calculation;
separated the proved counit API into a small module to satisfy the compiler time limit;
corrected imports, source/proof docstrings, DAG records, change record and report.

Final elaboration check: the complete five-module set compiled after the counit-module
split. The concrete specialization first elaborates the generic application as a local
fact and then matches it against the original target. A blank-line style warning was
removed before the final delivery dry run.
