## What changed

Recovered the complete reviewed D4 proof from 02838eb560 and the current-definition
adaptation from the route experiment. The parent proves the homology equation using
private exact-derived, exact-complex and coefficient-homology naturality lemmas.
It first proves two defining equations for the source isomorphism and H2's raw arrow,
then rewrites with them rather than broadly unfolding dependent equality transports.
The experimental Route helpers have been restored as private helpers in the parent;
no experimental namespace or helper module is delivered.

Recovered two fully proved supporting modules: AffineTildePushforwardHomologyFactorization
and AffineTildeCoefficientPushforwardHomologyCoordinates. The factorization imports
MixedTensorUnderlyingHomology and calls its existing mapHomologyIso_hom_comp, exposed
in place by removing only its private modifier. The inverse consequence occurs once,
in the factorization module, and the parent imports it. All copied generic forward,
iterated-data and inverse lemmas from D4's parent were removed.

The parent and supports have local bridges between Scheme.Modules and the explicit
SheafOfModules category and local irreducibility attributes for construction definitions.
They add no mathematical assumptions. The existing parent signature, definitions,
public import and docstring are unchanged. Route fields and matching Lean records
are updated. Change record: coord/changes/G3-affine-homology-shared-comparison-api.md.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.affineTildeDerivedTensorToPushforward_homology
(lem-pc-affine-tilde-derived-tensor-homology-coordinates).

Both new supporting declarations are proved:
AlgebraicGeometry.affineTildePushforwardHomologyFactorization
(lem-pc-affine-tilde-pushforward-homology-factorization) and
AlgebraicGeometry.affineTildeCoefficientPushforwardHomologyCoordinates
(lem-pc-affine-tilde-coefficient-pushforward-homology-coordinates).
The accessible inverse consequence AlgebraicGeometry.mapHomologyIso_inv_comp and
all seven parent private helper lemmas are also proved. The existing shared forward
comparison's proof is unchanged. No sorry remains in any delivered module and no
sorry is added or split off. Net holes closed: one; this is a complete proof.

First-worker validation: the recovered full set compiled cleanly, and the parent with its
private helpers compiled in 56.5 seconds. A fresh import/axiom probe of the rebuilt
sandbox parent, both supports and both composition APIs compiled in 1.6 seconds:
all five declarations use only propext, Classical.choice and Quot.sound.
The mandatory deliver3.py --no-push dry run printed OK at commit 1a26a9ad26:
the delivered set compiled and passed preflight except for the independent second
reading, which the second reader writes. Its complete declaration probes reported
no forbidden axiom. Nothing was pushed.

## No longer needed

Removed redundant explicit parent proof imports of
Sheaf.Algebra.Homology.AffineBaseChangeTildeCoordinates,
Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization and
Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel. Their required definitions
remain available through the existing public Mate import and the proved supports;
their DAG dependencies stay because those definitions are used. No existing module
is removed from the target import closure by this recovery.

No further open homology-coordinate leaf is needed. The parent needs neither the
geometric mate theorem nor the ordinary pushforward normalization existence theorem
in the cycle below this branch; it uses the actual ordinary comparison and derived
unit definitions. The existing mate/source-comparison/ordinary-exchange and ordinary
normalization interfaces stay for their other consumers. No K-flatness, boundedness,
quasi-coherence or invertibility of the tensor comparison is needed here.

The redundant generic iteratedHomologyData_comparison and mapHomologyIso_hom_comp
copies in D4's parent and factorization, and its inverse-composition copy in the
parent, are eliminated. They are not separate proof obligations. The new coefficient
module also replaces its public Mate import with
AffineTildePushforwardCohomologyNormalization, which already exports the module-model
and coordinate definitions used in its signature. Its new node states hphi and hpsi
explicitly and drops the redundant mate statement dependency. No additional module
is pruned from the parent's target import closure. The previous sandbox
Mate copy and experimental Route.HomologyNaturality file are omitted from the delivery.

## Where the brief, the DAG or earlier work was wrong

The statement is sound. The complete reviewed proof already existed; repeated splits
of this homology leaf were unnecessary. D4's return identifies an API visibility
problem: its generic copies duplicated private proved lemmas. This delivery fixes
that problem by exporting the existing theorem and importing it.

D4 predates H2's named counit and ordinary-target factorization. The raw-arrow equation
is adapted by change followed by Category.id_comp and associativity. The source-iso
equation is rfl. Eager unfolding through the dependent equality transport is avoided.
All generic naturality lemmas remain in the parent, respecting the no-file-splitting
rule. Zero rings, zero complexes, arbitrary integer degrees and unbounded complexes
are covered: every step is naturality, canonical-comparison compatibility or categorical
cancellation; no nonzero, boundedness or inverse-comparison hypothesis is introduced.

## New nodes

lem-pc-affine-tilde-pushforward-homology-factorization: recovered D4's fully proved
ordinary pushforward factorization. Its first step now cites the existing mixed-tensor
composition API and proves the inverse consequence by cancellation. Its Lean record
includes both public proved declarations and matches the source statement verbatim.

lem-pc-affine-tilde-coefficient-pushforward-homology-coordinates: recovered D4's fully
proved ordinary coefficient specialization. Apply the generic factorization to v,
distribute functors over composition and reassociate. This contains no derived counit
or source identification and is strictly an ordinary part of the parent's argument.
Its explicit additivity and zero-map instance bridges reuse existing instances.

No new open node is introduced. Both nodes inherit sec-picard-framework and
sk-thm-picard-semicon; the unit's realized statement/step lists are empty and unchanged.
The shared mixed-tensor node's Lean declarations list now includes its exposed API.

## Earlier second reading (a previous round; superseded)

1. Interfaces: PASS. Compared all four delivery modules with the repository using
   diff. The parent's existing theorem signature and docstring are byte for byte
   unchanged; no existing definition changed. MixedTensorUnderlyingHomology differs
   only by removing private from RingTensorCohomology.mapHomologyIso_hom_comp;
   its signature and proof are unchanged and the visibility change is recorded in
   coord/changes/G3-affine-homology-shared-comparison-api.md. The two supports are new.
   A scratch theorem with the repository's original parent signature accepts the
   delivered theorem directly, without the new local category instances: the
   instance bridges have not changed the meaning of its statement.

2. Proof and axioms: PASS. Independently compiled the four-file set in import order:
   MixedTensorUnderlyingHomology 27.2 s, factorization 48.4 s, coefficient coordinates
   56.8 s and parent 58.1 s; no errors or warnings. The narrowed coefficient import
   also compiled separately in 55.3 s. Searched all delivered Lean for sorry and
   forbidden declarations/escape hatches; none occurs. Fresh #print axioms probes
   for the parent, both supports, the inverse consequence and exposed forward API
   report only propext, Classical.choice and Quot.sound. The original-signature
   scratch theorem has the same axiom list. No data is selected from an unproved
   existence statement: the new data are existing category structures and instance
   bridges, and the equality transport is constructed from hphi.

3. Intermediate statements: PASS; no open statement is split off. Read both new
   signatures against their nodes and their docstring arguments. The factorization
   is precisely the defining pushforward map with the inverse composite homology
   comparison expanded. Its inverse lemma cancels the composite forward map and
   uses the existing proved composition API. The coefficient theorem specializes
   it to the four ordinary coefficient factors and distributes functors over
   composition. Neither restates the derived-counit calculation. For identity
   functors the inverse lemma reduces to inverse/forward cancellation; for the zero
   short complex the same categorical identities hold. The affine specializations
   admit zero rings, zero complexes and every integer degree; no boundedness,
   K-flatness or invertibility of m.comparison enters. Independently searched with
   leanfinder, loogle and grep using homology-composition/natural-transformation
   queries, and rg in lean/Sheaf and lean/WeilConjectures. Mathlib supplies the
   naturality APIs already used; the library supplies the forward composition API.
   No existing affine specialization was found. New-node search records include
   these checks. Read Stacks Tags 06Z0, 0AVW, 06Y6 and 0DJ8 online: these provide the
   exact-tilde and derived affine context; the displayed coordinate identities are
   proved from the actual library definitions, without invoking the stronger
   quasi-coherent pushforward equivalence or geometric mate existence theorem.

4. Route and pruning: PASS after one import repair. Checked the proof from its final
   equation backwards. exactDerivedHomology uses exact-derived naturality and the
   Q component formula; exactComplexHomology uses ordinary homology naturality;
   homologyFactorsh identifies the homotopy and complex coordinates;
   coefficientHomology uses restriction naturality, the inverse composite API and
   Mathlib's homologyMap_mapNatTrans. These justify each rewrite before the final
   ordinary factorization. All seven generic helpers remain private in the parent.
   Both direct support imports are needed there, including the inverse API.
   Replaced the new coefficient module's public AffineTildeDerivedTensorMate import
   by AffineTildePushforwardCohomologyNormalization, which supplies all definitions
   used in its statement. Its proof-only factorization import stays nonpublic.
   No old proof dependency was dropped: all four are used for definitions or model
   fields, as explained in No longer needed. No existing module is pruned from the
   target closure. Read dag/units/sk-thm-picard-semicon.json: its realized statement
   and step lists are empty and unchanged; this calculation does not replace the
   unit's semicontinuity or Grauert argument.

5. DAG agreement: PASS after updating the new coefficient node. Parent proof steps
   now describe the source/raw-arrow equations, exact homology naturality,
   m.comparison_eq and the two actual supports. The union of uses is proof_deps.
   The factorization node cites the exported mixed-tensor API; its Lean declarations
   also list the inverse consequence. The coefficient node cites its factorization.
   The three affine Lean statement records occur verbatim in their source files;
   the existing mixed-tensor statement record is unchanged. Existing nodes changed
   only stage-3-owned fields. The new nodes have source, proof, origin, searches,
   creation, blueprint, chapter, unit and Lean records and contain fully proved
   statements. Removed the coefficient node's redundant mate statement dependency
   and wrote its two scalar-map equality witnesses explicitly, matching its narrower
   import without changing the mathematical statement.

The first second-reader dry run compiled and passed its axiom checks, then fetched
a newer base containing OriginalCounitAdjunctionTransport. Preflight required that
new downstream user in the change record's Users table. Read its unchanged source,
verified that the new category instances are local and no adaptation is needed,
and added its row (unclaimed in the current claims directory).

Second reading changed only the coefficient public import, the corresponding new
node's prose/dependency and independent search evidence, the refreshed change-record
Users table, and this report. No proof,
existing statement, definition or hole count changed. One original hole closed;
zero holes added; zero split off.

The repaired second-reader deliver3.py --no-push run printed OK at c14d0c4ee5:
the full set compiled, all declaration probes passed, and preflight passed.

## Forced adaptations

Original MixedTensorUnderlyingHomology left RingTensorCohomology.mapHomologyIso_hom_comp private, so the new factorization module failed with an unknown-identifier error when referencing that theorem. The adapted file changes exactly one line, `private theorem mapHomologyIso_hom_comp` to `theorem mapHomologyIso_hom_comp`; its signature and proof are unchanged. This is necessary to reuse the existing comparison theorem and remove the duplicate proof.

## Second reading by G3

1. Interfaces: PASS. Compared every delivered module with the repository version. The
   existing parent target statement and docstring are byte-for-byte unchanged. The only
   existing declaration change is the intentional removal of `private` from
   `RingTensorCohomology.mapHomologyIso_hom_comp`; its signature and proof are unchanged
   and the change is recorded in the accompanying change record. A fresh scratch
   theorem using the repository's original signature accepts the delivered theorem
   directly, without local instance bridges. The two additional
   modules are new and their public imports match their statements.

2. Proof and axioms: PASS. Compiled all four modules in import order with
   `lcompile.py --all`; all completed without errors. A source scan found no `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. Independently compiled
   fresh `#print axioms` probes for the target, both supports, the inverse consequence,
   the shared forward API, and the original-signature scratch theorem; each uses only
   `propext`, `Classical.choice`, and `Quot.sound`. No definition contains postponed
   data or an arbitrary existence witness.

3. Intermediate statements: PASS. Read the two supporting statements and the exposed
   shared composition declaration against their Lean sources and DAG nodes. The inverse
   comparison is obtained by cancellation from the existing forward composition API;
   the coefficient statement is the ordinary specialization used by the parent. Neither
   restates the target, weakens a hypothesis, or introduces a new mathematical assumption.
   The edge cases described in the proof records (identity/zero maps, zero complexes,
   arbitrary degrees and unbounded complexes) are covered by categorical functoriality.
   Independent leanfinder, loogle, and grep searches for successive exact functors,
   `mapHomologyIso`, and natural transformations confirmed the available Mathlib
   infrastructure; `rg` found the shared forward API and no existing affine formula.

4. Route and pruning: PASS. Traced the parent proof from its final equality through the
   exact-derived and exact-complex naturality lemmas, `m.comparison_eq`, and the two
   ordinary support theorems. The narrowed imports are proof-minimal while retaining all
   definitions used in the target. The old redundant generic comparison copies are gone;
   the route and `No longer needed` record agree, and the unit's realized route is unchanged.

5. DAG agreement: PASS. The parent, factorization, coefficient, and adapted shared API
   records have statements, proof steps, dependencies, origins, and Lean declaration
   names matching the delivered files. New declarations have corresponding nodes, and
   the forced visibility adaptation has a change record. No open statement was split off.

Changed during this second reading: added this required review section only. The proof,
target statement, definitions, imports, DAG records, and change record were otherwise left
unchanged. The delivery closes one original hole, adds zero holes, and splits off zero
open statements.
