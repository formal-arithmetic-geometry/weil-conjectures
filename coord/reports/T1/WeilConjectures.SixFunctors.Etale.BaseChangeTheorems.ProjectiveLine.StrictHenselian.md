## What changed

Completed `AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal`
in the assigned module, with its signature unchanged. The proof composes a strict-local
stalk/total-space comparison with bijective closed-fibre restrictions over A and B.
The residue-field ring identity proves commutativity of the projective-line square.
The two resulting additive equivalences and their equations give the original conclusion.
The existing assertion for a bijective residue-field map then continues to apply unchanged.

Added proof-only imports of `Sheaf.AlgebraicGeometry.StrictLocalTotalCohomologyExchange`
and `Sheaf.AlgebraicGeometry.CohomologyRestrictionSquareTransport`.
The latter is proved using the new, proved coefficient-square compatibility module,
which uses the existing forgetting-coefficients and cohomology-functoriality declarations.
A private categorical cancellation lemma avoids expensive inference on scheme sheaves.
All original proofs, public imports, definitions, and declaration signatures are preserved.
Updated the strict-local exchange node and supplied three new nodes matching the Lean.

## Proved and sorry left

The assigned module's one original sorry is eliminated:
`AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal`
(node `prop-weil-pbc-strict-local-exchange`). This is a reduction, not a claim that its
transitive axiom dependencies are closed.

Also proved:
- `AlgebraicGeometry.Etale.exists_addEquiv_cohomology_moduleSquare`
  (`lem-weil-pbc-cohomology-module-square-compatibility`).
- `AlgebraicGeometry.Etale.exists_addEquiv_cohomology_restrictionSquare`
  (`lem-weil-pbc-cohomology-restriction-square-transport`).

The only sorry in the delivered files is
`AlgebraicGeometry.Etale.exists_addEquiv_strictLocal_totalCohomology_exchange`
(`lem-weil-pbc-strict-local-total-cohomology-exchange`), in its own new module.
Its hypotheses allow any cartesian square over the two strict local bases; its conclusion
concerns total-space cohomology, without assuming torsion or a closed-fibre comparison.
Its docstring gives the injective-resolution argument and the map compatibility.
The proved combination with the separately established projective-line restrictions is
the nontrivial remaining part implemented in the assigned module.

## No longer needed

None of the original imports is removed. The old direct proof dependency
`def-weil-pbc-derived-exchange` is no longer directly used by the completed proof;
it remains a statement dependency and a transitive dependency through
`lem-weil-pbc-strict-local-total-cohomology-exchange`. Its module is retained.
No node or module becomes unreachable: the strict-local exchange still uses the
strictly henselian projective-line comparison.
The new coefficient-square helper does not require a separate compatibility-of-units
lemma for the chosen module/abelian isomorphisms: its third isomorphism is constructed
from the first two and inverse-image composition. No such additional node is introduced.
The unit `sk-thm-p1` and all its realized steps are retained.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had not copied or reduced the assigned module and had no
report. Its coefficient-square proof also failed to compile at the final composition.
This attempt completes that composition with explicit cohomology-map arguments and
categorical isomorphism cancellation, then uses the helpers in the assigned module.
The earlier coefficient-square proof plan unnecessarily required coherent choices of
coefficient isomorphisms. The implemented existential statement needs only the existing
objectwise forgetting isomorphisms; its third equivalence absorbs these choices.

The original strict-local node compressed the derived/Ext comparison and both
closed-fibre comparisons into one step. The new total-space lemma isolates precisely
the former. Existing `DerivedExchangeTermwise` is expressed for abelian derived objects;
`StrictlyHenselianSectionsStalk` uses algebraically closed geometric fields and abelian
sheaves, and `InjectiveModuleAbelianAcyclic` uses `SheafOfModules` and right-derived
evaluation. None directly supplies the module-valued `DerivedCategory.Plus` homology /
`Sheaf.H` comparison needed here. They remain explicit proof dependencies of the new node.
The existing docstring already notes that the existential statement does not expose
canonical comparison maps; this delivery preserves that statement and does not claim
to repair that stronger specification.

Sources read: the locally available Stacks `etale-cohomology.tex`,
`lemma-vanishing-etale-cohomology-strictly-henselian` (03QO), and
`theorem-proper-base-change` (095T), especially the final map-on-stalks paragraph.
Searches in the existing sandbox log were checked; additional LeanFinder and Loogle
searches and repository/Mathlib text searches found no ready-made total-space comparison.
Edge cases of the new total-space statement include q=0, identity maps, empty total
spaces, and zero coefficient ring: the same section/resolution calculation applies.
The coefficient and restriction helpers also include those cases and arbitrary commuting
squares; bijectivity is used only in the restriction helper.

## New nodes

`lem-weil-pbc-strict-local-total-cohomology-exchange`:
`lean/Sheaf/AlgebraicGeometry/StrictLocalTotalCohomologyExchange.lean` states the remaining
stalk/total-cohomology bridge, independently of closed fibres and properness.

`lem-weil-pbc-cohomology-module-square-compatibility`:
`lean/Sheaf/AlgebraicGeometry/CohomologyModuleSquareCompatibility.lean` proves the
coefficient-forgetting and composition transport for an arbitrary commuting square.

`lem-weil-pbc-cohomology-restriction-square-transport`:
`lean/Sheaf/AlgebraicGeometry/CohomologyRestrictionSquareTransport.lean` proves the
transport through the two assumed bijective restrictions by composing additive equivalences.
No statement or definition change record is needed.


## Second reading by T1

1. Compared the delivered StrictHenselian module against the repository with `diff`.
   Only two plain proof imports and the original sorry body change. Every existing
   declaration signature, definition, docstring and pre-existing proof is unchanged.
   The three other delivered modules are new. Verdict: interface preserved; no
   statement-change record is required.
2. Compiled all four modules in import order through `lcompile.py`: no errors or
   warnings. Scanned every delivered Lean file for forbidden declarations and sorry.
   The only direct sorry is the reported public total-space comparison theorem;
   there are no hollow definitions. Scratch `#print axioms` checks on all four
   public new/changed theorems and the downstream isomorphism assertion show only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from open dependencies.
   Verdict: kernel-checked reductions, with the reported remaining proof obligation.
3. Read all new statements, their docstrings and their nodes. Checked identity base
   maps, q=0, zero coefficient modules/ring, and empty total spaces mathematically.
   The cartesian total-space comparison uses exact sections on each strict local
   base and module/abelian cohomology comparison; it makes no proper base-change
   isomorphism claim. Read Stacks Tags 03QO, 03FD and 095T on the official website
   because the recorded literature files are absent from this clone. Independently
   searched repository declarations and ran LeanFinder, Loogle and Mathlib grep
   searches with different terms. Existing sections/stalk, termwise exchange and
   module acyclicity results do not supply this derived-homology/Ext interface.
   The other two helpers implement coefficient-square cancellation and composition
   of bijective restrictions. Verdict: true statements; the sole open statement
   is a genuine part of the argument, not a renaming of closed-fibre exchange.
4. Read the whole assigned module, its old dependency plan and the unit's `realized`
   route. The proof uses the existing comparison over A and over B and retains
   every realized step of `sk-thm-p1`. No ready-made shorter bridge was found;
   proving the open derived/Ext comparison requires more than a short tactic repair.
   Each new proof import is used, and public imports of the new modules provide
   notions appearing in their signatures. Verdict: route kept and reduction valid.
5. Compared the old and delivered node metadata, checked new-node required fields,
   declaration names and recorded Lean signatures, and checked each proof step's
   `uses` against `proof_deps`. Only permitted proof fields of the existing node
   change; all three new nodes agree with the Lean. Verdict: metadata consistent.

Second reading changed only the pruning report: it now explicitly lists the old
`def-weil-pbc-derived-exchange` direct dependency and explains why it remains
transitively needed. No Lean repair was necessary.
