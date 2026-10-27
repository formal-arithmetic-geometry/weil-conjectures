## What changed

Filled the five theorem proofs in Sheaf.Paper.VerdierCompositionMateNormalization,
preserving every declaration signature and every definition. The composition mate
is computed by Mathlib's conjugation component formula and the supplied lifted
unit/counit equations. Substitution is two applications of adjunction naturality;
its Weil equation is the algebra-morphism equation of the lifted map. The main
normalization cancels the three inverse transposes, the fixed projection, and the
counit, then cancels I.hom to identify preExchange with I.inv. The stage epsilon
formula uses the same naturality calculation and StageConclusion.components.

Removed the unused private imports Sheaf.Paper.TensorAdjunctionExchange and
Sheaf.Paper.AdmissibleVerdierExchange. Updated the node's proof, proof_deps and
proof_origin to describe these proofs, and removed its obsolete top-level
fix-lem-tensor-adjunction tool-use entry. No statements, definitions, public
imports, source-library files or consumers change.

## Proved and sorry left

Closed all five existing holes, by declaration name:

- WeilConjectures.VerdierCompositionMate.composition_mate
- WeilConjectures.VerdierCompositionMate.substitution
- WeilConjectures.VerdierCompositionMate.substitution_weil
- WeilConjectures.VerdierCompositionMate.verdier_composition_mate_normalization
- WeilConjectures.VerdierCompositionMate.stage_epsilon

All are attached to lem-pod-verdier-composition-mate-normalization. Zero holes
remain in the item; zero holes and zero split statements were added elsewhere.
This is a proof, not a decomposition. The delivery compile and declaration axiom
probe verify the resulting module.

## No longer needed

Removed proof imports:

- Sheaf.Paper.TensorAdjunctionExchange (fix-lem-tensor-adjunction): the conditional
  normalization hypothesis already supplies I and its exact Hom-chain equation.
  The proof does not construct I or use tensor_adjunction. The Model and
  inverseComponent definitions used by stageTensorModel/stage_epsilon are already
  supplied by the retained public Sheaf.SixFunctors.TensorHomTranspositionData.
- Sheaf.Paper.AdmissibleVerdierExchange (fix-cor-verdier-exchange): neither the
  supplied-domain identities nor the conditional normalization requires its
  existence theorem or package.

The node's proof no longer uses def-weil-finite-tor-amplitude: every test object is
already in the supplied category and the normalized I hypothesis quantifies over
that category. Its statement dependency stays. The theorem nodes above also stay
as statement dependencies where already present; this delivery claims no global
withdrawal of their modules. Removed only the obsolete top-level tool-use approval
for fix-lem-tensor-adjunction. The unit record sk-lem-finite has no realized route
through this auxiliary node, and its statement and steps remain untouched.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The earlier plan invoked the
internal-adjunction existence theorem and field finite-Tor identification for a
conclusion that the Lean statement makes conditional on a supplied normalized
isomorphism. Those invocations are unnecessary for this statement. The Hom-chain
cancellation proves the conditional conclusion directly, including zero objects
and identity functors. The stage epsilon clause uses the right-tensor convention
of CoefficientClosedStructure exactly as recorded.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
