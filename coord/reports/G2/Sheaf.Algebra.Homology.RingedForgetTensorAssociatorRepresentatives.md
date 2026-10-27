## What changed

Replaced the original hole in `Sheaf.Algebra.Homology.RingedForgetTensorAssociatorRepresentatives` with the representative associativity calculation, preserving the public theorem's entire signature and docstring. The proof combines four representative squares, both model associator equations, tensor-model naturality, and localization-factorization naturality, then cancels isomorphisms.

Added four proved helper modules: `RingedForgetTensorChainAssociativity` lifts associativity through a comparison specified on coproduct summands; `RingedForgetTensorModelAssociativity` packages its application to two supplied associator models in abstract monoidal categories; `RingedTensorAssociatorDetection` identifies the model associator using local pure triples and the sheafification adjunction; `RingedForgetTensorAssociatorModelSquare` combines the two identifications with the abstract chain calculation. Their separation follows profiling and replacement of repeated tensor-instance construction by direct graded tensor hypotheses, to meet the per-file compile limit. None of these helpers adds a hole.

The chain calculation adapts the existing `mapCochainComplexμIso_associativity` proof. Tensor functoriality identifies the two-step map of the uncurried total tensor with the native tensor map. Inverting the supplied summand equation then permits testing on target coproduct summands, so no preservation of coproducts by U is assumed. The sheafification argument cancels a sheafified local equivalence; it makes no claim that global pure tensors generate sheaves.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_associator_representatives` (node `lem-sf-ringed-forget-tensor-associator-representatives`).

The new declarations `CategoryTheory.RingedForgetTensorTransposition.tensorComparison_chain_associativity`, `CategoryTheory.RingedForgetTensorTransposition.coefficientAssociator_eq_native`, `CategoryTheory.RingedForgetTensorTransposition.tensorComparison_model_chain_associativity`, and `CategoryTheory.RingedForgetTensorTransposition.ringed_associator_model_square` are proved. Holes added: zero. No `sorry` remains in any delivered module; every private helper is proved. This is a proof, not a decomposition into new obligations.

## No longer needed

None. All original proof dependencies remain used, directly or through the four proved helper modules. No existing public import, declaration, module, or unit step was removed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original instance assumptions stay in the public statement; the unused-section-variable linter is disabled for that last declaration to retain its interface. The adopted source library contains the relevant chain associativity calculation, but its packaged theorem additionally assumes coproduct preservation. The supplied natural comparison and summand equation suffice for its adapted calculation. Local pure triples require the sheafification argument rather than a global generation assertion.

## New nodes

`lem-sf-ringed-forget-chain-associativity`: a proved generic lifting of tensor-comparison associativity to cochain complexes, in `Sheaf.Algebra.Homology.RingedForgetTensorChainAssociativity`. It is a strict chain-level part of the argument, with no derived localization or representative-model assertion.

`lem-sf-ringed-tensor-associator-detection`: a proved identification of the total-complex associator from its local pure-triple formula, in `Sheaf.Algebra.Homology.RingedTensorAssociatorDetection`. It contains the sheafification detection argument and uses the already recorded native associator formula. No change records are needed: all existing signatures and public imports are preserved, and no other existing module is edited.

`lem-sf-ringed-forget-model-chain-associativity`: a proved application of the generic chain calculation to supplied model associators in abstract monoidal categories in `Sheaf.Algebra.Homology.RingedForgetTensorModelAssociativity`. This proves the conversion between uncurried total tensors and native complex tensors with abstract categories, so specialization avoids unfolding the large concrete sheaf tensor constructions; it has no derived localization, flatness, or representative normalization assertion.

`lem-sf-ringed-forget-associator-model-square`: the proved chain square from the two local pure-triple formulas, in `Sheaf.Algebra.Homology.RingedForgetTensorAssociatorModelSquare`. Its statement contains the coefficient tensor models and their generator formulas, so the derived proof avoids exposing native complex tensor data. The helper has no derived comparison or representative normalization square.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
