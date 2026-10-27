# Integral compact-support tensor module extraction

Group R4; item Sheaf.Paper.IntegralCompactSupportCoefficientComparison; 2026-10-28.

## Reason

The unchanged item exceeded the 60-second single-file limit (71.5 seconds).
Profiling identified native tensor representative checks, the pure-section identity,
and especially the scalarTensor definition and its extracted proof as costly.
Local irreducibility seals for the flat representative predicate and tensor
constructions were tried; full-module checks still took 63.6 and 71.7 seconds.
The worker brief expressly allows a self-contained split after improving slow
unfolding. Extract the tensor construction so both files can be checked separately.

## Interface and definitions

Added Sheaf.Paper.IntegralCompactSupportScalarTensor. It holds coefficientSiteSmall,
coefficientRingSheafify, coefficientAbSheafify, coefficientAbLocallyBijective,
tensorModel_exists, scalarOrdinaryTensor_existsUnique, scalarOrdinaryTensor,
scalarOrdinaryTensor_naturality, scalarTensorTotal, scalarTensorTotal_isIso,
scalarTensor_existsUnique and scalarTensor, in their original namespace.
The item publicly imports it. All existing public names and signatures are kept,
and definition bodies are unchanged. The ordinary existence/uniqueness theorem is
now proved. The pre-existing derived existence/uniqueness hole is relocated verbatim;
no new hole or axiom is introduced. The scalar section module instance and all new
auxiliary proofs are private and local where applicable.

The tensor definition owner is split into a new node, while its original combined
mathematical statement remains unchanged. Its recordedSupport and
recordedIdentification declarations stay attached to the old node. The main item
node no longer claims ownership of the moved declarations. The open-isomorphism
node records the actual localization/composite-adjunction argument.

## Consumers and validation

The public import retains visibility of the moved declarations for every importer.
There is no consumer signature adaptation. Remote compilation and the delivery
related-module checker validate the new dependency and affected importers. No
WeilConjectures source-library file is changed. No target or mathematical definition
changes meaning. Compile timings and any importer checks are recorded in report.md.

Tensor-only proof imports removed from the item: ScalarHomOrdinaryTensorComparison,
AdicCoefficientDatum and RingedDerivedTensorNative. They now occur in the tensor
module, whose statements and definition bodies require the existing data import and
canonical tensor-pullback import. Import-order compilation passed at 40.3 and 50.0
seconds before removing these redundant main-module proof imports.
