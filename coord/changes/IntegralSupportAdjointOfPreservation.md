# Change record

Repair of the returned delivery. The previous proof imported
`Sheaf.Paper.ExceptionalRingOperationsExistence`, which imports the parent
`Sheaf.Paper.ExceptionalIntegralSupportAdjoint` and creates a cycle back to this item.

The proof now imports only the new acyclic `Sheaf.Paper.IntegralSupportOperationRealization`
module. That module declares the strictly simpler integral-stage operation and compact-support
realization statement, which is the only remaining sorry in this delivery. The target proof
transports its operation adjunction through the realization and preserves the target signature.
