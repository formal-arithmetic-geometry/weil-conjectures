# Scalar completion proof and compilation split

The item is `Sheaf.Paper.CompactSupportScalarLimitReduction`, held by F5.
`scalarCompletion_existsUnique` is proved by the new completely proved
`CompletedScalarLocalizationBalancing` helper.

Full-file profiling found the aggregate elaboration and kernel checking of the
existing foundational and Roos declarations above 60 seconds. The foundational
prefix is moved to `Sheaf.Paper.CompactSupportScalarLimitFoundations`. The item
publicly imports this module. All moved declaration names, signatures and
non-theorem bodies are retained. The original public imports are retained.
The two original exactness holes in that prefix are retained as named theorems;
there are five remaining holes across the item and foundation module.

The existing definitions node
`def-pur-compact-support-scalar-limit-maps` has its Lean attachment updated to
the foundation module. The parent statement node retains its statement and
unit route, and updates its declaration list and Step 3 dependencies.

Local unfolding and elaboration settings apply only inside these modules.
They do not export changes to the reducibility of any declaration. No existing
consumer signature or proof is changed. Direct importers are compiled against
the full delivery; unchanged consumer copies are removed before submission.

Validation passed for the three delivery modules and every current direct importer:

- `Sheaf.Paper.ConstantCompletedOrdinaryAssociativity`.
- `Sheaf.Paper.CompletedScalarExactLocalization`.
- `Sheaf.Paper.ScalarLimitTensorComposition`.
- `Sheaf.Paper.ConstantCompletedScalarAssociativity`.
- `Sheaf.Paper.CompactSupportStrictScalarRefinement`.
- `Sheaf.Paper.CompactSupportScalarShiftStructures`.
- `Sheaf.Paper.CompactSupportScalarProjectionIdentification`.
- `Sheaf.Paper.CompactSupportStrictScalarComposition`.
- `Sheaf.Paper.ScalarRefinementOriginsF`.
- `Sheaf.Paper.ScalarLimitTensorRestriction`.

All ten unchanged consumer copies were removed from the sandbox.
