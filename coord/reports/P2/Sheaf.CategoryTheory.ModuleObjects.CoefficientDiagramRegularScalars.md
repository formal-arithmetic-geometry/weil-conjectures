## What changed

Completed the three theorem proofs in
`Sheaf.CategoryTheory.ModuleObjects.CoefficientDiagramRegularScalars`.
The existing declarations and both scalar-extension abbreviations retain their
statements and definitions. The private, proved helper `map_leftScalar` implements
the strong-monoidal scalar-transport calculation in proof step 2.

The monoid-morphism proof composes `mapMonCompIso` with `mapMonNatTrans`, retaining
the sequentially transported structure. The main proof constructs the comparison
from the existing mixed-bimodule right unitor, with the actual balancing
projection and inverse formula. Scalar intertwining follows by projection
hom-ext, naturality and regular-module linearity. All six planned steps remain.

Removed the unused ring-presheaf and free-monoidal-coherence imports and updated
the node's proof to match the Lean argument. The import API change is documented
in `coord/changes/coefficient-diagram-regular-scalars-imports.md`; downstream search
found zero importing modules. No source-library files are changed.

## Proved and sorry left

Closed 3 of the original 3 holes, all attached to
`lem-sfb-coefficient-diagram-regular-scalars`:

- `CategoryTheory.regularScalar_eq_leftMultiplication`.
- `CategoryTheory.coefficientDiagram_isMonHom`.
- `CategoryTheory.coefficientDiagram_regularScalars`.

Holes added: 0. Holes left: 0. Split off: 0.

Validation: the delivered Lean file compiles cleanly through `lcompile.py` in
2.1 seconds, exit code 0, with no warnings. The delivery command supplies the
independent axiom probe and preflight.

## No longer needed

Removed direct imports:

- `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`: the argument uses
  abstract monoid objects, not the construction of ring presheaves or sheaves.
- `Mathlib.CategoryTheory.Monoidal.Free.Coherence`: linearity is supplied by the
  existing proved `Mod.regularLift`, so no fresh coherence proof is necessary.

Removed the direct proof dependency
`lem-coef-monoidal-structural-coherence` from the node and its first proof step.
This only avoids a separate coherence calculation; it does not withdraw that
Mathlib leaf or any module used by other proofs. No Lean module is withdrawn.
The other ten planned proof dependencies remain used, and the unit route stays
unchanged. The existing node and its parent references are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. All three theorem signature
texts and both abbreviation declarations were compared with the repository copy
and are unchanged. The planned associativity
calculation to establish scalar linearity can be delegated to the already-proved
`Mod.regularLift`. The composite transport and sequential transport structures
are isomorphic but not definitionally equal: the proof explicitly uses
`mapMonCompIso` and supplies the sequential structure where needed, rather than
silently interchanging them. The mixed-unitor underlying maps have exactly the
required balancing source because only the regular module's left action enters
that coequalizer and its left S-action.

The older `Sheaf.Paper.RegularExtensionComparison` was also inspected. Its
isomorphism is constructed using the extension-restriction adjunction and its
naturality statement alone does not record the required balancing projection or
inverse formula. The mixed-unitor route supplies both formulas directly, so it
does not need that additional module or its node
`lem-weil-pbc-regular-extension-comparison`.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
