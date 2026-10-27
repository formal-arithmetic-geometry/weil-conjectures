## What changed

Proved `AlgebraicGeometry.Scheme.IdealSheafData.normalizedBlowup_calculus` with its
entire original signature. The proof combines the already stated normalized-blowup
finality theorem, componentwise normalization smooth pullback, integral-normal generic
recognition, and the proved ordinary-blowup and finite-type normalization APIs.
Private helpers prove the remaining geometric and categorical glue, including the
normalization comparison, the unit ideal, and identity/composition compatibility.
The calculus imports and uses the existing normalization lemmas instead of copying them.
No source-library file changes.

Expose the already proved `AlgebraicGeometry.finite_normalization`,
`normal_normalization`, `component_meets_dense_open`, and
`dense_preimage_normalization` in their owning, unclaimed module
`Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange`. Their binders,
conclusions and proof bodies are unchanged. Remove the four duplicate private
calculus declarations named in the return and qualify all shared uses. Record this
interface repair in `coord/changes/componentwise-normalization-helper-visibility.md`
and list the four helpers in the existing normalization node
`lem-weil-pbc-reduced-algebraic-normalization-field-change`.

Moved `normalizedBlowup` and `normalizedBlowupMap`, with identical signatures and
concrete bodies, to `Sheaf.AlgebraicGeometry.NormalizedBlowup`. The calculus publicly
re-exports them. Adapted the unclaimed finality module's statement imports so that it
can be imported by the calculus without a cycle. Updated the existing definition node's
Lean attachment and the calculus node's proof route. The change record is
`coord/changes/normalized-blowup-definition-module.md`.

Validation: the final five-module packet compiled cleanly together with lcompile.py.
The calculus took 18.3 seconds, the shared normalization module 16.0 seconds, and
the adapted ConductorSmoothBaseChange consumer 22.8 seconds. Its unchanged source
failed with the documented declaration conflict; the precise adaptation compiles.
The construction equations and existing theorem signature are unchanged. The proof
permits the empty scheme throughout and adds no nonemptiness hypothesis. Existing
stated dependencies still carry sorryAx; this delivery adds no axiom or new hole.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.IdealSheafData.normalizedBlowup_calculus`
(`lem-trf-normalized-blowup-calculus`). Zero holes remain in the item and zero holes
were added or split off. This is a proof from existing stated dependencies, not a claim
that those dependencies are already axiom-free.

The only textual `sorry` in the delivery is the unchanged existing theorem
`AlgebraicGeometry.Scheme.IdealSheafData.normalizedBlowup_finality`
(`lem-trf-normalized-blowup-finality`), whose module needed its import adapted.
The proof also uses existing holed normalization statements; it does not change them.

## No longer needed

Removed imports:

- `public import Sheaf.AlgebraicGeometry.ReducedNormalization`
- `public import WeilConjectures.Blowup.Gluing`
- `import WeilConjectures.Blowup.Principalization`
- `import WeilConjectures.Blowup.BlowupUniversal`
- `import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDominantLift`
- `import Sheaf.AlgebraicGeometry.RegularNormalDecomposition`
- `import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`

The first two construction imports remain available publicly through the new definition
module; their mathematics is retained. The proof no longer uses the private
`NormalizationDominantLift`, `RegularNormalDecomposition`, or `SmoothFiber` imports.
Regularity is handled by the proved source `IsRegular.isIntegrallyClosed_stalk` API;
flatness and openness are existing instances. The finality statement supplies
principalization and arbitrary-normal-source lifting, so the calculus does not
separately reprove or import their detailed implementations.

Declared dependencies omitted from this proof route:

- `lem-sfb-componentwise-normalization-generic-properties`
- `lem-trf-blowup-over-normalization-comparison`
- `lem-trf-reduced-blowup-generic-geometry`
- `lem-trf-smooth-reduced-dense-pullback`
- `sbc-lem-smooth-criterion`

The reduced-blowup and smooth-dense-pullback steps are proved here as private helpers
from concrete charts and existing Mathlib/source APIs. The separate blowup-over-
normalization comparison is proved from finality on S and its normalization, using
two inverse maps. Generic normalization properties use the existing shared
normalization lemmas, its finite normal locus, and generic-point topology. Thus no import is added
for those unattached planned modules. Removed obsolete tool approvals for
`lem-sfb-componentwise-normalization-generic-properties` and `sbc-lem-smooth-criterion`.
The four duplicated calculus helpers are removed; their original proved versions
remain in ReducedAlgebraicNormalizationFieldChange and are now public. The
duplicate private `normal_normalization` in ConductorSmoothBaseChange is also removed in favor of the shared theorem. No existing source-library declaration or
module is withdrawn. The unit's realized route is
unchanged (this auxiliary node realizes none of its statement or steps).

## Where the brief, the DAG or earlier work was wrong

Several listed proof dependencies currently have no Lean attachment: the reduced
blowup geometry, blowup-over-normalization comparison, smooth reduced/dense pullback,
and componentwise normalization generic properties. The existing ordinary-blowup and
normalization APIs suffice to prove the needed parts, so this does not block the item.
The finality module originally imported the calculus for its definitions; importing it
back would have created a cycle. The new definition-only module repairs that interface
without changing either construction. Its existing definition node is reused, and no
new node or unfinished lemma is introduced.

The returned packet copied four private theorems from
`ReducedAlgebraicNormalizationFieldChange`. The requested import-and-use repair also
requires exposing those existing private declarations; a plain import alone cannot
resolve them. This packet changes their visibility in place and removes every copy.
The old theorem signature of the calculus and the four shared helper types are
preserved exactly.

## Forced adaptations

`Sheaf.TraceFormula.ConductorSmoothBaseChange` was unclaimed. Compiling its original
source against the repaired normalization module failed at its old line 138:

```text
error: a non-private declaration `AlgebraicGeometry.normal_normalization`
has already been declared
```

The new public shared helper conflicts with that module's private declaration of
the same name. Delete only the private duplicate (old lines 138--152) and qualify
the two existing uses in `normal_of_iso_open` as
`AlgebraicGeometry.normal_normalization`. No existing public signature, visibility,
import or definition changes. Its unchanged source was compiled as
`ConductorConsumer__probe.lean` to establish this failure; the adapted actual module
is included in the final packet and compiled cleanly in 22.8 seconds.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
