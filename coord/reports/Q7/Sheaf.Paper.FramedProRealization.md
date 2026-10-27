## What changed

Proved `WeilConjectures.PurityFiniteSetting.divisorProRealization_existsUnique`
in `Sheaf.Paper.FramedProRealization`. Three proved private helpers compare any
normalized supported-Hom identifications, first on supported cocycles in a
bounded-below injective complex, then on every bounded-below derived object by
naturality, and finally on the pro-etale supported constant presentation.
The existence proof inverts one normalized additive equivalence on the canonical
site-comparison Hom class. Equality of the identifications proves its universal
normalization; injectivity proves uniqueness. The definition and both existing
public signatures remain unchanged. The item's DAG proof now records this route.

Validation: `lcompile.py` compiled the delivered Lean module successfully in
27.0 seconds, with no errors or warnings. No public imports, statements,
definitions, instances or attributes were changed.

## Proved and sorry left

Closed one hole: `WeilConjectures.PurityFiniteSetting.divisorProRealization_existsUnique`
(node `def-pur-framed-pro-realization`). No holes added or split off; zero textual
`sorry` remain in the delivered module. This is a proof from existing declarations,
including `AlgebraicGeometry.supportedHom_cocycle_normalization`, whose existing
hole is outside the delivery. `supportedHom_pullback` supplies the nonempty family
of normalized equivalences. No claim is made that their full dependency closure
is axiom-free yet.

## No longer needed

Removed the private proof import `Sheaf.Paper.SupportedRootScalarSiteComparison`.
Its node `lem-pur-supported-root-scalar-site-comparison` is unnecessary for this
existence/uniqueness theorem: the predicate already specifies the canonical Hom
class, and every such Hom class has a unique supported preimage. The stronger
root-coefficient comparison is therefore not reproved or assumed here. This does
not assert that other consumers of that module no longer need it. No module or
node is withdrawn; no unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item's node had empty `proof` and `proof_deps`. The previous unused private
import suggested a stronger root-scalar comparison theorem, which additionally
requires finite-type, quasi-compactness and separatedness hypotheses absent from
this theorem. Those hypotheses are unnecessary: normalization of supported Hom
alone gives the unique preimage of the already-defined canonical comparison map.
The three helpers prove the missing equality of all normalized identifications
without changing their interfaces. No mathematical statement was disputed or
changed. The rework row's historical missing-import quarantine is not a withdrawal:
the current source exists and is retained with both public declarations.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
