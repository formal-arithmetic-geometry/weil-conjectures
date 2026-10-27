## What changed

Proved `AlgebraicGeometry.lciConormalFibreFieldChange` without changing its statement,
public definitions, instances, or public imports. Added private proof imports for
localization base change, the polynomial tensor equivalence, the Hilbert basis
theorem, and dimension under scalar extension. Added
`import all WeilConjectures.RingTheory.StrictHenselizationCotangentDimension`
to use its existing private flat conormal base-change theorem.

The proof transports Mathlib's flat conormal base-change map from the tensor ring
back to the polynomial ring, cancels the module localizations after tensoring with
the residue fields, and composes the resulting linear equivalences. Its formula
on each relation class is checked component by component. Noetherianity supplies
finite generation, and `Module.finrank_baseChange` proves the dimension equality.
Repair of returned head `854c5e90cb9`: removed both duplicate private theorems
`AlgebraicGeometry.lci_cotangent_bijective_equiv` and
`AlgebraicGeometry.lci_flat_cotangent_bijective`. The proof now applies the
existing `Algebra.flat_cotangent_bijective` directly, using `import all` to access
the private declaration. Its existing helper `Algebra.cotangent_bijective_equiv`
is reused transitively. That source module is unchanged. The item node's proof
and dependency records now match this implementation.

Validation: the complete proof compiled through `lcompile.py`; the packet is also
checked by `deliver3.py`. The construction handles zero variables and zero fibres:
none of its tensor equivalences or dimension results requires positive dimension.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.lciConormalFibreFieldChange`
(node `lem-trf-lci-conormal-fibre-field-change`).

Proved 1 of 1 original sorries. Zero sorries remain, zero were added, and no
statements were split off. Every added private helper is proved.

## No longer needed

No original public imports were removed. During proof development the redundant
private imports `Mathlib.RingTheory.Flat.Stability` and
`Mathlib.RingTheory.TensorProduct.Finite` were removed.

The revised proof no longer uses these planned proof dependencies:

- `lem-weil-pbc-presentation-base-change`: the polynomial tensor equivalence is
  already in Mathlib. Working directly over the polynomial rings avoids quotient
  presentations entirely; surjectivity of the presentation is not needed for this
  stronger argument, while the original hypothesis is preserved.
- `lem-weil-pbc-field-extension-base-change-faithfully-flat` and
  `def-weil-pbc-faithfully-flat-ring-map`: freeness of a vector space and its scalar
  extension supply the flatness needed by the conormal map directly.
- `lem-weil-pbc-polynomial-ring-field-regular-ring`: only Noetherianity is needed,
  supplied directly by the Hilbert basis theorem. Regularity is unused.

These are proof-route dependency removals; no modules or declarations are
withdrawn. Statement dependencies and the unit route are preserved. The existing
WeilConjectures cotangent module is now a private proof import;
no Sheaf proof-dependency module is imported. The flat conormal dependency is
implemented by its existing proved helper, and the remaining ingredients are
Mathlib declarations. The two duplicated private cotangent lemmas have been
removed, rather than renamed or restated. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery duplicated two proved private source-library lemmas.
The return correctly required reuse: `import all` makes the existing private
flat conormal lemma available without changing the source-library interface.
Both duplicate declarations are removed in this repair.

No false statement or definition was found. The original plan unnecessarily
passes through the quotient algebra and faithful flatness. Mathlib's conormal
base-change theorem has a tensor-ring target; transporting it along tensor
multiplication supplies the stated general ring-map version. Explicitly
registering the modules associated to the chosen algebra structures is necessary
because the residue-field module instances can otherwise select a different
scalar action. No interface repairs or consumer adaptations were required.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
