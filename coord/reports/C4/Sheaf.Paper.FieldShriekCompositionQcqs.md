## What changed

The target theorem `WeilConjectures.sfFieldShriekCompositionIntegral_existsUnique` is now
proved by assembling the unique normalized integral component isomorphisms with
`NatIso.ofComponents`, using their naturality equation, and proving the resulting
specification and uniqueness by component extensionality. The component construction
and its naturality are split into two strictly smaller public statements in new
modules, each carrying the source argument and a DAG node. No existing public
signature or definition was changed.

## Proved and sorry left

Closed one sorry: `WeilConjectures.sfFieldShriekCompositionIntegral_existsUnique`.

Two strictly smaller proof steps remain as named sorries for follow-up workers:

- `WeilConjectures.sfFieldShriekCompositionIntegral_component`, in
  `Sheaf.Paper.FieldShriekCompositionIntegralComponent`.
- `WeilConjectures.sfFieldShriekCompositionIntegral_component_naturality`, in
  `Sheaf.Paper.FieldShriekCompositionIntegralNaturality`.

There are no sorries in definitions.

## No longer needed

None. The target's original proof dependencies remain available; the proof adds
only the two split modules needed for the component construction and its naturality.

## Where the brief, the DAG or earlier work was wrong

The original single hole bundled two independent obligations: constructing and
uniquely normalizing each input component, and proving that those components are
natural in the input. Treating the whole natural isomorphism as one componentwise
existence statement obscured the required naturality step. The delivered route
records these as separate, strictly smaller nodes and combines them with a real
`NatIso.ofComponents` construction and extensionality proof.

## New nodes

- `lem-zl-field-shriek-integral-component`
- `lem-zl-field-shriek-integral-component-naturality`

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
