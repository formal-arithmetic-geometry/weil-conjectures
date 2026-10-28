## What changed

The target module now proves `localChern_transport_identification` by composing two
finite-level statements: the transport arrow satisfies the finite Chern
specification, and finite specification uniqueness identifies its comparison image.
The finite-level definitions and split statements are kept in this item module so
its delivery compiles as one unit. `localChern` then follows by transitivity with
the existing transport existence statement. The source module's
`set_option Elab.async false` is retained because it keeps the proof within the
single-file compile gate.

## Proved and sorry left

Closed `localChern_transport_identification` and `localChern` (2 of the 3
original theorem sorries). The existing `localChern_transport_exists` sorry
remains. Added the strictly simpler split statements
`localChern_transport_finite_spec` and
`localChern_transport_finite_spec_unique_map` (2 split-off sorries).

## No longer needed

The temporary support modules `Sheaf.Paper.DiagonalUniformizerLocalChernAliases`,
`Sheaf.Paper.DiagonalUniformizerLocalChernFiniteSpec`,
`Sheaf.Paper.DiagonalUniformizerLocalChernSpec`, and
`Sheaf.Paper.DiagonalUniformizerLocalChernSpecUnique` are not delivered. Their
finite definitions and declarations are present directly in the item module;
this avoids a multi-file compile race and leaves no unused imports or nodes.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery split the finite definitions and lemmas into four support
modules. The delivery compiler batches new modules concurrently, and repeatedly
exceeded its 120-second batch limit even though the target compiled alone. The
finite statements are genuine lower-level reductions, so consolidating them in the
item module preserves the proof decomposition while making the delivery reviewable.

## New nodes

`lem-diagonal-uniformizer-local-chern-finite-spec` and
`lem-diagonal-uniformizer-local-chern-finite-spec-unique-map` remain split-off
nodes. The definition nodes `def-diagonal-uniformizer-local-chern-finite-comparison`,
`def-diagonal-uniformizer-local-chern-finite-spec`,
`def-diagonal-uniformizer-local-chern-local-composite`, and
`def-diagonal-uniformizer-local-chern-local-finite-arrow` point to declarations in
`Sheaf.Paper.DiagonalUniformizerLocalChern`.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalUniformizerLocalChern": "61f4e178e2e7bf7b33e8856a7c661d25967a2c9a"}, "own_failed": ["Sheaf.Paper.DiagonalUniformizerLocalChern"], "results": {}, "time": "2026-10-28T10:08:06+0800", "transitive": 0, "version": 1}
```

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
