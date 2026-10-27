## What changed

The assigned theorem now composes three strictly simpler public construction statements:
`finite_tate_scalar_balancing_exists`,
`finite_tate_scalar_line_normalization_of_balancing`, and
`finite_tate_scalar_source_compatibilities_of_balancing`. The main theorem is proved by
applying these statements and assembling their conjunction. The three new statements are
in separate modules and are imported privately by the assigned module. The three lower
proofs remain explicit named `sorry` theorems with their construction arguments recorded
in their docstrings and DAG nodes.

## Proved and sorry left

The original hole in
`finite_tate_scalar_source_normalization_exists` is closed by a genuine three-part
reduction. Three lower holes are added:

- `finite_tate_scalar_balancing_exists` — node
  `lem-pur-finite-tate-scalar-balancing-existence`;
- `finite_tate_scalar_line_normalization_of_balancing` — node
  `lem-pur-finite-tate-scalar-line-normalization-of-balancing`;
- `finite_tate_scalar_source_compatibilities_of_balancing` — node
  `lem-pur-finite-tate-scalar-source-compatibilities-of-balancing`.

No `sorry` occurs in a definition.

## No longer needed

The assigned proof no longer directly uses the former nine proof-dependency nodes:
`def-pur-sheaf-tensor-product`, `lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-asd-finite-etale-twist-line`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-pur-derived-change-of-rings`, `lem-pur-etale-scalar-mate-projection`,
`lem-pc-kflat-resolution`, `lem-pur-etale-compact-scalar-coherence`, and
`lem-pur-scalar-right-unit`. They are not imported by this delivery; their mathematical
content is the source of the three named lower statements.

## Where the brief, the DAG or earlier work was wrong

The original item proof plan contains a long construction that cannot be discharged from
the currently published declarations in one theorem. The DAG did not expose its three
independent construction layers as Lean statements. This delivery makes those layers
explicit while preserving the assigned theorem signature and the unit route. No target
statement or existing definition was changed.

## New nodes

`lem-pur-finite-tate-scalar-balancing-existence` states existence of the generator-pinned
ordinary balancing family.

`lem-pur-finite-tate-scalar-line-normalization-of-balancing` states the line and scalar-unit
normalization for a balancing family.

`lem-pur-finite-tate-scalar-source-compatibilities-of-balancing` states source invertibility
and the two endpoint unit equations after balancing and line normalization.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteTateScalarBalancingExistence": "5ee528e5bd62675b5229c6792b336ea5b697f694", "Sheaf.Paper.FiniteTateScalarLineNormalizationOfBalancing": "da0131744b554ec696ab4bd66c47bb9055e2b5e0", "Sheaf.Paper.FiniteTateScalarSourceCompatibilitiesOfBalancing": "f51d0f01fcda774741b78922a8177aeececbbfdd", "Sheaf.Paper.FiniteTateScalarSourceExistence": "e2cfac1dc5bd343de6e9b125e82be0eb2297a955"}, "results": {}, "time": "2026-10-28T03:27:58+0800", "transitive": 0, "version": 1}
```

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
