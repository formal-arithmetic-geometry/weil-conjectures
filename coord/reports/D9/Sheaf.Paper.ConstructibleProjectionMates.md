## What changed

Proved `WeilConjectures.CompactSupportFiniteProjection.domains` in
`Sheaf.Paper.ConstructibleProjectionMates`. All existing signatures, definitions,
public imports, and docstrings are unchanged. Added proof imports for intrinsic Tor
transport, finite-ring constructible origin, the etale constructibility comparison,
etale tensor preservation, pro-etale pullback preservation, Tor reflection, and the
exact derived tensor comparison. Three proved private helpers handle isomorphism
transport, the two etale bounded-constructibility presentations, and etale origins
in fixed-scalar coordinates. Updated the definition node's proof to record this route.

The tensor clause uses the existing etale theorem with only the second input of
finite Tor amplitude. The pullback clause retains constructibility from the operation
datum and proves preservation of the same Tor interval through the exact fixed-scalar
pullback; it therefore needs no geometric restrictions on the morphism. Bounds use
`min` so zero objects and initially unordered cohomological bounds are included.
The finite-ring comparison also includes empty schemes and zero coefficient rings.

## Proved and sorry left

Closed: `WeilConjectures.CompactSupportFiniteProjection.domains`
(node `def-sf-constructible-projection-mates`), the only original hole.
Added holes: none. Remaining holes in the item: none. No split-off statements.

## No longer needed

No original imports, nodes, or modules are removed. The original node had empty
`proof` and `proof_deps`. The more specialized `PullbackTorAmplitude` and
`FiniteCoefficientTensorCtf` modules are not needed as additional proof imports:
the already proved source fixed-scalar APIs and intrinsic Tor transport apply
directly, with the full input domains required here. No unit step is bypassed;
`sk-rem-sf-pf-done.realized` has no statement or step entries for this item.

## Where the brief, the DAG or earlier work was wrong

The rework row records a historical quarantine, but the current item source is
present and its baseline compiled successfully in 22.4 seconds. It is preserved
and proved, not withdrawn. There is no open
return entry for this item. The definition node had no numbered proof steps even
though its `domains` theorem carried a proof plan in its docstring; the updated
node records that plan's implementation and actual dependencies. No statement or
definition repair was required.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
