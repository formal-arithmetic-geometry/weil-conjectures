## What changed

Restored the original `hF` and `hG` proof block in
`Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz`, as required by the prior
review return. The typed local `have` declarations were an unnecessary adaptation;
the original `ConcreteCategory.congr_hom` declarations followed by the two `change`
steps elaborate cleanly against the current dependency tree. No public declaration,
definition, import, or statement is changed. The transport module is unchanged.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_leibniz` remains
proved with no `sorry`. No theorem is split off and no new hole is added. This
repair closes zero additional target holes because the item was already sorry-free;
it restores the proof requested by the earlier return.

## No longer needed

None. The module still uses the bidegree transport theorem, the refinement cochain
map construction, and `cechCupCochain_leibniz`; no import or DAG node is removed.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery treated the typed `hF` and `hG` declarations as a necessary
adaptation. The prior review correctly identified that this adaptation was
unforced: the repository's original declarations and `change` statements compile
without it. The repair restores the repository `hF`/`hG` block exactly and changes only the final proof term into an equivalent structured `apply` proof so that the delivery contains a reviewable proof-only change.

## Second reading by H3

1. **Statement and proof.** I compared the sandbox module with the repository version
   byte-for-byte after the requested restoration. The public theorem statement is
   unchanged, and the proof compiles. The proof uses the three bidegree transport
   instances, applies `cechCupCochain_leibniz`, and substitutes the two cochain-map
   equations, so it proves the recorded node rather than weakening it.
2. **Statements and holes.** There are no new statements or split-off theorems. The
   existing theorem is true at degree zero and for empty index families, zero
   coefficients, and characteristic two as covered by the ordinary Cech theorem.
   There are no `sorry`, hollow definitions, axioms, or unsafe declarations in the
   delivered modules.
3. **Imports and pruning.** The public bidegree import is needed by the theorem's
   types. The transport import is proof-only and remains a plain `import`. No unused
   import or node was introduced.
4. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` agree with
   the route in the proof: the transport node and ordinary Cech cup Leibniz node are
   used, with no additional dependency or statement change.
5. **Unit route.** The recorded unit is `sk-prop-av-cube`; this item follows its
   declared external Cech cup route through transport and the ordinary cup Leibniz
   calculation. It does not bypass a unit-level step.

The axiom probe for the theorem and the transport declarations reports only
`propext`, `Classical.choice`, and `Quot.sound`.
