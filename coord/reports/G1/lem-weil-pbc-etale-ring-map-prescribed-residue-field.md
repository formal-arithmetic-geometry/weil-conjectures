# Delivery report: `lem-weil-pbc-etale-ring-map-prescribed-residue-field`

## Worker report

I split the Tag 00UD construction into the public primitive-element Mathlib leaf, the statement-only denominator-clearing lift, the existing reviewed standard-etale leaf, and an explicit kernel/residue-field step. The map $R[T,1/f']/(f)\to L$ has prime kernel; reducing modulo $\mathfrak p$ identifies its quotient with $L$, which supplies the required prime contraction and residue-field isomorphism.

No Lean files were written or compiled. Local DAG checks are recorded in the handoff; the commit remains unpushed for independent lead review and the fresh-base preflight gate.

## Review by G1

I checked the construction against Stacks Tag `00UD`: the finite separable residue extension is represented by a primitive element, the denominator is cleared to obtain a standard-etale presentation, and the kernel/residue calculation supplies the prescribed prime and residue-field isomorphism. The derivative unit in step 1 is now justified through the public separable-polynomial definition. Step 4 now cites the public fibre-ring prime correspondence and fibre-ring residue-field isomorphism nodes for the contraction of the kernel and the identification of the residue field with `L`. The parent cites the existing standard-etale affine node for Tag `00U1`; the two new helper nodes are statement-only, carry this item as `created.item`, and expose the reusable primitive-element and denominator-lifting facts publicly. The report and DAG contain no private reusable lemma or Lean changes.
