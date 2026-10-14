## What changed

Proved `AlgebraicGeometry.schemeDirectImageSquare_single_unit_normalization`
by the two steps already specified in its DAG node. Five proved private helpers
identify pushforward congruence with equality transport, prove equality naturality
of the derived unit, express it with the successive-image source, identify the
homotopy comparison on complex representatives, and simplify its underived model.
The final proof combines these identities. The original public statement,
definitions, visibility, imports, and docstring are unchanged.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.schemeDirectImageSquare_single_unit_normalization`.
One original hole closed; zero holes added; no `sorry` remains in the module.
All five private helpers are proved. No new statement modules or decompositions.
Validation: `lcompile.py` and the required `deliver3.py --no-push` dry run
(local compilation, axiom probe, and delivery checks). Nothing pushed.

## No longer needed

None. Both original imports and both original DAG proof dependencies are used.
No node or module is pruned; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The missing compiled dependency reported by the
earlier attempts is now available. The preserved proof needed correction before
it could compile: its derived-unit transport helper now retains exactly the
`congrArg schemeDerivedDirectImage` equality expression in the original statement,
rather than expanding that functor family and triggering expensive conversions.

The existing `AlgebraicGeometry.directImageSquare_unit_transport` assumes derived
categories for every scheme. This item only supplies the relevant local instances;
its elementary equality-induction argument is proved locally with those instances.
No assumptions, definitions, dependency files, or public signatures were changed.

## Second reading by T3

1. **Interface: pass.** Diffed the sole delivered module against the repository.
   The existing theorem signature is byte-for-byte identical (also checked by
   extracting the text before `:= by`); its docstring, visibility, and imports
   are unchanged. Only proved private helpers and scoped proof elaboration options
   accompany the replacement of the original `sorry`. No definitions changed.
2. **Proof: pass.** Independently compiled the delivered file with `lcompile.py`
   (38.7 seconds, no errors or warnings). Inspected every helper: equality
   induction handles pushforward congruence and the derived unit; quotient-object
   surjectivity and functoriality handle the homotopy model; unfolding the concrete
   composition comparisons gives the underived equality. There is no `sorry` or
   forbidden declaration in the module. The delivery axiom probe checks all added
   constants; the public theorem is also checked in a scratch copy.
3. **Split statements: pass, none.** No holes or new public statements were added.
   The five private helpers are proved, strictly intermediate calculations; none
   moves the original hole elsewhere. Equality induction includes reflexive and
   identity squares, and quotient surjectivity includes zero complexes and empty
   schemes without extra hypotheses. No data is chosen from an unproved theorem.
4. **Route and pruning: pass.** Read both imported modules and searched the local
   library for congruence, unit transport, and homotopy comparison declarations.
   `directImageSquare_unit_transport` requires derived categories for all schemes,
   unavailable here; its elementary private helpers are not an accessible API.
   The present local equality-induction proof avoids that stronger assumption.
   Both imports supply public-signature definitions, so neither can be privatized
   or removed. Both original proof dependencies are used; `No longer needed` is
   complete. Read `sk-thm-picard-semicon.json`: no recorded realized unit step is
   bypassed or changed.
5. **DAG: pass.** Read the item's node and matched its two proof steps to the Lean:
   underived/homotopy comparison normalization, then unit equality transport using
   the composite-unit definition. Its proof dependencies and proof origin already
   describe this calculation, so no node edit is required. No new node is needed.

Second reading changed only this report, adding the independent review. No Lean
repair was needed. One original hole closed, zero holes added, no pruning.
