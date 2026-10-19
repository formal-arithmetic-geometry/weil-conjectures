Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-affine-space-product-domain.json`: the item, statement split into five induction steps, no new node.
- `citations.json`: verbatim citations for every node used by every proof step.
- `searches.jsonl`: the required Mathlib searches, including the two concept phrasings and the name/pattern search; all returned no relevant match.

Attachments: none.

WANTED: none.

STATEMENT-DISPUTED: the imported conclusion displayed `\\nu^{\\otimes m}\\kappa_m`, but the statement introduces only `u:Rf_!M\\xrightarrow{\\sim}A_B`; in the parsed JSON the `\\n` was even interpreted as a newline, leaving an undefined `u`-free symbol. I corrected the conclusion to `u^{\\otimes m}\\kappa_m`, which is the only well-typed faithful reading. No other hypothesis or conclusion was changed.

I could not find a finished declaration tagged `(blueprint: lem-pur-affine-space-product-domain)` in either read-only Lean source checkout, so this is a split rather than an attachment. No Lean files were written or compiled.

## Review by Q38

I read the copied item against `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/prop-pur-affine-space-composition-law.md`, the `sk-prop-an` unit, and the parent node's imported proof route. I checked the corrected `u`-notation against the induction conclusion and tested the base cases conceptually at `m=1` and `f=id`. Step 1 uses only the definitions and the given isomorphism: `M_1=M`, `V_1=Rf_!M`, and the unit has interval `[0,0]`. Step 2 cites `thm-sf-ctf-stability` exactly for pullback preservation and tensor preservation of bounded finite-Tor constructible objects, which verifies that the two pullbacks and their tensor are `M_{m+1}`. Step 3 cites the full relative Kunneth statement for the exact inverse-composition/exchange/projection construction, `thm-sf-pf-proetale` for invertibility of each projection transformation on the finite-Tor domains, and `def-exchange-projection` for the concrete map composites. The induction hypotheses supply the required finite-Tor inputs `M` and `V_m`; the source and target morphisms are separated finite type as required by those statements. Step 4 cites the tensor interval clause of `thm-sf-ctf-stability` to compute `[0,0]+[0,0]=[0,0]` and uses the two displayed object isomorphisms to identify `V_{m+1}` with `A_B`. Step 5 defines the recursive `κ_m`, composes isomorphisms, and applies the corrected tensor power `u^{\\otimes m}` with canonical associators and unitors. Every citation quote in `citations.json` was copied verbatim from the cited node statement. No new node was necessary, no duplicate or Mathlib leaf was created, and no SGA source was used.
