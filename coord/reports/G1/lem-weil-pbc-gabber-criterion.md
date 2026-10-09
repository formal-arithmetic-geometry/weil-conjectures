# Delivery: `lem-weil-pbc-gabber-criterion`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-gabber-criterion.json` — statement node, split; proof follows Stacks 0GY0 in five steps.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-gabber-strict-henselian-zariski-comparison.json` — new statement node for Stacks 09AX; Mathlib verdict: no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-zariski-cohomology-locally-zero.json` — new statement node for local triviality of positive-degree Zariski cohomology; Mathlib verdict: no match.

## Attachments

None.

## Review notes

- The imported statement agrees with Stacks 0GY0 and was retained.
- The imported node had no proof; it is now split into: etale/Zariski comparison on principal opens; induction simultaneously over all principal opens (so no localization transport is assumed); the ideal $I_h$ of principal opens inside $D(h)$ killing a class; degree-one addition by applying the stated kernel hypothesis to $hf,hg$; and higher-degree addition by Mayer–Vietoris, followed by $h\\in\\sqrt{I_h}$ and the vanishing conclusion.
- The local-triviality argument was initially hidden in the ideal step and was extracted as its own node, as required by the Stage 1 rule for non-elementary arguments.
- No Lean source declaration or attachment was present. Mathlib searches (LeanSearch, LeanFinder, and source grep) found no matching etale/Zariski comparison, local-triviality theorem, or Gabber criterion. The new 09AX node explicitly names the etale-to-Zariski site morphism and the site-cohomology pullback node.

## Checks

- `python3 tools/check_dag.py`: passed structurally; reports six pre-existing unreachable-node warnings.
- `python3 tools/review_split.py lem-weil-pbc-gabber-criterion`: passed.

## Unfinished

The two newly created nodes remain `unsplit` and join the queue.

## Repair review

The repaired step 1 cites `lem-weil-pbc-principal-localization-open-immersion` for $D(h)=\\operatorname{Spec}(R_h)$ and `lem-weil-pbc-spec-domain-stalks-function-field` for the local rings $(R_h)_{\\mathfrak pR_h}\\cong R_{\\mathfrak p}$. The induction quantifies over every original $h\\in R$; it does not replace $R$ by $R_h$. For fixed $h$, $I_h=\\{f: \\xi|_{D(hf)}=0\\}$ is used, and the degree-one step applies the original hypothesis to $hf,hg$, whose target opens are exactly the required opens after removing redundant powers of $h$. In higher degree, the existing etale Mayer–Vietoris node applies to $D(h(f+g))=D(hf(f+g))\\cup D(hg(f+g))$, and $P(i-1)$ kills the intersection term. Local triviality shows every prime avoiding $h$ avoids $I_h$, hence $h\\in\\sqrt{I_h}$ and the class vanishes on $D(h)$.

Validation evidence: both node files parse with `python3 -m json.tool`; `python3 tools/check_dag.py` reports 3183 nodes, 0 cycles, and only the six pre-existing unreachable-node warnings; `python3 tools/review_split.py lem-weil-pbc-gabber-criterion` passes and recognizes both new nodes. No unrelated files were changed.

## Review by G1

I checked the repaired proof against the actual Stacks `etale-cohomology.tex` proof at lines 14205 and 14228. The induction now stays over the original ring and uses `I_h`, so the returned localization-transport gap is removed; the degree-one and Mayer–Vietoris identities have the required `h` factors. Step 1 cites the principal-localization and stalk-identification nodes, and the 09AX child defines the site morphism and cites site-cohomology pullback. The report now cites the obtained source rather than `WANTED`. The repaired node and its children pass the DAG checks, and no unrelated file changed. I accept this repair.
