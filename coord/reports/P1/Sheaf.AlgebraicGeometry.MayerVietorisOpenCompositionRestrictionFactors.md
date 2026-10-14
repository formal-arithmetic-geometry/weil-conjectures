## What changed

Proved `AlgebraicGeometry.schemeMVOpenComposition_restriction_factors` in
`Sheaf.AlgebraicGeometry.MayerVietorisOpenCompositionRestrictionFactors`.
The private, fully proved `restriction_factors` lemma expresses the naturality square
for arbitrary categories and functors, precomposed with the localization unit and
postcomposed with the inverse restriction comparison. The public proof specializes
this lemma with explicit objects P, Q and R. All existing signatures and docstrings,
and the sole public import, are unchanged. No additional modules or nodes are needed.

Explicit endpoint objects avoid expensive conversion through the source complex
presentation. The original file-level options and attributes are unchanged. The final
file compiled cleanly in 8.1 seconds, within the unchanged 60-second limit.

## Proved and sorry left

Closed: `AlgebraicGeometry.schemeMVOpenComposition_restriction_factors`
(node `lem-pc-mayer-vietoris-open-composition-restriction-factors`).
One original hole closed; zero holes added; no sorry remains in the delivered module.
The private helper is completely proved by naturality, map_comp and associativity.
The delivery dry run checks the axioms of the public theorem and private helper.

## No longer needed

None. The sole existing import `Sheaf.AlgebraicGeometry.MayerVietorisImageChainData`
is required by the unchanged statement. Both recorded proof dependencies,
`def-pc-mayer-vietoris-image-chain-data` and
`def-pc-derived-mayer-vietoris-canonical-data`, remain necessary. The proof follows
the recorded plan, so no DAG update or unit-route change is required.

## Where the brief, the DAG or earlier work was wrong

The inherited sandbox attempt contained a naturality proof but no report or successful
dry run. Its large congruence calculation timed out. The replacement generic lemma
and explicit endpoint arguments compile promptly without changing definitions or
raising the time limit. No mathematical error in the statement or DAG was found.
The naturality argument applies equally to empty/full opens and identity morphisms,
and requires no cover or injectivity hypotheses.


## Second reading by P1

1. PASS: compared the sole delivered module with the repository using `diff -u`;
   independently checked the existing theorem signature byte for byte. Only its
   proof and a fully proved private helper are added. All existing definitions,
   docstrings, visibility, imports and options remain unchanged. No interface
   change or change record is required.
2. PASS: compiled the delivered file locally through `lcompile.py` with no errors
   or warnings (7.7 seconds). No sorry or forbidden trust declaration occurs.
   A scratch copy with `#print axioms` for both the public theorem and private
   helper compiled in 7.9 seconds: each lists only `propext`, `Classical.choice`
   and `Quot.sound`, with no `sorryAx`. The delivery constructs no data and
   selects no new witness.
3. PASS: no statements were split off, no new holes or public declarations were
   introduced. The private helper is a proved, strictly general naturality
   calculation, not a restatement left unproved. Its equation follows directly
   from beta.hom.naturality, functoriality and associativity, including identity
   maps and degenerate categories; specialization therefore also covers empty
   and full opens. There are no split statements requiring new nodes or searches.
4. PASS: read the localization and comparison definitions and searched the local
   library for restriction-factor/naturality variants, plus a fresh msearch grep
   for `naturality_assoc|naturality_app|NatTrans.naturality`. The proof already
   takes the direct Mathlib naturality route; no further intermediate theorem is
   needed. The sole public import supplies the existing signature and cannot be
   pruned. Both old proof dependencies are used, so `No longer needed: None` is
   complete. Read `dag/units/sk-thm-picard-semicon.json`: its realized statement
   and step lists are empty and this below-unit calculation changes no route.
5. PASS: read node `lem-pc-mayer-vietoris-open-composition-restriction-factors`
   and its recorded proof and dependencies; they describe exactly the expansion,
   naturality and functorial composition implemented here. The existing proof
   origin remains consistent, with no new nodes or DAG edits needed. Also read
   the relevant earlier import-change record for the parent normalization module;
   this delivery does not alter that interface or its users.

Second reading changed only this report by adding the independent review and
explicit compilation/axiom evidence. No Lean repair was needed. Confirmed one
original hole closed, zero holes added, no split-off obligations and no pruning.
