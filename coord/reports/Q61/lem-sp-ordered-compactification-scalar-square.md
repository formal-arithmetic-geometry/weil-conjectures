# Q61: lem-sp-ordered-compactification-scalar-square

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-ordered-compactification-scalar-square.json: statement item split into seven proof steps; no Mathlib match.
- citations.json: verbatim statement excerpts for each node cited in each proof step.
- report.md and searches.jsonl: report and actual search log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures by the item's exact tag and by ordered compactification, scalar square, and compactification/coefficient terminology. The LowerShriek/Formalism files give generic compact-support composition formalism, without the ordinary-etale finite-coefficient extension square in this item. They do not state every clause here. No existing Lean audit or Lean declaration is attached to the item.

## WANTED

None.

## What changed and why

The item was unsplit with no proof. Its statement is retained verbatim, along with its source, creation record, chapter, unit and blueprint ancestry. The seven steps check the domain, identify the actual line coefficient arrow, set up an induction for all inputs, apply the binary composition square, write the naturality substitution explicitly, pass to the specified compactification, and check independence and the zero-dimensional normalization. The proof is recorded as agent-written: the Charts paragraph motivates it, but does not itself write this induction.

I read the current main-20261015 Charts proof and the sk-lem-sp-reduction unit and chapter. In Stacks more-etale.tex I read lemma-shriek-composition (Tag 0F7J), including its choice-independence argument, and remark-Rf-lower-shriek-change-of-rings (Tag 0GL6). The remark gives commutation of derived scalar extension with compact support; it does not by itself assert equality of all the specified arrows. The existing coefficient-compatibility node supplies those normalized binary and refinement equalities. No SGA source was used.

## Search and reuse

Whole-DAG statement reads found the already-existing lem-sp-et-proet-coefficient-compatibility, lem-amb-etale-compact-comparisons, lem-sp-etale-ctf-chart-domain, lem-sp-finite-compact-support-domains, and lem-pur-etale-compact-scalar-coherence. The last two were read but are not needed: the same-unit chart-domain node and the coefficient-compatibility node suffice. Checked that none of the five cited nodes has this item in its dependency closure.

Ran blueprint_refs.py ancestor and searches for "compactification scalar" (no blueprint match) and "ordered" (47 matches, none stating this specified square). Retained same_as: []. This is a specialization of a general coherence theorem plus a finite induction, so creating another coherence or one-clause node would duplicate existing material. Every step is under 900 characters; none hides a long comparison argument.

The inherited Mathlib searches remain recorded. Additional actual Q61 searches are appended exactly from searches.jsonl: LeanFinder with two formulations, Loogle naturality, LeanSearch, and a Mathlib grep. The first semantic search and LeanSearch concern compactly supported continuous/test functions; the second LeanFinder search concerns the pseudofunctor of scheme module pullbacks, rather than derived ordinary-etale compact support and coefficient extension. Loogle gives general naturality, which is only the elementary equality in Step 5. No hit proves the item as a one-line specialization. No new nodes require independent search records.

## Tool uses

lem-weil-pbc-finite-type-over-noetherian is the generic Noetherian permanence tool. lem-amb-etale-compact-comparisons gives canonical composition and refinement coherence. lem-sp-et-proet-coefficient-compatibility gives the actual coefficient composition and refinement squares. All three are declared in split_report.tool_uses; none changes the unit's proper/open coefficient route or its ordered projective-line integration argument. The finite-Tor domain tool is in the item's own unit.

## Not duplicates

No new nodes were created. The generic binary square is used from the existing node rather than repackaged as a new node.

## Review by Q61

I checked delivery-errors B through E against the node and sources. There is no new unsplit statement, hollow object, bare literature citation used as a theorem, or restatement of this item hidden in another node. The item is not a unit key statement, so no unit binding fields are changed. The split uses the prescribed Charts route, adding only the explicit induction that the imported proof omitted.

For Step 1 I read the statements of lem-weil-pbc-finite-type-over-noetherian, def-amb-affine-trace-tower, and lem-sp-etale-ctf-chart-domain. The first really gives Noetherianity for finite type over a Noetherian base; Spec k satisfies the base condition because a field has only two ideals. The tower node gives the standard compactifications and separated finite-type maps. The domain node states preservation of bounded constructible finite-Tor complexes both by each specified compact-support candidate and by scalar extension. Thus applying the induction to L_r,A M does not require a lower bound on a resolution of B or its projective dimension.

For Step 2 I read the definition of the coefficient map in lem-sp-et-proet-coefficient-compatibility: proper counit mate followed by the open tensor identification, in the same order as the item's b^{u_r}. Its separated-etale sum normalization and final identity clause cover the identity compactification. With one identity summand, the scalar map is the identity. This checks equality of the specified maps, not just existence of some isomorphism.

For Step 3 I read the composition assertion of lem-amb-etale-compact-comparisons: its natural composition isomorphism is on D+, independent of compactification choices and associative. Step 1 supplies D+ for all A and B inputs. The induction quantifies over every input at level r; otherwise its use at L_r,A M would be unjustified. The recursive D is only an auxiliary spelling of the existing comparison, not a new construction asserted without a theorem.

For Step 4 I checked every factor against the displayed composition equation in lem-sp-et-proet-coefficient-compatibility, substituting f=u_r and g=p_r. The middle functor is H_r,B; its argument is the actual line coefficient arrow. Step 5 writes the naturality square for D_r,B at precisely that arrow, moving H_r,B(b^{u_r}) past D_r,B. Associativity and the two defining recursions then give B_{r+1} in its specified order. This algebraic substitution is elementary and uses no unstated geometric lemma.

For Steps 6 and 7 I read the refinement square and the explicit final common-refinement/identity/associativity sentence in the coefficient node, and the independence/cocycle/associativity assertions in the compact-comparisons node. Pasting their square with the inductive equality yields exactly C_B B_d. The auxiliary final compactification is compared to the specified c, rather than silently replacing c. For d=0 the auxiliary one is the identity, but c need not be; the same refinement pasting proves that case. Independence concerns the resulting canonical C for the fixed ordered product; changing parentheses uses the cited associativity constraints.

Small-case checks: d=0 as just described; d=1 reduces to the named proper/open composite; A=B uses its identity coefficient maps; M=0 gives the zero-object equality; the zero ring and N=1 give trivial module categories and no exception. Nonflat A->B, for example Z/ell^2->Z/ell, is permitted because every intermediate input remains finite-Tor by the domain node. Nothing in the induction assumes tensor exactness on arbitrary modules. Empty schemes cause no change to the functorial identities. No statement dispute was found. While checking citations I expanded the Step 4 quote to its whole formula, and used the actual composition sentence for Step 3 rather than an unrelated refinement sentence. Each citation quote is a verbatim substring of the named node's statement.

## Unfinished work

None in this one-level split. The existing cited nodes retain their own independent proof obligations; no Lean was written and no compiler or build tool was run. Server dry run and direct delivery follow this report.

The first dry run requested longer Step 1 excerpts for Noetherian permanence and the affine tower. I replaced both with the full relevant hypothesis-and-conclusion sentences; the proof itself required no change.
