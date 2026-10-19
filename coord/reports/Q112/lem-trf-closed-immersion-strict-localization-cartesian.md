# Worker report: lem-trf-closed-immersion-strict-localization-cartesian

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-closed-immersion-strict-localization-cartesian.json`: statement, no Mathlib match; repaired four-step split using existing nodes only.
- `citations.json`: refreshed verbatim statement quotations for all 18 step/node citation pairs.
- `report.md`: replacement report incorporating the maintainer's return at head `e5b4bf56c0` and this repair.

The unmerged sandbox file `lem-trf-strict-henselization-residue-uniqueness.json` has been removed, as requested. No new nodes and no new Mathlib leaves are delivered. The existing `searches.jsonl` is retained in full, including the searches for that withdrawn node; no new searches were needed or claimed.

## Attachments

None. I repeated the read-only search in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id and for strict-henselization, strict-localization and closed-immersion terminology. The hits concern other closed-immersion or strict-local constructions; none states the complete item. The exact upstream master remains reference material only; no compiler was run.

WANTED: none. The local Stacks sources contain all sources used in this repair.

## What was wrong and what changed

The retained sandbox agreed with the returned version: it used a new residue-uniqueness node in Steps 2-4 and asserted that uniqueness among isomorphisms made the given local map an isomorphism. Compared with the current shared item, its statement, statement dependencies, blueprint ancestry, chapter, unit and source metadata already agree. The shared item is still unsplit. I retained the four-step affine quotient route, the previous item searches and their logged results, the geometric residue-field comparison and the source citations. The initial required dry run passed mechanical preflight; the mathematical defects in the return still required the following substantive repair.

### STATEMENT-DISPUTED: withdrawn auxiliary statement

The removed node was false: it omitted the requirement in Stacks 08HT that the two structural composites from the base ring to the common residue field agree. Take $R=S=S'=K=\mathbb Q(i)$, all algebra structures identities, with $\epsilon=\mathrm{id}$ and $\epsilon'$ complex conjugation. The only $R$-algebra endomorphism is the identity, which cannot satisfy $\epsilon'\theta=\epsilon$. This is an error in the delivered auxiliary statement, not in Stacks or in the item. Rather than creating a corrected duplicate, I removed the node and all its citations. The item's statement is unchanged.

The repaired Step 2 forms the explicit quotient $Q=C_W/IC_W$ and factors the canonical ring map as $h^\#=\bar hq$. It only needs the quotient theorem's existence of a strict-henselization presentation relative to some $L$; it does not silently identify that unspecified field with the geometric $K$. The residue field of $Q$ is instead identified directly through the existing strictly henselian quotient theorem in Step 3.

Step 3 now applies `lem-weil-pbc-map-into-henselian-colimit` (08HR), whose statement gives existence and uniqueness among all maps with the prescribed prime preimage and residue map. It first applies with source $Q$ and target $C_Z$, then with source $C_Z$ and target $Q$ to construct $v$, then to endomorphisms of each ring to show $v\bar h=1$ and $\bar hv=1$. This repairs C4 without a new corollary (C5).

I added `lem-weil-pbc-strictly-henselian-quotient` and `lem-sc-pointed-etale-filtered` to Step 3 and its proof dependencies, repairing C1/E1. The step states why their hypotheses hold. I removed the unused `lem-sbc-pointed-etale-quotient-final` tool declaration and added declarations for the affine comparison and the three actual mapping/quotient/filteredness tools. These are requests for review in `split_report.tool_uses`, not maintainer-owned accepted `tool_uses`.

## Not duplicates

No new node is proposed. The withdrawn residue-uniqueness node duplicated consequences of `lem-weil-pbc-map-into-henselian-colimit`; the repair directly cites that existing node. No replacement node is created for an elementary inverse-composite argument or for a clause of the item.

## Review by Q112

I reread the item, the return in `coord/returns/Q112.md`, its parent `lem-trf-nearby-closed-image`, chapter `sec-trace-formula`, unit `sk-i-curve-zero`, the blueprint ancestry recorded in the item, and the full statements of every cited dependency. The split continues to supply the strict-local tube identification used in the closed-image reduction; it changes neither the chapter nor the unit route. The off-unit inputs are generic affine and ring-theoretic tools and are explicitly declared for the maintainer's review. No SGA source is used.

For the source I read local `algebra.tex` at 08HR (`lemma-map-into-henselian-colimit`, line 42881), 08HT (`lemma-uniqueness-henselian`, line 42902), 04GU (`lemma-strictly-henselian-functorial`, line 43369), 04GW (`lemma-strict-henselization-different`, line 43400), 05WR (`lemma-quasi-finite-strict-henselization`, line 43632) and 05WS (`lemma-quotient-strict-henselization`, line 43703), and `etale-cohomology.tex` 04HX (`lemma-describe-etale-local-ring`, line 4257). I checked the tag-to-label mapping. There is no new node needing a separate source review. Stacks 08HT has the commuting base-to-residue diagram missing from the removed node, and its proof explicitly reduces to 08HR; this is exactly the argument now written out in Step 3.

In Step 1, `def-weil-closed-immersion` explicitly includes the affine quotient characterization (01QO); `def-weil-affine-spectrum` gives the affine ring/morphism interpretation; `def-pc-fibre-product` supplies the comparison morphism's universal property. The statement of `lem-weil-pbc-etale-local-ring-triples`(2)-(3) permits restriction of the chosen geometric colimit to either affine chart. The statement of `lem-exc-affine-strict-local-ring-comparison` gives an algebra isomorphism to the local-ring strict-henselization colimit with the prescribed geometric evaluation and identity residue identification. Both local rings have residue field $\kappa(\mathfrak p)$, since $I\subseteq\mathfrak p$, so the same $K\subset\Omega$ is used. The colimit definition cited in this step specifies the chosen geometric ring and spectrum.

In Step 2, `lem-sbc-strict-henselization-surjective-quotient` applies to the surjection $A_{\mathfrak p}\to(A/I)_{\mathfrak p/I}$: these are local rings, and its kernel $IA_{\mathfrak p}$ lies in the maximal ideal. Its statement gives precisely the explicit quotient $Q$ as an algebraic strict henselization relative to some $L$, not an isomorphism for an uncontrolled canonical map. `def-sc-ring-strict-henselization` specifies the colimit presentation. `lem-weil-pbc-strict-henselization-functoriality`(1)-(3), together with the affine comparison, gives the canonical local map and its identity map on the common geometric residue field. The factorization through $Q$ follows directly because the structural map kills $I$; its locality follows by taking the preimage of the target maximal ideal under the surjective quotient map. No assertion that an arbitrary abstract isomorphism equals this factorization is made.

In Step 3, the affine comparison gives strict henselianity of $C_W$ and $C_Z$. The structural map $A_{\mathfrak p}\to C_W$ is local, hence $IC_W\subseteq\mathfrak m_{C_W}$; `lem-weil-pbc-strictly-henselian-quotient` therefore gives henselianity of $Q$, its maximal ideal and unchanged residue field. The colimit definition and `lem-sc-pointed-etale-filtered` apply over $R=(A/I)_{\mathfrak p/I}$ to each chosen separable closure, so both sources are filtered colimits of etale $R$-algebras. Small representatives are supplied by the definition. The maps to $K$ agree on $R$, a condition verified explicitly from the compatible quotient and functorial map; thus every identity residue map used in 08HR is a $\kappa(\mathfrak m_R)$-algebra map. In each application the source prime is its maximal ideal, which lies over $\mathfrak m_R$, and the target is henselian local. The existing 08HR node states uniqueness among all such $R$-algebra homomorphisms, so it identifies $\bar h$ with the forward map and proves that both inverse composites are identities. These verifications fix every substantive point in the return.

In Step 4, the cited affine-spectrum and fibre-product statements, with the closed-immersion quotient chart, identify the spectrum of the quotient with the required fibre product. Its projection maps are the structural map to $Z$ and the spectrum of $h^\#$, so the isomorphism obtained is the exact canonical morphism in the item's statement. This is the elementary final affine quotient interpretation already accepted in the return; no uniqueness-node citation remains there.

I rechecked B-E against the actual delivery: no new statement-only node or definition is needed, no proof depends on a hidden new lemma, each cited statement supplies the clause used, and the union of step uses is exactly `proof_deps`. The 08HR applications are a direct instantiation and inverse argument, not a concealed comparison lemma. All four steps are under 2000 characters. I checked the small cases $I=0$ (identity), $I=\mathfrak p$ (strict localization of the closed point), and a nilpotent quotient $k[\epsilon]/(\epsilon^2)\twoheadrightarrow k$ (kernel still generated by $\epsilon$). The unit ideal is excluded by the existence of the given point on $Z$. The counterexample with conjugation is excluded exactly because the repaired argument verifies common base-to-residue compatibility. No Noetherian or reducedness assumption is used.

The previous search log was read and retained: the item searches found ordinary quotient/localization, henselian, and closed-immersion base-change facts, not the strict-henselization comparison; the searches for the removed auxiliary node likewise do not yield an attachment. No search was invented or repeated. Every refreshed `citations.json` quotation was checked as a verbatim substring of the current cited node statement, with one entry for every step/node pair.

## Unfinished work

None in the stage-1 split. The existing dependency nodes remain their owners' items. This repair writes only inside the item sandbox and performs no Lean, Lake or build operation.
