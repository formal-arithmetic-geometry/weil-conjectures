# Stage-1 report: lem-sfb-raynaud-generic-ample-power-model

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-raynaud-generic-ample-power-model.json`: existing statement node, now split into two steps. Mathlib verdict: no matching declaration after LeanFinder (two phrasings), LeanSearch, Loogle, and two grep queries. All original searches are retained; this run's exact searches and returned summaries are appended from `searches.jsonl`.
- `citations.json`: one citation, quoting the existing symmetrization node's statement verbatim.
- `report.md`: this report. No new DAG nodes or Mathlib leaves. No unit records changed.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id, its blueprint docstring tag, Raynaud, cubical/cubist, and ampleness terminology. The only Raynaud occurrence concerns flattening. The ample module files do not state the group-scheme generic-extension assertion. No Lean was written or compiled.

## Wanted literature

WANTED: Michel Raynaud, *Faisceaux amples sur les schémas en groupes et les espaces homogènes*, LNM 119 (1970), XI Theorem 1.13 and Corollary 1.16, for lem-sfb-raynaud-generic-ample-power-model and its existing symmetrization prerequisite. Neither local Raynaud filename used by the existing nodes is present.

WANTED: Moret-Bailly, *Pinceaux de variétés abéliennes*, Astérisque 129 (1985), VI 3.1 and II 3.3.3, for the original positive-extension context. No local copy is present.

I read Lan's revised thesis online at https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision-dense.pdf, Lemma 4.2.1.6 (printed p.76, PDF p.89), including its proof and adjacent Remark 4.2.1.3. It cites Raynaud XI 1.16 and uniqueness of cubical extensions. It is a source cross-check, not a proof of this item's normal-base generalization. I have not claimed to read Raynaud or Moret-Bailly. The proof is explicitly agent-written assembly of an existing DAG theorem.

## Findings and changes

The item was unsplit with an empty proof. The whole-DAG search found `lem-sfb-raynaud-generic-ample-symmetrization`, which already states the required auxiliary extension for the symmetrized generic line, without assuming properness of the generic fibre or symmetry of the original line. I reuse its full statement. Its closure (108 nodes, counting statement and proof dependencies) does not contain the item, so this introduces no circularity.

The two steps apply that node and identify its generic restriction with a positive power using the supplied symmetry. No statement or statement dependencies changed. In particular, no cubical structure, rigidification, or extension over a dense open is introduced. There is no reason to create a second Raynaud existence node.

I read the recorded chapter and unit, the three levels in SETUP.md, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and direct-image proof. The existing long `blueprint.from.place` records this node's historical auxiliary role. The current direct-image proof has changed upstream and does not explicitly contain that older alteration expansion. I preserve the inherited provenance and identify the precise auxiliary subargument in `split_report.blueprint`; I do not change the fixed chapter/unit route or maintainers' metadata. `blueprint_refs.py ancestor` reports None for this deep created chain, as the inherited field does. Whole-blueprint searches for ample, Raynaud, semiabelian and symmetrization found no blueprint node giving this auxiliary extension; `same_as` remains empty.

## Not duplicates

No new nodes are created. The more general existing node `lem-sfb-raynaud-generic-ample-symmetrization` is cited directly rather than copied or restated as a child.

## Review by Q30

I checked delivery-errors B through E against the actual item and the full statement of its sole cited theorem. Step 1 uses exactly the affine covering, integers a_i >= 1, ordinary invertible Q_i, generic isomorphism to (M tensor [-1]^*M)^a_i, and relative ampleness on every affine open provided by `lem-sfb-raynaud-generic-ample-symmetrization`. The normal integral Noetherian affine base is locally Noetherian, and the smoothness, separatedness, finite presentation, commutative group identities, semiabelian geometric fibres, and generic ampleness match that theorem verbatim. It does not require cubical data or properness, and I did not infer anything from its proof (it is unsplit). The complete relevant statement is in citations.json. This is an application to an existing more general theorem, not a newly created node carrying the item's conclusion.

Step 2 uses only the supplied isomorphism theta: [-1]^*M ≅ M and the definition of tensor power. I wrote the actual tensor map id tensor theta, its a_i-fold tensor product, and regrouping of the 2a_i factors. In rank-one frames this is the usual tensor map with an inverse from theta inverse, so the maps agree on overlaps. Thus d_i = 2a_i is positive and N_i = Q_i has the same ampleness as before. No assertion about preservation or descent of ampleness, properness of a model, or cubical extension is hidden here. It is elementary, needs no new lemma, and is under 2000 characters; step 1 is also under that threshold.

For edge cases I checked a_i = 1 (the output exponent is 2), a zero-dimensional integral base (a field), the trivial group (all lines are one-dimensional vector spaces), and characteristic 2. We never divide by 2 or require an odd tensor exponent, so these cause no exception. The base is nonempty by integrality. Empty members of an affine cover can be omitted. The argument makes no uniform-exponent claim across the covering. No statement dispute arose.

The semantic searches returned structure-sheaf localization and limit facts, affine-space/Proj maps, and ordinary module tensor-power identities. Their returned types do not construct a relatively ample line on a group-scheme degeneration. Loogle and the two targeted Mathlib greps returned no hits. I record these searches as actually run, preserve the inherited records, and do not claim a Mathlib match. No unavailable search is represented as a negative result.

## Unfinished work

None for this one-level split. The existing symmetrization prerequisite remains a separate unsplit item; its original literature is still WANTED. The delivery remains subject to the maintainer's independent mathematical review.
