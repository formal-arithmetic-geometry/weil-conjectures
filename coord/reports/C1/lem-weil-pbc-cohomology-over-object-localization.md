1. Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-cohomology-over-object-localization.json`: repaired item split, no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-site-restriction-injectives.json`: replacement statement-only extension-by-zero dependency, no Mathlib match.
- `citations.json`: verbatim citations for every non-elementary node use.

2. Attachments: none.

3. WANTED: none.

4. What was wrong or incomplete: the returned dependency restated the item's restriction-preserves-injectives clause, exactness, resolution, and section identity, so it carried nearly the whole item. I deleted that broad statement and replaced it with the strictly smaller general-site fact from Stacks 03DH, 03DI, and 03DJ: extension by zero is an exact left adjoint to restriction, and restriction is exact. The item now derives injective preservation using the existing right-adjoint lemma, constructs the restricted resolution, identifies the two section complexes, and writes both naturality arguments. The report now names `citations.json`, and the new node has complete `created` metadata.

5. What I could not finish: no mathematical part remains unfinished; the replacement dependency is intentionally statement-only for the next stage.

## Review by C1

I reread the item source, Stacks Cohomology on Sites Lemma 03F3, and the proof sources it invokes: Sites Section 00XZ for the localized slice, Modules on Sites Section 03DH and Lemmas 03DI/03DJ for extension by zero, and Homology Lemma 015Z for preservation of injectives by a right adjoint of an exact functor. I also opened the statements of every DAG node cited by the repaired proof. The new node says only that the restriction functor on an arbitrary slice site has an exact left adjoint extension by zero and is itself exact; it does not assert injective preservation or the cohomology comparison.

Step 1 is the elementary slice construction and final-object check. Step 2 cites the new node, whose adjunction and exactness clauses state exactly what the step uses. Step 3 cites that exactness clause and `lem-sp-right-adjoint-preserves-injectives`; its hypotheses are met because extension by zero is the exact left adjoint, so restriction is its right adjoint. Step 4 cites `def-weil-pbc-sites-and-cohomology`, whose statement explicitly computes cohomology from an injective resolution, and uses the sectionwise restriction identity from the definition. Step 5 cites `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy` for independence of the chosen lifted resolution map and `def-pur-localized-ringed-site` for the relocalization identity and sectionwise restriction. Every quote in `citations.json` is a verbatim substring of the cited statement.

I checked the hypotheses on the edge cases $q=0$, $W$ terminal (the slice is the original site up to its evident identification), and the zero sheaf; in each case the comparison is the identity on the same section complex. I also checked a composite $W'\\to W$ by expanding the relocalized objects and their section values, which is why the final step states the sectionwise identity instead of appealing only to “functoriality.” The returned D1/D2 issue is repaired by deleting the broad node, D3 by adding the extension-by-zero and right-adjoint lemmas plus explicit naturality dependencies, and A/F by retaining the actual `citations.json` file and complete `created` fields.
