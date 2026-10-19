# Stage-1 report: lem-pur-open-adjunction-shift

1. **Files written.**
   - `lem-pur-open-adjunction-shift.json` — statement node, split; no new nodes and no Mathlib leaves were created.
   - `citations.json` — six step/node quote records.
   - `report.md` — this report.

2. **Attachments.** None. I searched both read-only source trees for the item id, its title, and the open-extension/shift declarations; no sorry-free declaration states this item exactly.

3. **WANTED.** None. The proof uses the existing localized-site, system-realization, exact-derived-functor, and adjunction-shift statements.

4. **What I checked and corrected.** The imported node was unsplit and had no proof. I retained its statement and hypotheses, including the strict semilinear system category, quasi-compact open immersion, and the requirement that the equality hold before finite evaluation and total limit. I filled its blueprint provenance and recorded the four Mathlib searches actually run through `msearch.py`; the search results gave only generic shift/adjunction declarations and no extension-by-zero-specific theorem. I did not add a duplicate generic node because the existing DAG already contains the generic adjunction shift-compatibility statement and the exact derived-functor shift statement.

## Review by NX

I read the item node, `lem-pur-site-restriction-module-adjunction-exact`, `lem-sf-integral-compactification-system-realization`, `lem-sf-exact-functor-derived-triangulated`, and `lem-weil-pbc-adjunction-shift-compatibility-unique`. Step 1 uses the localized ringed-site statement exactly for the exact extension-by-zero/restriction adjunction and the realization statement exactly for the termwise system functors (J_j\dashv P_j). I checked that the realization statement uses the same strict system categories and records the maps before restriction/evaluation. Step 2 uses the exact-derived-functor statement for the termwise cochain shift and the generic adjunction theorem for the unique compatible right shift and for the implication from unit to counit compatibility; the given (P_j) comparison is the degreewise restriction comparison, so uniqueness identifies it with that structure. Step 3 checks that the resulting equations are equations of system maps before any finite-level evaluation or total limit, as required by the item. All hypotheses used in these applications are present: the open is quasi-compact, the ringed diagram categories are the module categories realizing the systems, and both termwise functors are exact. I also checked the zero/identity open cases: the adjunction is the identity and the shift squares reduce to identities.

5. **Could not finish.** Nothing remains for this stage; the sandbox is ready for the required dry run and delivery.
