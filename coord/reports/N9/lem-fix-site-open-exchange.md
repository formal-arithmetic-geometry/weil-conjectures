1. Files written

- `dag/nodes/sec-smooth-purity/lem-fix-site-open-exchange.json`: repaired item; updated its source and blueprint ancestry to main-20261015, made the right-adjoint premise explicit, and cited the existing normalized finite open-exchange theorem.
- `dag/nodes/sec-smooth-purity/lem-cbc-proetale-open-right-adjoint-comparison.json`: new unsplit statement node for the sectionwise pro-etale right-adjoint comparison; Mathlib searches found no match.
- `citations.json`: regenerated verbatim citation witnesses for every current step/use pair.

2. Attachments

None. No sorry-free project declaration states the item or the new right-adjoint comparison.

3. WANTED:

None. The current main-20261015 proof and the cited Stacks site-comparison sources are present in the repository.

4. What was wrong in the returned version

The returned version used stale master sec-smooth-purity ancestry and treated the inverse-image comparison as if it also supplied a pro-etale direct-image/right-adjoint comparison. Its mate node therefore depended on an unproved `t`. I repaired the ancestry to the current main-20261015 compact-support coefficient-change proof, where the relevant route is the final site-comparison transport paragraph. I replaced the former mate helper by `lem-cbc-proetale-open-right-adjoint-comparison`, whose statement explicitly defines the two pro-etale composite right adjoints and gives their sectionwise canonical isomorphism. The existing `lem-cbc-finite-open-exchange-scalars` is cited for the canonical open base-change map's inverse-unit/mate normalization; this is a distinct, already landed statement and is declared as a cross-unit tool use. Steps 2–5 now use both premises explicitly. All stale references to the former helper and to returned master step 8 were removed from the item and report.

5. What I could not finish, and why

Nothing. No Lean file was written and no compiler, Lake, or build tool was run.

## Review by N9

I read the current main-20261015 parent statement and proof, the retained item, the full statements of every dependency used by all six steps, and the proof/source of `lem-cbc-proetale-extension-zero-base-change`. The parent statement is finite coefficient comparison for compact support; the item realizes its final site-comparison transport clause, so its ancestry now points to the main coefficient-comparison proof rather than the obsolete master sec-smooth-purity snapshot.

Step 1 uses the existing etale/pro-etale extension comparison, exact extension-by-zero statements, and canonical inverse-image comparison to construct the degreewise derived `c_j` and the oriented `rho`; each cited statement supplies the asserted naturality or exactness. Step 2 uses the actual etale and pro-etale open base-change maps, the underived etale mate normalization, and the new right-adjoint node for the pro-etale sectionwise comparison. The existing `lem-cbc-finite-open-exchange-scalars` supplies the separate canonical mate/unit characterization of the pro-etale exchange; its statement is broader coefficient-restriction data, so it is recorded as a tool use rather than treated as an unstated consequence of pullback coherence. Step 3 uses the unit-normalized site-comparison theorem to identify the specified `c_j` with the canonical comparison, including its Hom rule and transported unit equation. Step 4 applies the explicitly named composite-adjunction and mate-pasting formulas: the new node supplies `t`, the finite open-exchange node supplies the normalized mate, and comparison-pullback supplies the inverse-image coherence needed to cancel intermediate factors. Mate-bijection injectivity then gives the displayed equality. Step 5 identifies the common mate with the unit-normalized inverse and rewrites the comparison as the item’s `rho_{h,K}`; naturality follows from the cited comparison statements. Step 6 checks identity, empty-open, zero-complex, and zero-ring cases and uses no extra hypothesis on `g`.

I checked the new node on the identity square, an empty open, and the zero coefficient ring: the sectionwise comparison is respectively the identity or the unique zero-category map, and its adjunction compatibility remains valid. I searched Mathlib with LeanFinder, Loogle, grep, and LeanSearch for the new node; the hits were generic Zariski module adjunctions or generic category-theory comparisons and did not state the pro-etale square. The item’s citations now quote the current statement text verbatim, and its tool-use list records the one off-unit normalized mate theorem. No SGA source is used.
