# Delivery report

1. Files written:

   - `dag/nodes/sec-proper-base-change/lemma-weil-pbc-proper-underived-exchange.json` — repaired statement node, split.
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-sections-base-field-extension.json` — new unsplit statement node for Stacks Tag 0A3I; no Mathlib match.

2. Attachments:

   - No new attachments.

3. WANTED:

   - None.

4. Problems found and corrected:

   - The returned step 1 incorrectly treated both closed geometric fibres as the fibre over the single field $\\Omega$. I added the missing Stacks 0A3I node and now pass separately from the fibres over $\\kappa(y)^{\\mathrm{sep}}$ and $\\kappa(y')^{\\mathrm{sep}}$ to the fibre over $\\Omega$ using pullback-section invariance.
   - Step 1 now cites `lem-weil-pbc-proper-base-change` for properness of $f'$, and explicitly checks the quasi-compact/quasi-separated hypotheses of the stalk formula and torsion of $g'^{-1}F$.
   - Step 2 now follows the blueprint sketch's explicit germ computation: a germ $s$ over an etale neighbourhood is restricted along $X'\\times_{Y'}V\\to X\\times_YW$, and both stalk identifications are the same restriction to $X\\times_Y\\operatorname{Spec}\\Omega$. The unused naturality citation was removed from the step's uses; the imported `uses_not_cited` field remains untouched.

5. What remains unfinished:

   - The Lean declaration `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isProper` still contains `sorry` in slopmaster2; stage 1 records this in `lean_audit` and does not write Lean.

## Review by M1

I read the returned entry, the item blueprint proof for Tags 0A3T/0A3U, the explicit blueprint sketch's final germ paragraph, and the existing nodes for the strict-henselian stalk formula, proper strict-henselian H0 comparison, cartesian square, scheme conventions, etale sheaves, underived exchange, properness under base change, and geometric-stalk conservativity. For the new node I checked the Stacks 0A3I statement and searched the whole DAG and blueprint for duplicates before creating it; the Mathlib searches were LeanSearch (service error with no result), LeanFinder (only unrelated `FormallyEtale` declarations), and a source grep (no sheaf-theoretic declaration). The new node is consistent with the strict-henselian H0 node's warning about transcendental geometric points: that warning concerns the sheaf restricted to the canonical closed geometric fibre, while 0A3I concerns the pullback sheaf after extending a separably closed base field, whose sections are unchanged.

For repaired step 1, I verified that the cited proper-base-change node states exactly preservation of properness, that properness in the scheme conventions supplies finite type and separatedness and hence the qcqs hypotheses, and that inverse image preserves the relevant geometric stalks and torsion condition. I checked that the two H0 comparisons land over the separate separable closures and that 0A3I is then applied to each pullback sheaf to reach $\\Omega$. For step 2, I checked the exchange definition's restriction along the base-changed neighbourhood map and wrote the stalk calculation on a representative germ, with both comparison maps identified as restriction maps from step 1. Step 3 remains the cited geometric-stalk conservativity argument. I also checked the item and new node JSON parse, blueprint provenance, statement dependencies, and proof-dependency union. The repair changes the false fibre assertion, adds the missing node and dependency, adds the properness and hypothesis checks, and removes the unsupported naturality use.
