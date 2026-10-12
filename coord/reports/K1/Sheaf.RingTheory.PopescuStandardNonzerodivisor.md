## What changed

The existing signature of `exists_popescu_standard_nonzerodivisor` is byte-for-byte
unchanged. Its proof obtains a smooth factorization over the total fraction ring,
applies the existing
`Algebra.exists_factorization_isElementaryStandardElement_of_localized_smooth`,
and converts its elementary standard element to a strictly standard element.
All existing public imports are unchanged. The two new helper imports are private
proof imports.

`PopescuStandardNonzerodivisorAux` now states only the localized smooth
factorization, not the almost-complete elementary-standard version of the item.
`elementary_standard_is_strict` is proved using the initial c-element subset,
`Finset.orderEmbOfFin_unique`, and `Matrix.det_transpose`.
No definitions, existing statements, or other modules were changed.

## Proved and sorry left

Hole closed: `exists_popescu_standard_nonzerodivisor` (1 of 1 original holes).
New theorem proved without sorry: `elementary_standard_is_strict`, node
`lem-weil-pbc-elementary-to-strict`.
Hole added and left: `exists_localized_smooth_factorization`, node
`lem-weil-pbc-popescu-standard-nonzerodivisor-aux`.
The latter has a complete proof in words in its docstring and a matching node.
No other delivered declaration contains sorry.

This is a decomposition, not a completed proof of the original mathematical
result: one original hole closed and one lower hole added, for net zero holes
removed. The main theorem also uses the existing open delocalization theorem.
The proved bridge uses only propext, Classical.choice and Quot.sound; the
localized helper and main theorem additionally depend on sorryAx.

## No longer needed

No dependency modules are pruned from the target's import closure.
`ReducedNoetherianTotalRingFractions` and `FilteredColimitSmoothProduct` cease to
be direct imports of the item but remain proof-plan imports of the open localized
helper. `PopescuDelocalizeBase` remains imported and is actually applied.

Every old direct proof dependency absent from the item's new proof_deps is listed
below. These dependencies remain in the localized helper's plan, or in the proved
bridge; they are not claimed as globally unnecessary:

- `lem-weil-pbc-noetherian-finitely-many-minimal-primes`
- `lem-weil-pbc-reduced-noetherian-total-ring-fractions`
- `def-weil-pbc-localization-at-prime`
- `def-weil-pbc-g-ring`
- `def-weil-pbc-flat-ring-map`
- `lem-weil-pbc-popescu-product`
- `def-weil-pbc-filtered-colimit-smooth-algebras`
- `def-weil-pbc-noetherian-ring`
- `lem-weil-pbc-filtered-colimit-algebras-elementwise`
- `lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`
- `def-weil-pbc-smooth-ring-map`
- `def-weil-pbc-strictly-standard-element`

## Where the brief, the DAG or earlier work was wrong

The first report claimed two split-off declarations but supplied neither new
node, and the existing node still recorded the old proof. Its auxiliary theorem
was the target with elementary in place of strictly standard, despite being
named a localized smooth factorization. The second reading replaced it with the
actual localized factorization and restored the existing delocalization step.
The first report's claimed removal of PopescuDelocalizeBase was incorrect.
The elementary-to-strict bridge required no new hole and is now proved.

## New nodes

`lem-weil-pbc-popescu-standard-nonzerodivisor-aux`: exactly the localized smooth
factorization in the third paragraph of Stacks 07F5. Its plan retains the total
fraction decomposition, product of ind-smooth algebras and finite-presentation
factorization steps of the old node. This is the sole new sorry.

`lem-weil-pbc-elementary-to-strict`: the elementary-to-strict conversion from
Stacks Definition 07C7 and the fourth paragraph of 07F5; its Lean proof is complete.
Both nodes include logged Mathlib searches, their verbatim Lean signatures,
sources, unit/chapter, blueprint provenance and proof plans. No change record is
needed because no existing statement, definition or public import changed.

## Second reading by K1

1. Compared the item with the repository by diff and directly compared the
   complete declaration signature before `:= by`: byte-for-byte identical.
   All existing public imports and definitions are unchanged. The helpers are
   new modules, and no adapted module or interface change is delivered. Pass.
2. Compiled all three modules in import order with lcompile.py, with no errors
   or warnings. Inspected all declarations: only the named localized helper
   has sorry; no forbidden declaration, compiler escape, hollow definition or
   data selection from an unproved existence statement occurs. Explicit
   #print axioms scratch checks verify standard axioms for the bridge and only
   the permitted standard axioms plus sorryAx for the open reduction. Pass.
3. Read Stacks smoothing.tex at Definition strictly-standard (07C7) and the
   third/fourth paragraphs of lemma-reduce-to-field (07F5), from the local
   literature mirror. The localized helper retains all hypotheses and only
   proves the pre-delocalization step. Checked the field base case (one factor),
   a reduced product base, A=R, and the zero target ring: none requires extra
   nontriviality of the target. No arbitrary witness becomes definition data.
   The bridge uses the same presentation and the same relation condition; its
   subset proof works for c=0, n=0, c=n, and the zero algebra. Searched Mathlib
   with msearch.py (LeanSearch unavailable, LeanFinder/Loogle and source grep
   successful), and searched Sheaf/upstream by standard-element, localization,
   factorization and ind-smooth terminology. No existing theorem states either
   helper. The first auxiliary was too close to the item; the replacement is
   strictly the localized factorization, and the main proof now actually applies
   the existing delocalization declaration. Pass after repair.
4. The proof follows the original source route: total fractions and field case,
   then delocalization, then elementary-to-strict. The last step is now closed
   directly with Mathlib enumeration and determinant lemmas. Proof-only helper
   imports are plain import. The two original field-case dependency imports
   remain in the open helper's proof plan. Every removed old direct DAG edge is
   listed above; no globally pruned module is claimed. Read sk-thm-p1.json
   realized: the item is below the unit's realized nodes, and no unit statement,
   route, realized field or chapter dependency changes. Pass.
5. Updated the item node's proof, proof_deps and proof_origin to the written
   reduction; its statement and lean signature stay unchanged. Added both
   missing node files with full fields, matching signatures and proof_deps
   equal to the union of proof-step uses. The localized node retains the first
   two source steps; the bridge records its actual finite-sum/transposition
   argument. No cycle or reference back to the item is introduced. Pass.

Second-reading changes: narrowed the auxiliary statement to a genuine localized
smooth factorization; proved the elementary-to-strict bridge; restored the
existing delocalization application; supplied both missing DAG nodes; corrected
the item proof plan, imports, sorry accounting and pruning claims.
