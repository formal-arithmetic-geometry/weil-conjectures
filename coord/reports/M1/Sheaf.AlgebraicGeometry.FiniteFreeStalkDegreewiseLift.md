## What changed

The existing theorem `AlgebraicGeometry.Scheme.Modules.exists_degreewise_of_stalk_local`
now composes individual-degree representation, finite common-neighbourhood restriction,
and choice of one representative per degree. Its signature and visibility are unchanged.
Two proof-only imports provide the two lower steps, in separate new modules:
`Sheaf.AlgebraicGeometry.FiniteFreeStalkDegreewiseLocal` and
`Sheaf.AlgebraicGeometry.FiniteFreeStalkDegreewiseLiftCore`.
The new local theorem does not require boundedness; the new common-neighbourhood
theorem does not require freeness. Their docstrings give complete mathematical proofs.

## Proved and sorry left

Closed hole: `AlgebraicGeometry.Scheme.Modules.exists_degreewise_of_stalk_local`
(node `lem-pc-finite-free-stalk-degreewise-lift`). Its proof still depends on sorryAx.
Added holes (both whole proofs of public named theorems):
- `AlgebraicGeometry.Scheme.Modules.exists_local_degreewise_of_stalk_local`,
  node `lem-pc-finite-free-stalk-degreewise-local`, in `FiniteFreeStalkDegreewiseLocal`.
- `AlgebraicGeometry.Scheme.Modules.exists_degreewise_of_stalk_local_core`,
  node `lem-pc-finite-free-stalk-degreewise-lift-core`, in `FiniteFreeStalkDegreewiseLiftCore`.

This is a decomposition, not a completed proof: one hole closed, two holes added,
net -1 before any closure-specific ledger accounting. No lower hole was closed by
this second reading. The common-neighbourhood theorem assumes the individual-degree
representatives; it isolates restriction and finite intersection rather than restating
the original existence theorem. The local theorem supplies those representatives
without assuming a common neighbourhood. Choice is inside the proposition proof only;
no data definition is introduced or chosen from an unproved existence theorem.

## No longer needed

No imports or modules are pruned. The old direct proof-dependency list was
`def-pc-derived-pullback`, `def-pc-stalk-restriction-complex-iso`,
`def-weil-pbc-free-module`, and `def-weil-pbc-module-stalk`.
All four are removed from the item's direct `proof_deps` in favour of the two new
lemma nodes. All four remain needed through the lower statements or their proofs;
none is declared unreachable. The public comparison and cochain-embedding imports
remain necessary for the existing statement. The two new imports are proof-only.

## Where the brief, the DAG or earlier work was wrong

The earlier report described one core sorry while delivering two. It also called
the reduction a proof without clearly accounting for the extra hole. Both new
sorry docstrings omitted the required complete proof in words. The target node
listed only the common-neighbourhood theorem although its proof calls both lower
theorems. The common-neighbourhood node incorrectly listed the local existence
lemma as a proof dependency instead of treating local existence as its hypothesis.
These reporting and dependency faults are repaired. No mathematical error in the
unit route has been established or assumed.

## New nodes

`lem-pc-finite-free-stalk-degreewise-local` isolates finite-matrix representation for
one degree, with zero-term and rank-zero cases; it needs no support bounds. Its
module is `lean/Sheaf/AlgebraicGeometry/FiniteFreeStalkDegreewiseLocal.lean`.

`lem-pc-finite-free-stalk-degreewise-lift-core` isolates finite intersection and
restriction of representatives already supplied by its hypothesis. It requires
bounded supports but no freeness. Its module is
`lean/Sheaf/AlgebraicGeometry/FiniteFreeStalkDegreewiseLiftCore.lean`.
No existing statement or definition changed, so no change record is required.

## Second reading by M1

1. Compared the delivered item against the repository with diff. The existing
   declaration's signature, docstring and visibility are byte-for-byte unchanged;
   only its proof and two plain imports changed. There are no adapted existing
   modules, definitions or target statements. Verdict: pass.
2. Compiled all three modules through lcompile.py in import order. Each compiles
   cleanly. Independent scratch #print axioms checks show only propext,
   Classical.choice, Quot.sound and sorryAx, as expected for this decomposition.
   No axiom, unsafe, opaque, implemented_by, extern or hollow definition occurs.
   The only two textual sorries are the named lower theorems listed above.
   Verdict: pass as a decomposition, not an axiom-free target proof.
3. Checked both lower statements mathematically, including zero terms, rank zero,
   disjoint or reversed support intervals, and the empty finite intersection.
   Added full docstring proofs and separate matching modules/nodes. Independent
   leanfinder, loogle and grep searches found free-pullback, restriction-composition
   and germ-representation ingredients, but no matching theorem. Also inspected
   StalkInternalHomFinitePresentation (still sorry, different module-stalk interface)
   and FiniteFreeConstantMapEtaleFactorization (constant coefficients on the etale
   site); neither directly supplies the required scheme stalk-pullback equation.
   Each lower theorem is a strictly distinct part of the argument. Verdict: pass.
4. The target is reduced from the top to individual representation and finite
   intersection, then assembled by choice; no chain equations are added. Public
   imports are needed by statements; new imports are proof-only. The report now
   accounts for every old proof dependency. Read dag/units/sk-thm-picard-perfect.json:
   its realized statement and step lists are empty; no recorded unit realization
   is bypassed or changed, and the finite-matrix route is retained. Closing either
   lower theorem requires substantial comparison/naturality work, beyond a short
   second-reader repair. Verdict: pass, no module pruning.
5. Corrected the target proof steps to name both actually called lemmas. Corrected
   the common-neighbourhood node to reflect its hlocal hypothesis and comparison
   dependencies; synchronized new statements and lean records with the files.
   Sources, provenance, chapter/unit and creation records are retained, and fresh
   independent search records are appended. Verdict: pass.

Second reading changed: separated new statements into their own modules, removed
unnecessary boundedness/freeness assumptions from the corresponding new lemmas,
added complete docstring proofs, corrected DAG proof dependencies and lean records,
and replaced the inaccurate report with explicit decomposition accounting.
