## What changed

Proved `RingHom.essFiniteType_of_artinian_local_residue` in
`Sheaf.RingTheory.ArtinianLocalEssentiallyFiniteTypeResidue`, with its signature
and all public imports unchanged. Added the proof-only import
`Mathlib.RingTheory.HopkinsLevitzki`. The second reader removed the redundant
`Mathlib.RingTheory.LocalRing.ResidueField.Basic` proof import.

The proof follows Stacks Tag 07DT (3), converse direction: lift a finite set of
essential residue generators, form their generated subalgebra, localize at its
elements that are units in S, prove surjectivity onto the residue field, apply
Hopkins–Levitzki, and compose essentially finite type algebras. Using Mathlib's
fraction criterion avoids explicit polynomial presentations, prime ideals and
prime residue fields. Updated the item's node proof, proof_deps and proof_origin
to describe the actual Lean argument. No definitions or statements changed.
The item is not a statement or step in `sk-thm-p1.realized`; that unit's route stays.

Validation: single-file compilation without warnings. Explicit `#print axioms`
checks the theorem; delivery dry run performs the final compile and preflight.

## Proved and sorry left

Closed the original hole in
`RingHom.essFiniteType_of_artinian_local_residue`
(node `lem-weil-pbc-artinian-local-essentially-finite-type-residue`).
One hole closed; zero holes added; no sorry remains anywhere in this delivery.
This is a complete proof from proved Mathlib results, not a decomposition.
Its axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed `def-weil-pbc-localization-at-prime` from this node's proof_deps.
The proof does not use `Localization.AtPrime`, `Ideal.ResidueField`, or
`Ideal.Fiber`; no explicit import of
`Mathlib.RingTheory.Localization.AtPrime.Basic` is needed. It localizes the
concrete submonoid of units instead, which is the same complement of the
contracted maximal ideal. This prunes that dependency from this proof only;
other users of the node are unaffected.

No baseline imports were removed: all three public imports describe the statement.
Removed the exploratory proof import `Mathlib.RingTheory.Localization.Basic`
after verifying that the final file compiles without it. The second reader also removed the redundant proof import
`Mathlib.RingTheory.LocalRing.ResidueField.Basic`; deleting it still compiles,
whereas deleting HopkinsLevitzki fails at `finite_of_isArtinian`. All remaining DAG
proof dependencies are used, through their proved Mathlib realizations.
No Sheaf or WeilConjectures proof dependency modules are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The DAG's explicit prime and
polynomial presentation are unnecessary for formalization: the finite-set
fraction criterion and localization at the unit preimage implement the same
argument directly. The local Stacks source checkout is absent on this machine;
the statement and proof were checked at
[Stacks Tag 07DT](https://stacks.math.columbia.edu/tag/07DT).


## Second reading by Q3

1. **Unchanged interface: pass.** Compared the only delivered module with the
   repository version. The sole theorem's signature is byte for byte unchanged:
   arbitrary commutative rings R and S and ring map f, Artinian and local S,
   essentially finite type composite R -> S -> S/m, conclusion f.EssFiniteType.
   No hypotheses were added or conclusions weakened. There are no definitions,
   new declarations, adaptations, or change records. All public imports remain.
2. **Proof and axioms: pass.** Compiled the delivered theorem locally without
   errors or warnings. Compiled a scratch copy with `#print axioms` for
   `RingHom.essFiniteType_of_artinian_local_residue`: only `propext`,
   `Classical.choice`, `Quot.sound`. Scanned for sorry and forbidden declarations:
   none. The lift uses the proved residue surjection, not an unproved existence
   theorem. A, M, C and g are actual constructions; htower explicitly identifies
   the composite algebra map with f. Surjectivity of C -> S/m supplies precisely
   Module.Finite C (S/J(S)), and the Artinian S instance supplies the remaining
   Hopkins–Levitzki hypotheses.
3. **Split statements: pass, none.** No new theorem or hole was split off.
   The proof works for field S, for zero residue generators, and for arbitrary
   noninjective f; no injection of R or chosen coefficient field is assumed.
   The zero ring cannot satisfy IsLocalRing S in Mathlib. Reviewed the finite
   fraction criterion and the Artinian finiteness theorem in Mathlib source.
4. **Shortest route and pruning: pass after import repair.** Repeated searches
   using different wording with msearch grep and Loogle; no theorem giving this
   conclusion was found (Loogle's single hit assumes essentially finite type).
   LeanFinder was unavailable, recorded as such. Searched the repository's Sheaf
   and WeilConjectures ring-theory files as well. Checked the source argument in
   [Stacks Tag 07DT](https://stacks.math.columbia.edu/tag/07DT), part (3).
   This uses proved Mathlib leaves, with no remaining Sheaf proof dependencies.
   The only removed old proof dependency is
   def-weil-pbc-localization-at-prime, correctly named above. The item's node is
   not in sk-thm-p1.realized; its localization/generation argument changes no
   statement or step of that unit. Both proof-only imports were tested by
   deletion: HopkinsLevitzki is necessary, ResidueField.Basic is redundant.
5. **DAG agreement: pass.** Compared the node JSON against the repository:
   only proof, proof_deps and proof_origin differ. Each retained dependency has
   its recorded Mathlib realization used in the proof, and proof_deps equals
   the union of the proof steps' uses. The four steps describe lifted generators,
   the explicit localization map and residue surjectivity, Artinian module
   finiteness, and composition, exactly as in Lean. No new node is required.

Changes by the second reader: removed the redundant proof-only import
Mathlib.RingTheory.LocalRing.ResidueField.Basic; restored the original theorem
docstring (the full proof explanation remains in this report and the node);
corrected the import description above. The proof body is unchanged.
