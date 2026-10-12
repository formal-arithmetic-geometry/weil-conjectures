## What changed

Proved `AlgebraicGeometry.Etale.geometricFibreExchange_germs` in
`Sheaf.AlgebraicGeometry.GeometricFibreExchangeGerms`, without changing any existing
signature, visibility, universe, definition, or definition body.

Added two fully proved private helpers: `terminalGerm_isIso` establishes bijectivity
of the identity-point terminal germ directly, and `sourceStalkIso_germ` proves the
formula for the specific canonical source comparison. The latter adapts the proved
argument in `Sheaf.Paper.InverseImageStalkGerm` to module coefficients; it does not
choose an arbitrary comparison. Constructed the target isomorphism from the inverse
terminal germ and the unique terminal-object comparison. Germ extensionality,
`unit_map_baseChangeMap_app`, and explicit iterated-pullback projection calculations
then prove the exchange equality from the assumed formula for Theta.

Updated the existing node's proof, proof dependencies, and proof origin to describe
this route. The unit record `sk-lem-universal-datum` has no realized node statements
or steps that this reduction bypasses. The original public imports remain.

Validation: the item compiles with the prescribed `lcompile.py`, no warnings,
no increased heartbeat limit, and no local sorry. No new module or adaptation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.geometricFibreExchange_germs`
(node `lem-sbc-geometric-fibre-exchange-germs`).

Holes closed: 1. Holes added: 0. Split off: 0. No sorry remains in this module
or in any new declaration of this delivery. Both private helpers are fully proved.
This is a proof, not a decomposition into new admitted statements.

## No longer needed

Removed proof-only import `Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`.
The node `lem-weil-pbc-strictly-henselian-sections-stalk` is no longer a proof
dependency of this item. Its general strictly henselian section construction,
affine-localization argument, and Olivier theorem are not needed on this route:
at the identity geometric point the marked morphism itself supplies the section.
This is pruning from this item's route, not a claim that these modules are unused
by every other target branch.

No other original imports or proof-dependency nodes were removed. The two source
modules `WeilConjectures.SixFunctors.BaseChange.Square` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk` remain necessary for the
existing interface and proof. An experimental import of
`Mathlib.Algebra.Category.ModuleCat.FilteredColimits` was also removed before
completion: its instances already arrive through the retained public imports.
No new proof dependency on `Sheaf.Paper.InverseImageStalkGerm` is introduced;
the module-coefficient germ formula is proved from the existing source APIs.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The planned invocation of the
general strictly henselian theorem was unnecessary and had abelian-group rather
than module coefficients. Its identity-point specialization has a direct proof,
so no coefficient-forgetting bridge or new admitted theorem is needed.

The canonical source comparison must be checked itself, rather than merely
obtaining some isomorphism from an existential stalk theorem. The private germ
calculation verifies exactly the comparison already defined in this module.

## Second reading by N1

1. PASS: compared the delivered module and node with the repository using `diff`.
   All four existing declaration signatures, visibility and docstrings are byte
   for byte unchanged; the three existing definition bodies are unchanged.
   Only two proved private helpers, the target proof, and removal of one private
   proof import affect the Lean file. No interface change or change record is needed.
2. PASS: independently compiled the complete module using `lcompile.py`, without
   warnings. No local `sorry`, axiom, unsafe declaration, opaque declaration,
   implementation override or foreign code remains. A scratch copy checks
   `#print axioms` for both helpers, all three definitions and the target theorem;
   every result contains only `propext`, `Classical.choice` and `Quot.sound`.
   The terminal comparison is inverted only after proving its bijectivity;
   the other comparison is the unique terminal-object isomorphism. No arbitrary
   witness from an admitted existence theorem supplies any data.
3. PASS: no statements were split off and no new holes or public statements were
   added. Read both private helper proofs: the marked point gives an actual
   section over the identity point, and the source formula checks the specified
   canonical isomorphism itself. These arguments also cover zero sections and
   zero coefficient rings; they do not require the exchange or Theta invertible.
   Searched the Point APIs in Mathlib and the Sheaf/WeilConjectures sources using
   terminal/germ/isIso terminology. No existing module-coefficient theorem
   replaces either helper; the abelian-group inverse-image germ theorem supplies
   the same underlying calculation, as acknowledged in the report.
4. PASS: the proof follows germs from the target downward, uses the existing
   exchange-unit identity and stalk comparison, and finishes by the actual
   two-projection calculation for the defined lift. The two retained public
   imports are needed by existing signatures and definitions. The removed
   StrictlyHenselianSectionsStalk import and its node are fully listed in
   `## No longer needed`; comparison of old and new proof dependencies shows no
   other omitted dependency. Read `dag/units/sk-lem-universal-datum.json`: its
   realized statement and step lists are empty, so this reduction bypasses no
   required realized unit node.
5. PASS: compared the node records. Only `proof`, `proof_deps` and `proof_origin`
   change, and they accurately describe the terminal germ bijectivity, explicit
   target comparison, canonical source germ formula, exchange-unit identity and
   iterated-pullback projection calculation. The dependency list is exactly the
   union of the recorded steps' uses. The statement and Lean record are unchanged;
   there are no new nodes requiring additional records.

Second reading changed only this report by adding the independent review.
No proof repair was needed. Closed holes: `AlgebraicGeometry.Etale.geometricFibreExchange_germs`
(1); added holes: none (0); split off: none (0).
