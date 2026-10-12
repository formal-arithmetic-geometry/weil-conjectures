## What changed

The existing theorem `IsDiscreteValuationRing.cohenRing_mod_pow_formallySmooth` keeps its
signature byte for byte. It combines the formal-smoothness and explicit-lifting clauses.
The new Core module now proves the residue-field base case using
`RingHom.exists_lift_of_field_charP`, then performs induction on the positive exponent.
The new Explicit module proves ring-map lifting from Core using the actual canonical
ZMod-algebra structures and `Algebra.FormallySmooth.exists_lift`. Only the successor
step is split off into the new Step module. All imports used only by proofs are plain
`import`; the unused public ZMod import in Explicit was removed.

## Proved and sorry left

Hole closed relative to the repository:
`IsDiscreteValuationRing.cohenRing_mod_pow_formallySmooth` (1 of 1 original holes).
New declarations with completed proof bodies:
`IsDiscreteValuationRing.cohenRing_mod_pow_formallySmooth_core` and
`IsDiscreteValuationRing.cohenRing_mod_pow_formallySmooth_explicit`.
Hole added:
`IsDiscreteValuationRing.cohenRing_mod_pow_formallySmooth_step`, node
`lem-weil-pbc-cohen-ring-mod-pn-formally-smooth-step`.
There are no other delivered sorries. This is a decomposition, not a complete proof:
one original hole is replaced by one strictly smaller induction-step hole (net zero).
Relative to the first worker's sandbox, both Core and Explicit holes were closed and
one Step hole added. All four declarations have only propext, Classical.choice,
Quot.sound and sorryAx in their printed axiom sets.

## No longer needed

The target's old proof-only imports `Sheaf.RingTheory.ExistsLiftOfFieldCharP` and
`Sheaf.RingTheory.FormallySmoothAdic` are replaced by Core and Explicit.
ExistsLiftOfFieldCharP remains used by Core, so its module is not globally pruned.
FormallySmoothAdic is no longer needed by this item's proof.

Every old parent proof dependency absent from the new parent's direct proof_deps is:
`def-weil-pbc-formally-smooth-adic`, `def-weil-pbc-cohen-ring`,
`lem-weil-pbc-field-char-p-nilpotent-lifting`,
`lem-weil-pbc-pid-torsion-free-module-flat`,
`lem-weil-pbc-flat-module-quotient-flat`, `def-weil-pbc-flat-ring-map`, and
`lem-weil-pbc-lift-formal-smoothness-flat-square-zero`.
The Cohen-ring definition remains in the signatures and in Core's base case; the
field-lifting node remains in Core; the two flatness nodes and square-zero criterion
remain in the Step plan. The adic-definition and flat-ring-map-definition nodes are
not needed by the new argument. No claim is made that these nodes or modules have
left the entire targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The first worker split the two equivalent formulations of formal smoothness into two
unproved clauses and called them independent. Their proof plans had empty uses and
proof_deps despite referring to lower non-elementary results. The second reading
replaced that duplication with a proved base case, actual induction and a proved
conversion to arbitrary-universe ring-map lifting. The only unfinished part is the
successor step of Tag 0329. The earlier report's suggestion that field-characteristic
lifting was no longer needed is corrected above.
The first dry run in this reading failed at git fetch because the project server reset
its SSH connection. The previous report's installed-source mismatch was not reproduced.

## New nodes

`lem-weil-pbc-cohen-ring-mod-pn-formally-smooth-core`: base case from the existing
field-lifting theorem, then induction using Step; proved body, no new sorry.
`lem-weil-pbc-cohen-ring-mod-pn-formally-smooth-explicit`: actual conversion from Core
to ring-map lifting in any target universe; proved body, no new sorry.
`lem-weil-pbc-cohen-ring-mod-pn-formally-smooth-step`: only the successor implication,
assuming the preceding exponent's formal smoothness; complete docstring proof via
flatness, the power-quotient identifications and the Mathlib Tag 031L criterion.
All new nodes carry matching Lean records and actual search records. LeanSearch is
currently unavailable (HTTP internal server error); this is recorded as unavailable,
not as evidence of absence. Loogle, LeanFinder, and local rg searches were completed.
No statement or definition of the existing library changes; no change record is needed.

## Second reading by E2

1. Compared the existing module with the repository using diff and separately checked
   the theorem signature. The signature, universes, visibility and existing docstring
   are byte-for-byte unchanged. No existing definitions or target statements changed.
2. Compiled every delivered module with lcompile.py. Only the named Step theorem has
   sorry, with a complete source-based proof in its docstring and its matching node.
   There are no definitions containing sorry and no forbidden declarations or attributes.
   Scratch #print axioms checks show only the three permitted axioms plus sorryAx,
   expected from the open Step theorem and any still-open imported lower statements.
3. Checked the Step statement against Stacks Tags 0329 and 031L:
   https://stacks.math.columbia.edu/tag/0329 and https://stacks.math.columbia.edu/tag/031L.
   For n=1 its ideal is (p) in Z/p², whose square vanishes; n=0 is excluded.
   The prime hypothesis rules out p=0 and p=1. The residue quotient is a genuine
   field, and the ring-map conversion covers the zero target ring without a
   nontriviality assumption. The Step hypothesis is exactly the induction hypothesis;
   it is strictly one part of the original argument, not a renamed whole target.
   Searched other terminology with msearch.py and rg in Mathlib, upstream, and lean/Sheaf.
   The generic flat square-zero criterion exists in Mathlib, but the specific power
   quotient instantiation still needs formalization; no duplicate successor theorem found.
4. The route now uses the shortest existing field-lifting and Mathlib lifting APIs.
   Removed unused proof/public imports. The No longer needed section enumerates all
   old direct parent proof_deps and distinguishes retained lower dependencies from
   genuinely unused notions. Inspected dag/units/sk-thm-p1.json realized: this auxiliary
   node realizes no unit statement or step, and no unit route or realized field changes.
5. Parent proof_deps matches the conjunction proof. Core records the field-lifting base
   case and Step induction; Explicit records the conversion from Core; Step records
   torsion-freeness, quotient flatness and the square-zero quotient criterion. All uses
   agree with proof_deps and the nodes match their Lean declarations. Verdict: valid
   one-hole decomposition; the prescribed dry run passed compilation and preflight.

Changes made by this second reading: proved both original split clauses, replaced their
holes by one documented successor-step theorem, repaired new-node proof plans and search
records, corrected the hole accounting and pruning report, and removed unused imports.

Validation: `deliver3.py E2 Sheaf.RingTheory.CohenRingModPowFormallySmooth --no-push`
printed OK at commit e6e734e28e; review class CODEX (new nodes/modules, one named sorry).
