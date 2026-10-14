## What changed

Proved `AlgebraicGeometry.Scheme.affine_torsor_single_stabilizer_component_section`
without changing its statement. The proof establishes reconstruction of a section from
its label on the connected puncture, applies the exact stabilizer equation to establish
invariance, and uses affine invariant-ring descent. The base equation follows from
uniqueness, not an additional assumption.

Added the fully proved public theorem
`AlgebraicGeometry.Scheme.affine_invariant_basic_open_descent` in
`Sheaf.AlgebraicGeometry.Morphisms.AffineInvariantBasicOpenDescent`. Its explicit
localization calculation works for arbitrary families of algebra endomorphisms and
arbitrary subgroups, with no finiteness, flatness, etaleness, or action laws.
The ring map is constructed by preimages under a proved injective localization map;
every preimage is uniquely determined and no data are chosen from an unproved theorem.

Added a proof-only import of that module and proved private reconstruction helpers
(the existing reconstruction declaration in SplitAction is private). The two existing
open-component assembly proofs stay unchanged. The section statement retains unused
Galois hypotheses, so its unused-variable linter is locally disabled with an explanatory
comment; no signature or visibility changes. Updated the section node's proof and
proof dependencies to the actual argument.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.affine_torsor_single_stabilizer_component_section`
(node `lem-sbc-affine-torsor-single-stabilizer-component-section`).
Added zero holes. No `sorry` remains in either delivered module.
`affine_torsor_single_stabilizer_component_open` and
`affine_torsor_single_stabilizer_component` were already proved and their proofs
are unchanged. The imported openness criterion remains another item's existing hole;
this delivery neither adds nor relocates it.

The generic descent theorem compiles cleanly in approximately ten seconds.
The section proof compiles cleanly in approximately three seconds, and `#print axioms`
reports exactly `propext`, `Classical.choice`, and `Quot.sound` for it.
Both complete delivered modules compile cleanly, and
`deliver3.py N3 Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSingleStabilizerComponent
--no-push` printed `OK`: compilation, declaration-axiom probes, and stage-3 preflight
passed, with only the independent second reading pending. Nothing was pushed.
Initial attempts waited for the newly landed openness module to reach the shared
green cache; after publication the same delivered sources passed. No imported source
was duplicated, changed, or compiled around that restriction. The standalone section
axiom audit used a scratch file that has been removed from the delivered Lean sources.

## No longer needed

No existing import, DAG node, or module is removed. All existing public imports are
retained as part of the interface, and the openness criterion is still required by the
two assembly theorems. The section proof no longer needs the proposed Galois-category
classification route: no Galois equivalence, torsor quotient construction, or additional
localization-invariants theorem is imported. The finite map to D(g) is used only to
make Y affine. The new descent module's unused explicit Localization.Away.Basic import
was removed, since AffineScheme already supplies that API.

## Where the brief, the DAG or earlier work was wrong

The section node's proposed proof is longer than necessary. Connectedness gives
stabilizer invariance directly, and the affine Hom correspondence proves descent.
The Galois rotation and etaleness assumptions are unnecessary for this factorization,
but the public statement is unchanged. The repaired historical STATEMENT-DISPUTED
comment refers to the old arbitrary-component statement, not the current existence
statement; it is preserved without modifying the existing interface or docstring.

Edge cases: K trivial gives F=C and the factorization is the identity on the basic
open. The ring calculation permits infinite K because the same denominator is fixed
by every endomorphism. With d=0 there is no x:Fin 0, so the section theorem has no
instance. A zero h is excluded by the existing nonzero hypothesis; no assumption
that its image is a unit in H is used. No normality, characteristic or group-order
invertibility assumption is introduced. The unit's recorded route is unchanged.

## New nodes

`lem-sbc-affine-invariant-basic-open-descent` records the unique factorization of
an invariant morphism from D(h_C) through D(h_F), for an affine target. Its module
contains a complete proof, including localization injectivity, invariant numerators,
construction of the descended ring map, scheme-map compatibility and uniqueness.
The node inherits the original chapter and unit and has no new sorry or change record.

## Second reading by N3

1. Compared the delivered section module with the repository version. The existing theorem
   signature is byte-for-byte unchanged; the new descent theorem is in its own module and
   has a matching DAG node. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. There are no errors, no
   `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definitions, and
   no `sorry` remains in either delivered module. The localization preimages are uniquely
   determined by the proved injectivity of the localization map. Verdict: pass.
3. Checked the new descent statement against the localization construction and edge cases
   (trivial subgroup, arbitrary subgroup, and infinite subgroup). It states exactly the
   needed unique factorization and introduces no finiteness or action hypotheses. Searches
   found no duplicate library or Mathlib declaration. Verdict: pass.
4. Read the proof from the target downward. It uses the existing split-label laws, the
   proved reconstruction helper, and affine localization descent; the unit route remains
   recorded and no old proof dependency is incorrectly removed. The new module's
   `AffineScheme` import is proof-only and is now private. Verdict: pass.
5. Checked both delivered DAG records against the Lean declarations, including proof
   dependencies, origins, source, and the new node's complete proof plan. Verdict: pass.

Changed the new descent module's `Mathlib.AlgebraicGeometry.AffineScheme` import from
public to proof-only, and added this second-reading record. No theorem statement or
existing declaration was changed.
