## What changed

Proved `Algebra.exists_finiteEtale_artinian_residue_lift_capture` in
`Sheaf.RingTheory.ArtinianSeparableResidueLiftCapture` without changing its signature,
universes, visibility, or existing docstring. Added the proof-only import
`Mathlib.RingTheory.Unramified.LocalStructure`; all four original public imports remain.
Updated node `lem-weil-pbc-artinian-separable-residue-lift-capture` to record the actual
standard-étale polynomial route and its existing Mathlib leaf dependency.

Lift the monic minimal polynomial of b from κ(D) to D, and invert its derivative to
construct a standard étale algebra E with a D-algebra map to κ(S) carrying its generator
to b. Mathlib makes E finite over the Artinian D. Formal smoothness lifts its residue
map across the nilpotent maximal ideal of S. Localize E at the kernel of that residue
map; Artinian localization is surjective, so the local factor remains finite and étale.
Prove both maps local and verify the generator's residue directly. ULift handles the
arbitrary extra universe z before localization.

Validation: local single-file compilation passed without warnings. The source paragraph
was read at https://stacks.math.columbia.edu/tag/07FI because the cited literature file
is not present in this clone. The argument uses proved Mathlib declarations only.
Searches used msearch LeanFinder (residue capture), Loogle (`AdjoinRoot, Algebra.Etale`),
and grep (quasi-finite finiteness and Artinian localization), plus rg in both library
roots and Mathlib. The searches found no exact capture theorem but did find all the
construction tools. Edge cases need no extra assumptions: b=0 or b in κ(D) has a
separable linear minimal polynomial; local rings are nontrivial; q is prime via its
map to the field κ(S); ULift covers all u, v, z.

## Proved and sorry left

Closed the sole original hole:
`Algebra.exists_finiteEtale_artinian_residue_lift_capture`
(node `lem-weil-pbc-artinian-separable-residue-lift-capture`).
One hole closed; zero added; no remaining sorry in the delivered module.
This is a complete proof from Mathlib, not a decomposition into new holes.
No new declarations or modules are added.

## No longer needed

No original imports, modules, or named proof-dependency nodes were removed: the original
node had no named proof dependencies. No new Sheaf or WeilConjectures imports are needed.
In particular the construction does not require `HenselianFiniteEtaleEquivalence`,
`HenselianFiniteTypeProductDecomposition`, `HenselianEtaleRetraction`, or
`WeilConjectures.Mathlib.RingTheory.Etale.ResidueField`; these were investigated but never
imported, and are not claimed globally pruned. The recorded unit route is unchanged.

Removed the redundant trial proof imports `Mathlib.RingTheory.Artinian.Ring`,
`Mathlib.RingTheory.Etale.StandardEtale`, and `Mathlib.Algebra.Polynomial.Lifts`:
the retained `Mathlib.RingTheory.Unramified.LocalStructure` provides their declarations
and the essential étale-to-quasi-finite instance transitively.

## Where the brief, the DAG or earlier work was wrong

The original node contained only a prose construction step, with no named dependencies.
It can nevertheless be proved entirely using existing Mathlib results. Its mathematical
statement is correct and unchanged. Henselian factorization is unnecessary here: the
Artinian target has a nilpotent maximal ideal, so formal smoothness directly lifts the
residue map, and Artinian localization selects its finite local factor.
No interface corrections, forced adaptations, or new nodes were needed.

## Second reading by C1

1. Compared the complete delivered Lean file with the repository version using diff,
   and separately checked the declaration prefix through `:= by` byte for byte.
   Verdict: the sole existing signature, universes u/v/z, visibility, hypotheses,
   conclusion, and docstring are unchanged. The only source changes are its proof
   and one plain proof-only import. There are no definitions, extra declarations,
   interface changes, change records, or forced adaptations.

2. Compiled the delivered module through lcompile.py: clean, 2.8 seconds. Compiled
   a scratch copy with `#print axioms
   Algebra.exists_finiteEtale_artinian_residue_lift_capture`: precisely propext,
   Classical.choice, Quot.sound, with no sorryAx. Scanned the delivered source for
   sorry, axiom, unsafe, opaque, implemented_by, extern and skipped kernel checking:
   none. Verdict: a complete kernel-checked proof, one original hole closed and
   zero holes added. The chosen polynomial comes from a proved Mathlib lifting
   theorem, and FormallySmooth.lift comes from the proved exists_lift theorem
   (Smooth/Basic.lean:129–150), not an unproved existence statement. E is the
   explicit standard-étale quotient, and D' is its explicit prime localization.

3. No statements were split off, so no new docstrings or nodes require validation.
   Independently searched both Lean roots for residue capture, finite étale lift,
   and Artinian localization, and ran msearch grep for formal-smooth lifting and
   separable residue existence. Read upstream Etale/ResidueField.lean: its
   exists_etale_residueField_equiv realizes a whole finite residue-field extension
   but does not give the local map into S or capture the prescribed b; using it
   would add intermediate-field and residue-equivalence bookkeeping. The core
   and final capture theorems in Sheaf depend on this item and cannot be used.
   Verdict: no duplicate helper, relabelled hole, or shorter ready-made proof found.
   For b=0 or b in the base residue field the minimal polynomial is linear and
   its derivative remains nonzero. Separability supplies integrality even when
   K/k is not finite; no finiteness hypothesis on K was silently used.

4. Read the proof from its conclusion back to each construction. Polynomial
   lifting and derivative evaluation give P.HasMap b; the standard-étale instance
   supplies étaleness; the quasi-finite instance at Unramified/LocalStructure.lean:332
   and Module.Finite.of_quasiFinite give finiteness over Artinian D. Artinianness
   of S makes its maximal ideal nilpotent, enabling the lift. Artinian E makes
   E→D' surjective, so D' remains finite; Noetherian D supplies finite presentation
   for the localized formally étale algebra. The unit-reflection proof of g'
   uses this surjectivity and the prime-localization unit criterion. Locality of
   D→D' follows from the composite being the given local D→S map. The final
   lift_X calculation captures exactly b. ULift meets max u v z without shrinking
   any universe. All original public imports supply notions in the signature;
   the new import supplies the standard-étale construction and quasi-finite
   instance. No original proof_deps existed to prune. Read sk-thm-p1.json:
   this helper is below its realized statement and steps, all of which remain
   intact. Verdict: the route and the report's No longer needed list are sound.

5. Compared the node JSON with its repository version: only proof, proof_deps
   and proof_origin change. Read the existing Mathlib leaf
   lem-weil-pbc-standard-etale-monic-derivative and its declarations
   StandardEtalePair.Ring, lift, lift_X, homEquiv, and étale instance: they supply
   exactly the construction cited in step 2. The other steps identify the actual
   proved Mathlib declarations used in the Lean; their applications and routine
   transport calculations are elementary at this level. proof_deps is precisely
   the union of the uses lists. Read Stacks Tag 07FI online: its algebraic-residue
   paragraph constructs a finite étale extension and factors it into the
   henselian Artinian target, matching the capture goal. The direct nilpotent
   lifting proof is an allowed shorter route below the unit. Verdict: the node
   matches the unchanged Lean statement and the actual proof.

Changes by the second reader: appended this independent review only. No proof,
import, statement, definition, or node repair was necessary.
