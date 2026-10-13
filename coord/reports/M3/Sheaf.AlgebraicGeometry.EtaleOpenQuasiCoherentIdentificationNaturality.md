## What changed

Proved `AlgebraicGeometry.etaleOpenTensorSectionsComponent_naturality` in
`Sheaf.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentificationNaturality`.
The existing public signatures, visibility, and component-isomorphism definition
are unchanged. Added only proof imports of Mathlib's `CompositionIso` and
`Sheaf.AlgebraicGeometry.EtaleTensorSectionsMapNaturality`.

Five proved private helpers specialize normalized left-adjoint associativity,
cancel its comparison isomorphisms, evaluate unit naturality on global sections,
and handle the triangle transports by equality elimination. The public proof
combines this triangle compatibility with the existing coefficient-module
naturality theorem. Updated the existing node's proof, proof dependencies, and
proof origin to record these actual steps.

The direct source pages read were Stacks 03DR, equation
`descent-equation-quasi-coherent-presheaf`, and 03DU, item 4. The local Stacks
TeX checkout is absent on this machine. Read the pinned Mathlib
`Adjunction/CompositionIso.lean` and `AlgebraicGeometry/Modules/Sheaf.lean`.
The three search modes run through msearch were leanfinder, loogle, and grep;
the useful match was `Adjunction.leftAdjointCompIso_assoc`. Repository searches
found the already-proved coefficient-module naturality theorem.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.etaleOpenTensorSectionsComponent_naturality`
(node `lem-weil-pbc-etale-open-qcoherent-identification-naturality`).
All five private helper theorems are proved. No `sorry` remains in the delivered
module; no hole was added or split off. This is a proof, not a decomposition.

Single-file compilation through lcompile.py passes without warnings.
The unchanged direct importer also compiles against the sandbox overlay. The
triangle calculation applies to arbitrary morphisms and modules: it assumes
neither nonemptiness nor quasi-coherence. Identities, empty schemes, and zero
modules are covered by the same unit and isomorphism equations.

## No longer needed

None. Both original public imports are retained; each added proof import is
used. All original proof dependencies remain involved in the construction or
proof, with the existing coefficient-module naturality node added. No unit
statement or realized step is bypassed, and no module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was needed. The DAG's single large
step was implemented through explicit proved private helpers. Scheme composition
is definitionally associative here, but tensor functor-object presentations
needed `convert ... <;> rfl` or `erw` when specializing the generic coherence
calculation. No definitions were changed to address elaboration. The interface scanner
requires a scope-command change record despite unchanged public signatures:
`coord/changes/etale-open-naturality-proof-scope.md` records those commands
and their users. No module is adapted.


## Second reading by M3

1. **Interface — pass.** Read the repository and sandbox modules in full and
   compared them with `diff -u`. Both existing declaration signatures and the
   complete body of `etaleOpenTensorSectionsComponentIso` are byte-for-byte
   unchanged, as are public imports and visibility. The added imports are plain
   proof imports. The scope commands have the declared change record; they do
   not change any mathematical object. There are no adapted modules.
2. **Proof — pass.** Independently compiled the delivered module through
   `lcompile.py`, cleanly (19.5 seconds). Compiled a scratch copy with
   `#print axioms` for both public declarations: each uses only `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. There is no `sorry`,
   axiom declaration, unsafe code, opaque declaration, extern, or implemented_by
   in the module. All five helpers are proved. The selected adjunction is for
   the already constructed tensor functor and has its unit specified sectionwise
   by `exists_tensorPullbackAdjunction`; no arbitrary module or section is
   selected from an unproved mere-existence statement.
3. **Split statements — pass, none.** No new public statement, new node, or
   split-off hole is delivered. Checked the five private intermediate equations:
   pushforward coherence is sectionwise identity; cancellation of comparison
   isomorphisms gives the inverse equation; unit naturality evaluated at the
   whole source gives the section equation; substitution of the triangle
   equality removes both transports. Each applies to arbitrary schemes and
   modules, so identities, empty schemes, and zero modules add no hypotheses.
   Repository searches for composition associativity, restriction compatibility,
   and unit naturality found no reusable public replacement. The matching
   private unit calculation in `EtaleTensorSectionsMapNaturality` is inaccessible.
   `EtaleTensorOpenSectionsNaturality` instead concerns open objects and cannot
   replace compatibility for arbitrary etale objects in this theorem.
4. **Route and pruning — pass.** Read Mathlib's
   `Adjunction.leftAdjointCompIso_assoc` and the imported tensor definitions and
   coefficient-module naturality proof. The generic Mathlib associativity lemma
   is used directly; the remaining proof consists of cancellation, unit
   naturality, equality elimination, and the existing coefficient theorem.
   All four imports are used: EtaleTensorSections supplies the prescribed
   constructions, Tilde supplies the open-restriction adjunction, CompositionIso
   supplies associativity, and MapNaturality supplies the final square. No old
   proof dependency is removed, so `No longer needed: None` is complete.
   Read `dag/units/sk-prop-cd.json`: the unchanged item remains the comparison
   supporting the quasi-coherent descent branch of its Artin-Schreier argument;
   no realized unit statement or step is bypassed or changed.
5. **Node agreement — pass.** JSON comparison found changes only to `proof`,
   `proof_deps`, and `proof_origin`. The dependencies are exactly the union of
   the steps' uses, and each resolves to the imported declaration or recorded
   Mathlib match. The four steps describe the five helpers and the public proof.
   Matched the node's open immersion j, arbitrary module F, etale objects v,w,
   triangle g, specified comparison components, and execution-order equality
   to the unchanged Lean signature and definition. In particular, there is no
   quasi-coherence assumption. Independently read Stacks
   [03DR](https://stacks.math.columbia.edu/tag/03DR) and
   [03DU](https://stacks.math.columbia.edu/tag/03DU), item 4, for the construction.

Second reading changed only this report by adding the independent checks above.
No mathematical, proof, import, or node repair was necessary. One original hole
is closed, zero holes are added, and zero statements are split off.
