## What changed

Reduced `exists_affineBaseChangeTildeMateFactorization` to the calculation for the identity
representative `Q(tilde M)`, in the new module
`Sheaf.Algebra.Homology.AffineBaseChangeTildeMateIdentityFactorization`. The combining proof is
complete: it transports quasi-coherence through homology of `e.symm`, constructs the source
comparison by composing with `H.mapIso (F.mapIso e)`, applies the proved coefficient naturality
of derived base change (proved locally from the pinned adjunction), and uses the explicit representative transport equation.

Moved the existing definition `affineBaseChangeTildeRepresentativeIso`, unchanged, into the new
module `Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative` so that the identity-case
module can use it without an import cycle. Added the proved equation
`affineBaseChangeTildeRepresentativeIso_identity_hom` there. The item publicly imports this
module, preserving visibility of the definition; its proof imports the identity-case module
only. Naturality is a proved private helper for arbitrary natural transformations because importing
`Sheaf.AlgebraicGeometry.DerivedBaseChangeNaturality` creates an import cycle.

Repair of X-27336: generalized the private helper to
`mate_naturality_of_transformation`, with `e : P ⋙ L' ⟶ L ⋙ Q` instead of an
isomorphism. Its proof uses only naturality of e and the counit; it does not require an inverse.
The affine specialization applies it to `q.hom`. This is the generalization permitted by the
return, rather than another copy of the existing isomorphism theorem. No public signature,
remaining hole, import or definition body changes in this repair.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.exists_affineBaseChangeTildeMateFactorization`.
Added one strictly special-case hole:
`AlgebraicGeometry.exists_affineBaseChangeTildeMateIdentityFactorization`, node
`lem-pc-affine-base-change-tilde-mate-identity-factorization`. Thus this is a decomposition:
one original hole closed, one new hole added, net zero. The arbitrary derived object K and
its arbitrary representative isomorphism e have been eliminated from the remaining calculation.
The naturality and explicit representative transport steps are fully proved.

`AlgebraicGeometry.affineBaseChangeTildeRepresentativeIso_identity_hom` is proved, with no sorry.
There are no other sorries in the three delivered modules. No data are chosen from the new theorem.

## No longer needed

No dependency module is globally pruned: the original resolution, tensor comparison,
cohomology and derived-unit dependencies remain needed by the identity-case calculation.
The item's direct proof now uses only the identity-case node, the explicit representative node,
and the pinned derived-mate definition. The old ten direct proof dependencies
are carried by the identity-case node rather than discarded. Explicitly, the old direct dependencies transferred to the identity-case node are:
`def-pc-affine-base-change-tilde-coordinates`,
`def-pc-base-derived-tensor-cohomology-model`, `def-pc-derived-base-change-map`,
`lem-pc-affine-derived-pullback-tensor-tilde`, `lem-pc-affine-morphism-hi`,
`lem-pc-affine-tilde-pushforward-cohomology-normalization`,
`lem-pc-derived-base-change-unit-compatibility`, `lem-pc-source-module-kflat-resolution`,
`lem-sc-qcoh-acyclic-derived-pushforward-cohomology`, and
`lem-weil-pbc-tilde-pullback-base-change`. The derived-mate definition is also used directly
by the transport proof. No old dependency is dropped from the calculation's plan.

The second reader removed the redundant direct public imports of
`Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap` and
`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat` from the new representative module.
Its normalization import already supplies the definitions its construction needs.
The obsolete inverse-cancellation
helper and the invalid `True ∧` core from the earlier sandbox attempt were removed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox core merely repackaged the original target. It has been deleted.
An attempted equation for every arbitrary source cohomology isomorphism was also discarded:
changing that isomorphism can change the left side, so that statement is false.
Importing the existing coefficient-naturality module creates a cycle through affine base-change
modules, so the private proved helper now establishes naturality for arbitrary comparison natural
transformations, strictly generalizing the existing isomorphism theorem.
The import-direction check also confirms that `DerivedBaseChangeOpenUnit` reaches this item;
importing its `mate_naturality` would close a cycle. The previous private isomorphism theorem
was a word-for-word duplicate, as X-27336 correctly reported; this repair removes that duplicate.
The delivered reduction fixes the identity representative and uses a real naturality proof
for the passage to arbitrary K and e. Zero complexes and zero rings impose no special cases
on this transport argument. Unboundedness is unchanged.

## New nodes

`lem-pc-affine-base-change-tilde-mate-identity-factorization` states only the identity representative
calculation; its hypotheses contain neither an arbitrary derived coefficient object nor its
representative isomorphism. Its proof plan retains the original affine resolution and
pinned derived-unit calculation.

`def-pc-affine-base-change-tilde-representative-iso` records the existing, unchanged explicit
representative construction in its new module and its proved identity transport equation.

Change record: `coord/changes/affineBaseChangeTildeRepresentativeIso.md`.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered item with the repository using diff and checked the declaration
   slices byte for byte. The existing theorem signature is identical. The moved definition's
   entire signature and body are identical; only its blueprint docstring tag changes. The move
   has a change record, and the original module imports it publicly. The downstream query finds
   the item and OrdinaryComparison as textual users; their types and the value of the definition
   are unchanged. No target meaning, existing hypothesis, or conclusion changes. Verdict: pass.
2. Read the naturality proof, the construction of the transported source isomorphism, and the
   representative equation. The original three modules compile without warnings. The only
   source sorry is the named identity-case theorem. No forbidden declaration, hidden sorry,
   or new choice from an arbitrary existence theorem is introduced. The copied representative
   uses the already proved unit-normalized tensor comparison; its normalization determines it
   on generators. The private adjunction choices are the same pinned choices in the existing
   derived-mate definition. Axiom probes and final delivery validation are recorded below.
3. The remaining statement specializes the original one to Q(tilde M) with its identity
   representative. The arbitrary K and arbitrary e are eliminated; their transport is actually
   proved, including coefficient naturality, so this is a strict special-case decomposition,
   not a renamed application of the old hole. Checked zero complexes, zero coefficient rings,
   identity maps, and noncartesian commuting squares in the tensor and mate argument: none
   requires cancelling the coefficient map or asserting an invertible mate. The proof uses
   unbounded K-flat resolutions, without a boundedness hypothesis. Read the recorded dependency
   declarations and searched again with homology/scalar-extension/exchange terminology via
   leanfinder, loogle and grep, plus rg on lean/. No existing identity-case factorization was
   found. The existing coefficient-naturality theorem and generic mate lemma lie above this
   item in the import graph, so cannot be imported here. Expanded the remaining hole's
   docstring to state the source isomorphism, unit equation, homology factors, equality
   transports and counit cancellation explicitly. Its source and matching new node are
   present. Verdict: pass; the lower hole remains open.
4. The top proof takes the identity-case calculation, then functoriality and naturality; it
   adds no unnecessary affine or target-coordinate theorem. Removed two redundant imports
   from the moved definition module and made the list of old dependencies explicit under
   No longer needed. The old ten dependencies remain in the identity-case proof plan.
   Reviewed dag/units/sk-thm-picard-semicon.json: this item is below the unit statement and
   step realization, whose route and realized fields are untouched. No module is globally
   pruned. Verdict: pass.
5. The updated existing node changes only lean, proof, proof_deps and proof_origin. Its
   three proof steps match the Lean transport proof. The new identity-case node retains the
   affine-resolution calculation; the representative node records the copied definition and
   its proved hom-composition equation. Checked dependency unions, required new-node fields,
   declaration names and signatures. Corrected the identity-case module title and blueprint
   header, which still named the original module. Verdict: pass.

Second-reading changes: removed two redundant imports; expanded the identity-case proof
explanation; corrected its title/blueprint header; completed the dependency accounting in
this report. No Lean statement or definition body changed. One original hole is closed by
one strictly smaller hole, so the result remains a decomposition with net zero, not a closed
proof of the target. No additional hole was closed in the second reading.

Validation after the second-reading edits: all three modules compile without warnings
through lcompile.py (26.0 s, 18.2 s, 26.9 s). A scratch #print axioms check reports
only propext, Classical.choice and Quot.sound for the representative definition and
its identity-transport equation. Both factorization theorems report those same
axioms plus sorryAx, as expected from the remaining named identity-case hole.


## Second reading by F1

1. Compared every delivered existing declaration with the repository by diff and exact
   string comparison. The original factorization theorem signature is byte for byte
   identical; the representative definition's complete signature and body are identical.
   Its module move is declared in the change record and preserves its public visibility
   through the item's public import. No existing theorem, hypothesis, conclusion or
   definition value changes. Verdict: pass.
2. Read both private naturality proofs and the transport proof. The generalized helper
   uses an arbitrary natural transformation, its naturality, and counit naturality; no
   inverse is used. The specialization uses the exact choices of the pinned mate.
   The source comparison is transported by homology of F.mapIso e; the final factor
   uses the proved representative transport equation. All three files compile without
   warnings via lcompile.py (35.7 s, 23.1 s, 35.0 s including slot waits). The only
   source sorry is the named identity-case theorem. There are no forbidden declarations
   or sorries in definitions, and no data chosen from the new existence theorem.
   The existing tensor comparison is proved and unit-normalized, not an arbitrary
   witness selected from an unproved existence theorem. Verdict: pass.
3. The new hole fixes K to Q(tilde M) and e to its identity, strictly removing the
   arbitrary-object transport step. That step is genuinely proved in the item, rather
   than hidden behind a renamed theorem. Read its full docstring and node proof; checked
   the scalar-restriction and homology factors against BaseDerivedTensorCohomologyModel,
   and the pinned exchange equation against DerivedBaseChangeUnitCompatibility.
   Zero complexes, zero rings, identity maps and a noninvertible coefficient map cause
   no exception: no cancellation of that coefficient map or invertibility of the mate
   is asserted. Unbounded complexes are retained. The affine tensor calculation agrees
   with Stacks Tag 0DJ8; its commuting-square extension uses the mate construction of
   Tag 08HY and derived tensor construction of Tag 06Y6. Repeated leanfinder, loogle
   and grep searches with homology/scalar-extension/exchange terminology, and rg on
   Sheaf and WeilConjectures. No matching closed affine factorization was found.
   Mathlib's mates correspondence supports naturality, but the short direct proof
   avoids an additional import. Existing coefficient naturality is above this item
   in the import graph and cannot be imported without a cycle. Verdict: pass;
   the identity calculation remains open and is not claimed as a net proof gain.
4. The top proof follows the shortest available identity-case reduction, then naturality
   and functoriality. Imports of the new representative module supply its construction;
   the identity-case import is proof-only. SchemeDerivedBaseChangeMap and KFlat occur
   in public signatures. No additional import is needed. The ten old direct proof
   dependencies are explicitly accounted for above and remain in the lower calculation's
   plan. Reviewed dag/units/sk-thm-picard-semicon.json: its realized fields and route
   are untouched, and this transport reduction is below the unit level. Verdict: pass;
   no module is globally pruned.
5. The existing node changes only lean, proof, proof_deps and proof_origin; its three
   steps match the actual reduction. Verified proof dependency unions for all three
   nodes, mandatory new-node fields, names, module paths and verbatim signatures of
   the new declarations. The representative node records the moved definition and its
   closed identity equation. Corrected that node's copied source/proof-origin metadata
   to refer to its actual construction, and added the independent search records to
   both new nodes. Verdict: pass.

Second-reading changes in this round: corrected representative-node source metadata,
added independent Mathlib search records, and appended this review. No Lean proof,
signature, definition body or import changed. Closed zero additional holes. The delivery
closes exists_affineBaseChangeTildeMateFactorization and adds
exists_affineBaseChangeTildeMateIdentityFactorization: one-for-one decomposition, net zero.

Current axiom validation: the independent scratch #print axioms probe compiles (2.1 s).
The representative definition and identity-transport equation use only propext,
Classical.choice and Quot.sound. Both factorization theorems additionally use sorryAx,
exactly as expected from the single remaining named identity-case hole.
