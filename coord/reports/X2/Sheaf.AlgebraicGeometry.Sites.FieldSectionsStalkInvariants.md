## What changed

Replaced the single sorry in `AlgebraicGeometry.Scheme.fieldSections_stalkInvariants`
with a complete Lean proof from one strictly smaller remaining statement.
The existing theorem signature and visibility are unchanged, checked with the delivery parser.

Constructed the canonical finite-field lifts and the actual stalk action. The action uses
`Point.presheafFiberDesc` on changed lifts. Extension to Omega is obtained from the already
proved `exists_algEquiv_extending_separableClosure`; uniqueness follows from Mathlib's
purely inseparable extension API. Identity and multiplication are proved on colimit germs.
No data is chosen from an unproved existence statement.

Proved finite-field germ injectivity using `toPresheafFiber_eq_iff'`, a singleton etale
cover, and `Presieve.isSeparatedFor_singleton`. Proved that section germs are invariant,
embedding compatibility, both naturality clauses, and independence of the extending
Galois automorphism. The independence proof represents a fixed element by a section,
then applies embedding compatibility twice, rather than separately proving conjugation.

Added `Sheaf.AlgebraicGeometry.Sites.FieldInvariantGermRepresentative` for the sole
remaining surjectivity step. Its theorem takes an action already characterized on germs
and asks only for a section representing one invariant element. It neither produces an
action nor claims injectivity or any naturality. Its source is Stacks Tag 04JM's direct
proof over L. Tags [04JM](https://stacks.math.columbia.edu/tag/04JM) and
[03QW](https://stacks.math.columbia.edu/tag/03QW) were read online because this clone has
only the literature indexes, not the Stacks source checkout.

Added proof-only imports of `Mathlib.FieldTheory.PurelyInseparable.Basic`,
`Sheaf.FieldTheory.GaloisAutomorphismExtension`, and the new module to the item.
All existing public imports are preserved. The theorem's old nested nondependent proof
binder names trigger the unused-variable syntax linter once the sorry is removed;
`set_option linter.unusedVariables false in` is scoped to that theorem alone, preserving
its exact signature. Helpers and the new module compile with their linters enabled.

Both delivered modules compile together cleanly using lcompile.py. The unit
`sk-prop-h2` has no realized statement or step bound to this node; its Kummer route is
unchanged. Only the node-level implementation changed.

## Proved and sorry left

Closed the original direct hole:
`AlgebraicGeometry.Scheme.fieldSections_stalkInvariants`
(node `lem-exc-field-sections-stalk-invariants`). No sorry remains in the item's module.
Its action construction, action laws, lift-change characterization, injectivity,
section invariance, embedding compatibility, choice-independence, and sheaf naturality
are implemented in Lean.

Added one direct hole:
`AlgebraicGeometry.Scheme.exists_fieldSection_of_invariant_germ`
(node `lem-exc-field-invariant-germ-representative`), whose entire proof is `:= by sorry`
in its own new module. This is a decomposition: one upper hole closed, one strictly
smaller lower hole added; net direct holes zero. The final theorem still depends on
this hole, so this is not a sorry-free proof of the mathematical theorem.

The new statement was checked on L = K, L the bottom intermediate field, separably
closed K (trivial finite separable extensions), an empty sheaf/stalk (no m can occur),
and positive characteristic. No perfectness is assumed: purely inseparable uniqueness
works in every characteristic. For arbitrary L, using normal closure inside Ks
preserves the specified embeddings needed for the germ, rather than merely giving an
abstract receiving field.

## No longer needed

Removed these direct proof imports from the item:
`Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`,
`Sheaf.AlgebraicGeometry.Sites.FiniteGaloisSectionsDescent`, and
`Sheaf.FieldTheory.FiniteGaloisReceivingSeparableExtensions`.
The first two remain dependencies of the new surjectivity item and are not claimed
as globally pruned.

The route no longer uses
`lem-weil-pbc-finite-galois-receiving-separable-extensions` or its module
`Sheaf.FieldTheory.FiniteGaloisReceivingSeparableExtensions`.
The new surjectivity plan instead constructs a normal closure in the specified Ks
using the existing Mathlib leaf `lem-weil-pbc-finite-set-in-finite-galois-subextension`
(`FiniteGaloisIntermediateField.adjoin` and `subset_adjoin`).

`lem-galois-yoneda-hom-bijection` is also no longer needed on this route:
Mathlib's point-colimit identities directly prove both kinds of naturality.
The old etale-covering-composition, finite Galois descent, and etale fibre nodes
remain below the new surjectivity node. Cofiltered neighbourhoods, geometric stalks,
and the sheaf condition remain used by the actual injectivity/action proofs.
No claim is made that another target's independent uses of these nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No existing statement was changed or disputed. The planned Yoneda step was unnecessary:
`toPresheafFiber_w_apply` and `toPresheafFiber_naturality_apply` give the needed formulas.
The original plan also left the actual construction of the action implicit. The
algebraicity hypothesis allows a direct construction with unique extensions to Omega.

For the remaining field enlargement step, the receiving-field theorem gives abstract
embeddings, whereas the stalk formula requires the chosen embeddings into Ks. The
normal-closure construction inside Ks avoids that interface mismatch. This refinement
is recorded in the new node's proof; the old receiving-field theorem is not adapted.
No forced adaptations or interface changes to existing modules are needed.

## New nodes

`lem-exc-field-invariant-germ-representative`, at
`dag/nodes/sec-curve-estimates/lem-exc-field-invariant-germ-representative.json`, is the
surjectivity part of step 2 of the original node's proof. Its single new module is
`lean/Sheaf/AlgebraicGeometry/Sites/FieldInvariantGermRepresentative.lean`. It carries a
self-contained statement, source, five proof steps, matching signature, and three
kinds of search. LeanSearch was unavailable; LeanFinder and source grep found no
independent theorem. A blueprint search found no separate node for this step.
The parent node's proof and proof_deps now match the implemented combination.
There are no change records because no existing public interface was changed.

## Second reading by X2

1. I compared the delivered `FieldSectionsStalkInvariants.lean` with the repository version. The existing theorem signature and all declaration statements are unchanged; only proof-only imports, private helpers, and the proof body differ. Verdict: pass.
2. I compiled both delivered modules with `lcompile.py --all`. Compilation succeeds with no errors. The parent has no `sorry`; the sole remaining `sorry` is the named theorem `exists_fieldSection_of_invariant_germ` in its own module, with a matching split node. No forbidden declarations or hollow definitions were found. Verdict: pass.
3. The split theorem is a genuine surjectivity statement, strictly smaller than the parent: it assumes the action and its germ characterization and concludes only existence of one representing section. Its docstring gives the Stacks source and a complete proof route, and its node records the same signature and dependencies. Verdict: pass.
4. The proof follows the shortest available route below the unit: explicit lifts and stalk action, Mathlib purely inseparable uniqueness, and direct stalk identities. Removed imports and no-longer-needed dependencies are recorded above; no additional pruning was found. Verdict: pass.
5. The parent node's proof and proof dependencies match the implemented helpers and split theorem. The unit `sk-prop-h2` has no realized step attached to this node, so its route is unchanged. Verdict: pass.

I changed only this second-reading report section; no Lean statements or proofs required repair.
