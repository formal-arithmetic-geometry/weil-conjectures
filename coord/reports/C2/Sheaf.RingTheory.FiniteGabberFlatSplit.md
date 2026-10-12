## What changed

Proved `Algebra.exists_flat_split_gabber_neighbourhood` without changing its signature
or public imports. Added proof imports for the existing idempotent lifting theorem,
the new proved localization theorem, integral finite algebras, complementary
idempotents, and étale flatness.

Added `Sheaf.RingTheory.FiniteTensorFactorLocalization`, proving
`Algebra.exists_flat_tensor_factor_localization`. Nakayama gives a scalar g congruent
to 1 modulo the ideal whose multiplication lands in the scalar image. Localization
at g preserves the quotient and is flat. A quotient tensor map and induction on
tensors prove scalar surjectivity. The private quotient localization helper is
adapted from the proved helper of `EtaleMakeTensorPairCoprime` and proved here for
any localization at g.

The main proof checks scalar compatibility and residue first-coordinate
surjectivity, composes flat maps and quotient equivalences, constructs the two
complementary principal ideals, proves their intersection is zero, and lifts the
first-factor coefficient from the extended ideal. The unit route is unchanged.

## Proved and sorry left

Closed the one original hole:
`Algebra.exists_flat_split_gabber_neighbourhood`
(node `lem-weil-pbc-gabber-flat-split-neighbourhood`).

Also proved `Algebra.exists_flat_tensor_factor_localization`
(node `lem-weil-pbc-finite-tensor-factor-localization`) and its private helper
`Algebra.quotient_localization_bijective`.

No sorry remains in either delivered module; no hole was added or split off.
The existing idempotent-lifting theorem remains an upstream dependency; this
report claims closure of the item's hole, not elimination of all upstream holes.
Both delivered modules compile together without warnings using lcompile.py.

## No longer needed

No module was pruned and no existing import was removed. The old direct nodes
`lem-weil-pbc-nakayama-one-plus-ideal-annihilator` and
`lem-weil-pbc-localization-flat` are no longer direct proof dependencies of the
main node: both remain used through the new proved localization node. The actual factor rings
need not be named: the proof uses the complementary principal ideals and their
quotients directly, keeping the same idempotent splitting argument.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The initial module had no proof imports
although its node named the planned dependencies. The local literature tree has
no more-algebra.tex; the source proof was read at
https://stacks.math.columbia.edu/tag/0EM0. LeanSearch returned Internal Server Error;
that search is recorded as unavailable, without a mathematical verdict. Loogle,
LeanFinder, Mathlib source searches, project searches, and blueprint searches ran.

The ancestor utility returns no blueprint ancestor for this node because its old
blueprint.from is a string. The new node records the original finite Gabber
polynomial ancestor found in the upstream tensor-coefficient node's structured
blueprint record. No existing blueprint field was changed.

## New nodes

`lem-weil-pbc-finite-tensor-factor-localization`, in
`dag/nodes/sec-proper-base-change/`, records the already proved generic Nakayama
localization step. Its statement does not need an idempotent: finite generation
of the quotient factor suffices. Edge cases checked in the argument: zero factor
(all elements already scalar), unit ideal (localization at zero permitted), zero
base ring, and arbitrary e. No Jacobson or nontriviality hypothesis is used.
The construction chooses the localization of the proved Nakayama scalar; no data
is taken from an unproved existence statement. No change record or forced
adaptation is needed: all existing signatures and visibility are preserved.

## Second reading by C2

1. **Interfaces: pass.** Diffed the existing module against the repository and
   checked its theorem signature byte for byte. Only its proof and plain proof
   imports changed; existing public imports, visibility, universes, hypotheses,
   conclusion, and docstring are unchanged. The only existing node fields changed
   are `proof`, `proof_deps`, and `proof_origin`. There is no interface change or
   forced adaptation requiring a change record.
2. **Kernel proof: pass.** Independently compiled both delivered modules in import
   order with lcompile.py, with no warnings or errors. Scratch-copy `#print axioms`
   checks for `Algebra.exists_flat_split_gabber_neighbourhood`,
   `Algebra.exists_flat_tensor_factor_localization`, and the private
   `Algebra.quotient_localization_bijective` report exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Neither module has a
   sorry, forbidden declaration mechanism, or hollow definition. The localization
   is explicitly constructed; all existential choices in this proof come from
   proved statements, including the idempotent lift's full dependency closure.
3. **New statements: pass.** No statement was split off with sorry. The new proved
   tensor-factor lemma is strictly the Nakayama/localization part of the argument,
   not a renamed whole item. Checked the scalar-range argument, quotient inverse,
   tensor-map relation, and tensor induction. For J=top localization at zero is
   valid; for a zero factor scalar surjectivity is immediate; zero base rings and
   arbitrary e require no extra assumptions. Its full docstring proof and node
   agree. Repeated LeanFinder search with the words "finite module cokernel scalar
   inclusion killed by element congruent one localization surjective": finite
   presentation and local-surjectivity tools do not replace this theorem. Loogle
   `IsLocalization, Ideal.quotientMap` finds a maximal-ideal surjectivity theorem,
   which requires hypotheses absent here. Project/Mathlib rg searches found the
   already reported private helper in EtaleMakeTensorPairCoprime, not a reusable
   public theorem of this type.
4. **Route and pruning: pass after report correction.** Read the Stacks 0EM0 proof
   and `dag/units/sk-thm-p1.json`, including `realized`. The proof retains the
   idempotent lift, finite first-factor Nakayama step, localization, and scalar
   ideal lifting. It bypasses no realized unit step. All added main-module imports
   are proof-only. New-module public imports support its signature; Nakayama,
   finite tensor base change, and localization imports are private proof imports.
   No shorter exact library result was found. No module becomes unneeded.
5. **Nodes: pass.** Checked both Lean statements against their node Lean records,
   and each proof step against the written proof. The existing dependencies for
   integrality, idempotent lifting, etale flatness, and flat composition are used;
   Nakayama and localization flatness are now mediated by the new node. New-node
   provenance, source, searches, creation record, chapter, unit, blueprint ancestry,
   and Lean record are present. No unit or existing statement field changed.

Second reading changed only this report: explicitly listed the two old direct
proof dependencies now used through the localization node and added this review.
No Lean proof repair was needed. Independently verified holes closed: the one
original item hole; holes added: zero. The new localization theorem and private
helper are fully proved, so this is a proof rather than a decomposition.
