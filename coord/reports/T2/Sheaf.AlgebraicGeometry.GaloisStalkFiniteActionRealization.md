## What changed

Proved `AlgebraicGeometry.Scheme.galoisStalkActionFunctor_finite_mem_essImage`
with its original signature. A proved private helper constructs the comparison for
the fixed sheafification of the lifted representable presheaf. Its identity-germ
map is proved bijective directly from the stalk colimit: evaluation gives a left
inverse and every section germ becomes an identity germ. The sheafification unit
induces a bijection on stalks. Existing proved source results then identify
Omega-points with Ks-points. The assumed germ formula proves equivariance.

The main proof transports the finite action to `ULift (Fin n)` in the small
universe, proves continuity through a discrete homeomorphism, applies
`etaleFieldGsets`, and composes the comparisons and counit into an action
isomorphism. No nonempty hypothesis or special empty-case witness is needed.

Added `Sheaf.FieldTheory.GaloisAutomorphismExtension` for the remaining pure
field-theoretic extension step. The constructed sheaf and the transported action
are actual constructions; no definition chooses data from an unproved existence
theorem. Both files compiled without warnings using `lcompile.py --all`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.galoisStalkActionFunctor_finite_mem_essImage`
(node `lem-exc-galois-stalk-finite-action-realization`). Its private helper
`galoisStalkActionFunctor_representable_comparison` is also fully proved.
There are no sorries in the item's module.

Added one hole: `exists_algEquiv_extending_separableClosure`
(node `lem-exc-galois-automorphism-extension`), in
`Sheaf.FieldTheory.GaloisAutomorphismExtension`. This is a decomposition with
one hole closed and one strictly smaller hole added, not a claim of a net
reduction in holes or of a proof independent of sorry. The remaining statement
concerns only extending a field automorphism and contains no sheaf, stalk,
finite action, or essential-image assertion.

## No longer needed

Removed the proof imports
`Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`,
`Sheaf.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`, and
`Sheaf.AlgebraicGeometry.GaloisStalkActionFunctor`.

The corresponding planned proof-dependency nodes
`lem-weil-pbc-etale-fibre-discrete-separable-points`,
`lem-weil-pbc-small-etale-representable-presheaf-sheaf`, and
`lem-exc-galois-stalk-action-functor` are no longer needed by this proof.
The planned node `lem-galois-stalk-representable` and its particular
`Point.shrinkYonedaCompPresheafFiberIso` construction are replaced by the proved
identity-germ evaluation argument, which works directly in the larger value
universe. These are local pruning claims; other modules may still need them.
The item's existing public imports remain because the statement uses their types and
instances. The second reading additionally removed redundant imports
`Mathlib.CategoryTheory.Sites.LeftExact` and `Mathlib.Topology.Algebra.MulAction`
from the item, and `Mathlib.FieldTheory.IsAlgClosed.Basic` from the new field module;
the needed declarations are already publicly available through other imports. No unit's statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The DAG omitted the separate
field extension assertion needed to instantiate the assumed germ formula.
`AlgEquiv.liftNormal` cannot directly provide it when Omega is transcendental
over K, since `Normal K Omega` includes algebraicity. The new node records the
full transcendence-basis argument instead of adding that hypothesis.

The planned residue-field comparison already has proved source tools:
`Scheme.Hom.exists_SpecMap_comp_eq_of_isSepClosed` in `GeometricLifts`, and
`Scheme.SpecMap_comp_injective` in `ResidueField`. Neither had a DAG attachment,
so this delivery attaches them as two already closed source nodes. Their Lean
files are unchanged and are not delivered.

The local checkout has no `literature/stacks-project` text files. I checked the
primary source at https://stacks.math.columbia.edu/tag/03QW and
https://stacks.math.columbia.edu/tag/03QT. Tag 03QW explicitly states the
surjectivity of the automorphism restriction, including nonalgebraic geometric
points. The supplementary natural-language extension proof is written by T2.
LeanSearch returned Internal Server Error; that result is recorded as unavailable,
not as absence. LeanFinder and actual Mathlib/source searches were inspected.
The item is itself a created node and the ancestor helper returns `None`; the
new nodes refer to the existing blueprint ancestor used by its parent chain,
`lem-exc-field-discrete-modules` (traced through the recorded `blueprint.from`
chain).

## New nodes

`lem-exc-galois-automorphism-extension` states the pure field extension step,
with one named sorry in its new module and a complete proof in its docstring
and node. Edge cases checked: trivial g admits the identity; an algebraic Omega
uses an empty transcendence basis; positive characteristic is covered by unique
purely inseparable extensions. The hypotheses allow transcendental Omega.

`lem-exc-etale-lift-separably-closed-factorization` attaches the already proved
source declaration
`AlgebraicGeometry.Scheme.Hom.exists_SpecMap_comp_eq_of_isSepClosed`.
It is used for surjectivity of Ks-points to Omega-points.

`lem-exc-field-point-precomposition-injective` attaches the already proved
source declaration `AlgebraicGeometry.Scheme.SpecMap_comp_injective`.
It is used for injectivity of that same map. These two nodes add no holes.
There are no statement-change records because no existing signature or
definition was changed.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered item module with the repository version. The target theorem signature is unchanged; only its proof, imports, and a private helper were added. The field-extension module contains a new theorem with a matching node.
2. Compiled both delivered modules with `lcompile.py --all`; both compile without errors or warnings. The item has no `sorry`; the sole remaining `sorry` is the named field-extension theorem, documented in its node and docstring. No forbidden declarations or hollow definitions were introduced.
3. Checked the new split-off statement against the extension argument and edge cases (algebraic and transcendental overfields, empty transcendence basis, and positive characteristic). It is strictly smaller than the sheaf realization theorem and has exactly the hypotheses used by the proof. The two attached source declarations already exist and are unchanged.
4. Verified the proof follows the unit route through `etaleFieldGsets`; the direct stalk comparison is below the unit level. Removed imports are listed above, and the DAG proof dependencies match the declarations actually used.
5. Checked changed node metadata, including `proof`, `proof_deps`, `proof_origin`, `lean`, source locations, and the new node records. Verdict: PASS; changes are limited to the intended proof, its required helper theorem, and corresponding DAG/report metadata.

Changed after review: added this second-reading record to satisfy the stage-3 delivery contract; no Lean code or mathematical statement was changed.

Added the previously omitted citation lem-weil-pbc-sets-sheafification-geometric-stalk to step 2 and proof_deps; its recorded Mathlib instance is exactly the stalk isomorphism used in hη.


## Second reading by T2

1. **Interface: PASS.** Read the complete diff against the repository module and
   checked it with `stage3_delivery.diff_module`: `statement_changed` is empty.
   The original signature, including both universes, the compatibility of the
   field embeddings, the arbitrary functor T and comparison j, the germ formula,
   and the finite essential-image conclusion, is byte for byte unchanged. There
   are no changed definitions, adapted modules, or statement-change records.
2. **Proof and trust: PASS.** Independently compiled both modules through
   `lcompile.py --all`, with no errors or warnings. Read the identity-germ
   bijectivity proof: evaluation descends via `presheafFiberDesc`, is a left
   inverse, and joint surjectivity plus `toPresheafFiber_w_apply` gives the other
   direction. The sheaf is the explicit sheafification of lifted Yoneda, not
   an arbitrary witness extracted from a sorry. The private comparison and
   original theorem have no local holes. Scratch `#print axioms` checks for
   both and the field lemma return only propext, Classical.choice, Quot.sound,
   and sorryAx. The sole added hole is the named field-extension theorem;
   no forbidden declaration or hollow definition occurs.
3. **New statements: PASS.** Read Stacks Tags 03QW (the surjective restriction
   after the nonalgebraic-point example) and 03QT, and matched the field lemma's
   hypotheses to the embeddings and algebraically closed geometric field.
   Algebraicity of Omega is deliberately absent. The algebraic closure inside
   Omega is normal over K, so extending g there and then fixing a transcendence
   basis gives an automorphism of its rational function field; uniqueness of
   algebraic closures extends this to Omega. The restriction equation has the
   correct orientation. Checked g = 1, algebraic Omega (empty basis), and
   positive characteristic (unique purely inseparable extension). This lemma
   contains no sheaf or realization assertion and is a strict part of the
   argument. Independent LeanFinder search for extension via a transcendence
   basis and Loogle search for `IsAlgClosure.equivOfEquiv`, plus rg in Mathlib
   field theory and both project roots, found tools but no ready replacement.
   In particular `equivOfTranscendenceBasis` returns a ring equivalence without
   the required restriction formula. Read the two new source attachments at
   GeometricLifts.lean:54-88 and ResidueField.lean:90-108; their hypotheses and
   conclusions exactly match the factorization and injectivity used by hq.
4. **Route and pruning: PASS after import cleanup.** Finite transport uses
   ULift (Fin n), including n = 0, and continuity is transported by a discrete
   homeomorphism. The proof uses `etaleFieldGsets` and its counit, then the
   representable comparison and germ formula to construct the action iso.
   All four removed old proof dependencies, including
   `lem-galois-stalk-representable` despite its indirect original import, are
   listed in No longer needed. Read dag/units/sk-prop-h2.json: its realized
   arrays are empty; this subordinate comparison bypasses no recorded unit
   statement or proof step. Retained the original public imports needed for
   the signature's types and discrete-action instances.
5. **DAG: PASS.** Read the changed realization node and all three new nodes.
   The five proof dependencies correspond to etaleFieldGsets, sheafification
   preserving stalks, separably closed lift factorization, precomposition
   injectivity, and automorphism extension. Read the three cited field-theory
   leaf nodes; normal extension is applied to the algebraic closure inside
   Omega, never to a transcendental Omega/K. New records include source,
   docstring proof, searches, creation data, blueprint ancestry, chapter,
   unit, and matching Lean signatures. The two source nodes attach existing
   proved declarations and introduce no Lean files or holes.

Changed in this reading: removed the three redundant imports listed above,
validated each removal in a scratch compile, and appended this independent
review. No mathematical statement or proof term was rewritten. This remains
one original hole closed and one strictly smaller hole added (net zero), a
decomposition rather than a claim of a fully sorry-free proof.
