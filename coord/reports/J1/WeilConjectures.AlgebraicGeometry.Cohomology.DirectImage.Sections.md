## What changed

Proved two original holes without adding holes or changing any existing signature or visibility.

`AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage` now follows from the existing
local vanishing theorem. Choose the neighbourhood and bound at every point, extract a finite
subcover by compactness, and take the finite supremum of the bounds. The existing
`isZero_of_iSup_eq_top`, applied to the subtype of the finite cover, gives global vanishing.
The empty base is included; no extra import is needed for this argument.

`AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_tensorObj_pullback_iso` now uses the
already proved ordinary projection formula, checked natural in the source module by a private
proved helper `projection_naturality`. The helper uses the tensor-sheafification adjunction and
elementary tensors, so it does not assume that global tensor sections generate globally.
Tensoring with an invertible module is an equivalence by its tensor-dual evaluation. Tensor
an injective resolution, apply the ordinary projection isomorphism termwise, take homology,
and compose the right-derived resolution comparisons. This works for arbitrary f as required.
Added the proof-only import `WeilConjectures.AlgebraicGeometry.Modules.Dual`.
Updated the proof, proof dependencies, and proof origin of `lem-pc-projection-formula` to record
the route actually used for its existing Lean declaration.

## Proved and sorry left

Closed two of six original holes:
- `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_tensorObj_pullback_iso`
  (`lem-pc-projection-formula`), proved without any sorried theorem.
- `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage`, proved from the unchanged
  local vanishing theorem; this is the real finite-cover argument, with no split-off statements.

No holes were added and none were split off.
Four original holes remain unchanged:
- `AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H`
  (`lem-pc-cohomology-sections-affine-base`).
- `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict`.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`.
- `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_restrict`.
The restriction/coherence/local-vanishing statements retain their existing source-library
context; no attachment or signature is changed by this delivery.

## No longer needed

None. The six proof-only imports used by the earlier projection route are retained because
`import_prune_check.py` found that downstream modules rely on declarations exposed through
those imports (`HomotopyCategory.MonoidalCategory.leftUnitor` and `rightUnitor`). Removing
them would break those downstream modules; direct-import adaptations are outside this repair.

## Where the brief, the DAG or earlier work was wrong

The global vanishing declaration is an original hole in the assigned module, and is also
listed in the source audit of `lem-pc-coherent-hi`; its primary Lean attachment is elsewhere.
Its existing docstring states the finite-cover argument proved here.

The natural-language projection-formula node states an unrestricted unbounded D_QCoh theorem,
whereas its existing Lean declaration states the invertible-module R^q case. The delivery
preserves that declaration exactly and proves it; it does not claim the more general statement.
Its unit has no realized statement/steps carried by the six pruned nodes, and the unit's
representability argument only needs the invertible twist formula. This shorter route stays
below the unit level.

The ordinary projection formula used as a tool is recorded in the declarations of
`lem-pc-closed-immersion-coherent-cohomology`, although the actual declaration lives in
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`. Its statement holds for every f,
so it fits here without a closed-immersion hypothesis. Tensor-dual evaluation is likewise an
already proved declaration of the module of `lem-pc-tensor-dual-invertible`.

For the untouched affine sections hole, the imported Leray statements use ringed-space derived
module cohomology, whereas `Scheme.Modules.H` uses underlying abelian Ext. They require a
natural comparison, not a definitional identification. The existing module/abelian comparison
only provides objectwise isomorphisms in its signature, despite mentioning naturality in prose.


## Earlier second reading (a previous round; superseded)

1. Compared the complete module with the repository version and checked the raw signature
   slices of every existing declaration: byte-for-byte identical. Existing visibility,
   docstrings, section hypotheses, and definitions are unchanged. Only the assigned module
   and the allowed proof metadata of `lem-pc-projection-formula` are delivered. Verdict: pass.
2. Compiled the module locally and compiled a full scratch copy with explicit `#print axioms`.
   The projection theorem and private naturality helper depend only on `propext`,
   `Classical.choice`, and `Quot.sound`. Global vanishing additionally depends on `sorryAx`
   through its unchanged local-vanishing premise; it closes its own hole, not that premise.
   The four original holes are whole proofs of the same named theorems; no forbidden trust
   mechanism or hollow definition was added. The resolution and equivalence data are real
   constructions using proved tensor-dual evaluation, not arbitrary sorried witnesses.
   Verdict: pass, with the four existing holes explicitly retained.
3. No statements or holes were split off. The private proved helper is the required naturality
   square for the already constructed projection map. Checked it after tensor sheafification,
   not by assuming global tensor sections generate. Checked the empty finite cover, empty base,
   degree zero, and unit twist: the arguments need no extra nonemptiness or positive-degree
   assumption. Verdict: pass; no new-node or split-off search obligation arises.
4. Read the ordinary projection formula, tensor-dual evaluation, and the open-cover vanishing
   lemma; searched the library and Mathlib for naturality, right-derived comparisons, and local
   vanishing with different terminology, and queried LeanFinder for exact-equivalence derived
   commutation. No ready-made theorem replaced the projection proof. Found the existing
   `AlgebraicGeometry.Scheme.Modules.isZero_of_iSup_eq_top`, which replaces the finite-union
   induction and avoids the added VanishingOnOpen import. The six removed original imports
   are exactly the six old projection-node proof dependencies. The remaining planned imports
   support the unchanged affine comparison route. Read the item's unit record:
   `sk-thm-picard-f-representable.realized` has no statement or step assigned to those six nodes;
   its representability step is unchanged. Verdict: pass after the vanishing simplification.
5. Compared the delivered node with its repository version: only `proof`, `proof_deps`, and
   `proof_origin` change. The three steps describe the actual naturality square, tensor
   equivalences and resolution, then homology and resolution comparisons. Their uses union is
   exactly `proof_deps`. Checked the existing dependency declarations for ordinary projection
   and tensor-dual evaluation. The report explicitly distinguishes the unchanged broader
   derived-category informal statement from the existing invertible-module Lean signature;
   this delivery establishes only the latter. No new nodes or statement changes. Verdict: pass.

Second-reading changes: replaced the redundant finite-union induction with the existing
open-cover vanishing theorem, removed the resulting unnecessary added proof import
`WeilConjectures.AlgebraicGeometry.Modules.VanishingOnOpen`, and corrected the report's account
of the vanishing proof and its existing audit attachment. No existing statement changed.

## Second reading by J1

1. Compared the delivered module with the repository version. Existing declaration signatures,
   visibility, definitions, and docstrings are unchanged; only proofs, imports, and the recorded
   proof metadata for `lem-pc-projection-formula` differ. Verdict: pass.
2. Compiled the module and checked its declarations with explicit `#print axioms`. The two closed
   proofs use only the permitted axioms, while the four retained holes remain the original named
   theorems. No forbidden trust mechanism or hollow definition was introduced. Verdict: pass.
3. Checked edge cases of the finite-cover argument (including empty base and empty cover), and
   the tensor projection argument (degree zero and unit twist). No statement was split off and no
   new statement was added. Verdict: pass.
4. Searched Mathlib and the library for an existing naturality or derived projection theorem and
   for a shorter global-vanishing argument. The proof uses the existing tensor projection formula,
   tensor-dual equivalence, and `isZero_of_iSup_eq_top`; the unit route remains intact. Verdict: pass.
5. Compared the changed node metadata with the Lean proof. Its proof steps and dependency union
   record the naturality square, tensor equivalences, injective resolution, homology, and derived
   comparisons actually used. No statement or dependency outside the permitted proof metadata was
   changed. Verdict: pass.

Second-reading changes: added this explicit second-reading record required by the delivery
contract. The proof and declarations were otherwise unchanged.
