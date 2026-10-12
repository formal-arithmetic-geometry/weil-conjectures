## What changed

Completed `CategoryTheory.Sheaf.torsor_h1_boundary_representative` in
`Sheaf.CategoryTheory.Sites.TorsorH1BoundaryRepresentative` with its statement unchanged.
The proof obtains a representative extension, uses `Quotient.sound` to transport the
class along its torsor isomorphism, and applies the already proved
`CategoryTheory.Sheaf.Torsor.classH1_lifts` for both class identities.
The proof imports `Sheaf.CategoryTheory.Sites.ZariskiTorsorRepresentativeExists`
in place of `Sheaf.CategoryTheory.Sites.ZariskiExtTorsor`.

The new module states only the extension/fibre existence step. It contains no
cohomology-class identity or converse clause. Its source is Stacks Lemma 02FQ,
first construction, read at https://stacks.math.columbia.edu/tag/02FQ; the local
normal-form argument supplies the omitted fibre identification. No definitions,
existing signatures, visibility, or public imports were changed. The unit
`sk-thm-curveestimate` has no realized intermediate proof steps to bypass;
its realized statement and the ancestor's representative-level route are kept.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.Sheaf.torsor_h1_boundary_representative`
(node `lem-sc-torsor-h1-boundary-representative`). There are no sorries in the item's
module. Added one hole, the public theorem
`CategoryTheory.Sheaf.zariski_torsor_representative_exists`
(node `lem-sc-zariski-torsor-representative-exists`), in its own new module.
This is a decomposition: one original hole closed, one strictly smaller hole added,
net zero holes. Both cohomology-class identities are proved from the existing
sorry-free boundary theorem; only the extension construction remains.

The previous sandbox-only `boundary_representative_exists` with an artificial
`∧ True` was discarded, rather than delivered as another hole. No arbitrary
witness is selected inside any definition. Both delivered modules compile in
import order through `lcompile.py --all`.

## No longer needed

Removed the direct proof import `Sheaf.CategoryTheory.Sites.ZariskiExtTorsor`.
The following six Sheaf modules disappear from this item's import closure:

- `Sheaf.CategoryTheory.Sites.ZariskiExtTorsor`
  (`lem-sc-zariski-ext-torsor`).
- `Sheaf.CategoryTheory.Sites.ZariskiContractedPowerExtension`
  (`lem-sc-zariski-contracted-power-extension`).
- `Sheaf.CategoryTheory.Sites.ZariskiContractedPowerExtensionPresentation`
  (`def-sc-zariski-contracted-power-extension-presentation`).
- `Sheaf.CategoryTheory.Sites.ZariskiContractedPowerTorsor`
  (`lem-sc-zariski-contracted-power-torsor`).
- `Sheaf.CategoryTheory.Sites.CoherentContractedPowers`
  (`def-sc-coherent-contracted-powers`).
- `Sheaf.CategoryTheory.Sites.BinaryContractedProductPresentation`
  (`def-sc-binary-contracted-product-presentation`).

These modules may still be needed by other items; this report claims pruning
from this item's proof and closure only. The planned standalone
`def-sc-topological-abelian-cohomology` proof dependency is no longer cited by
this item's proof: the boundary map is supplied by `classH1_lifts` in the
already public-imported source torsor module. It remains a statement dependency
and a dependency of the new extension existence node.

## Where the brief, the DAG or earlier work was wrong

The recorded `zariskiExtTorsor` declaration asserts existence of an abstract
bijection between torsor classes and Ext, without specifying the representative
extension or the map to its fibre. Its signature therefore cannot supply the
witness demanded here. The contracted-power extension theorem requires
`G : Sheaf ... AddCommGrpCat.{u + 1}` for `X : Scheme.{u}`, while this item requires
coefficients in `u`. No existing interface has been altered to conceal this
mismatch. The new existence theorem isolates the missing same-universe step.

The previous attempt neither proved the main theorem nor provided a node or a
source docstring for its helper; its extra dependency copy was unnecessary.
The required launcher `deliver3.py` exists at the absolute path in the brief.
Mathlib searches used LeanFinder, Loogle, and grep. LeanSearch was attempted
twice but returned Internal Server Error; the node records that unavailability
without claiming a negative search verdict. The blueprint search found only
the existing étale extension/torsor bijection, not this Zariski representative
statement. Edge cases checked: a trivial torsor has the split extension
`G ⊕ ℤ_X`; for `G = 0` the fibre is terminal; on the empty scheme all involved
sheaves and the fibre have their unique empty-open sections. The local
normal-form construction applies uniformly to these cases.

## New nodes

`lem-sc-zariski-torsor-representative-exists` in
`dag/nodes/sec-curve-estimates/lem-sc-zariski-torsor-representative-exists.json`
records `CategoryTheory.Sheaf.zariski_torsor_representative_exists` in
`Sheaf.CategoryTheory.Sites.ZariskiTorsorRepresentativeExists`. It asserts
extension existence and equivariant fibre identification only, with the
same universes as the original item. The proof in words constructs the free
abelian sheaf, its augmentation and kernel map, the pushout extension, and the
local normal form identifying its fibre. The parent node's proof and
`proof_deps` now match the compiling Lean combination of this existence step
and `classH1_lifts`. No change records or forced adaptations are needed.

## Second reading by K3

1. **Statements unchanged.** Compared the delivered boundary module with the repository version;
   the theorem signature is byte-for-byte unchanged. The new representative-existence theorem is
   a strictly smaller extension-and-fibre statement, with the same universes and no class identity.
   Verdict: pass.
2. **Proof and axioms.** Compiled both modules with `lcompile.py --all`; the only remaining
   `sorry` is the named split theorem `zariski_torsor_representative_exists`. The boundary proof
   uses `Quotient.sound` and `Torsor.classH1_lifts`; no forbidden declarations occur. Axiom checks
   show only the permitted axioms plus `sorryAx` through the split theorem. Verdict: pass.
3. **New statement and source.** Searched the library and recorded LeanFinder, grep, and
   unavailable LeanSearch results in the node. The new theorem is sourced to Stacks Lemma 02FQ,
   and its docstring gives the free-sheaf, pushout, and local-normal-form construction. Edge cases
   (trivial torsor, zero coefficient sheaf, and empty scheme) are addressed in the report. Verdict:
   pass.
4. **Pruning and route.** The helper import replaces the unused Zariski extension import. Two
   helper imports (`Sites.Spaces` and `GrothendieckAxioms.Sheaf`) were removed from the new theorem
   module because its public statement compiles without them. The old contracted-power dependency
   chain and topological cohomology proof import are not used by the boundary proof, as listed
   above. The unit route and realized statement remain intact. Verdict: pass.
5. **DAG agreement.** The parent node's proof and `proof_deps` exactly follow the Lean proof, and
   the new split node's declaration, statement, source, and proof steps match its module. No
   existing declaration or target was changed. Verdict: pass.

I changed only the new module's unused imports and added this second-reading record; no theorem
signatures or definitions were altered.
