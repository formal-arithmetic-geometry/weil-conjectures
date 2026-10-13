## What changed

Proved `AlgebraicGeometry.supportedOpen_tensor_directImage_comparisons` in
`Sheaf.AlgebraicGeometry.SupportedOpenTensorDirectImageComparisons`, without changing
its statement, public imports, definitions or visibility. Added only proof imports
and proved private glue. Updated the existing node's proof, proof_deps and
proof_origin to match the compiled argument. No other library module is adapted. The conservative interface-command flag is
documented in
`coord/changes/supportedOpen-tensor-directImage-proof-elaboration.md`.

Exact restriction/homology and the stalk comparison establish vanishing on opens
with an independent localization universe. Open base change then propagates closed
support through derived direct image. The open direct image is fully faithful, so
the supported unit is invertible on U; both its endpoints vanish on X minus T.
Sheaf-module locality and homology detection prove global invertibility.
Applying Rf_* and the existing derived composition comparison gives the first
isomorphism. Restriction commutes with tensor, and tensorRight preserves the empty
coproduct, so tensoring preserves support. Apply the same unit argument to the
tensor input. Finally, compose the restriction and pullback adjunctions, transport
along direct-image composition, and use uniqueness of left adjoints to identify
restricted Lf^*K with L(fj)^*K. Map the resulting tensor isomorphism by R(fj)_*.

The auxiliary opens use `HasDerivedCategory.standard`; the given X, S and U
localizations and their universe w are retained throughout. There is no new
existential choice installed in a definition. The only new private definition
constructs a stalk isomorphism explicitly from existing natural isomorphisms.
The argument covers empty U, empty T, the empty scheme, zero E and unbounded K.
For U empty the support hypothesis forces E to be zero, and both comparisons are
between zero objects. For U total the unit and composition comparisons recover E.

Searches used msearch leanfinder (derived tensor/support/open direct image), loogle
(`CategoryTheory.MonoidalCategory.tensorIso`) and grep (tensor/support), together
with rg on both library roots. No exact existing theorem was found. Sources read
online: Stacks Tags 08DF (supported unit), 08FE (open base change), 06YH (K-flat
derived tensor), 079W (derived adjunction), and 0D5T (composition). The node remains
below the unit level; the unit's statement and steps are unchanged.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.supportedOpen_tensor_directImage_comparisons`
(node `lem-pc-supported-open-tensor-direct-image-comparisons`).

No sorry remains in the item's module. No holes, modules or nodes are added;
this is a proof from existing library declarations, not a decomposition. Every
private helper is fully proved. Imported declarations retain their existing
transitive dependencies; closing this module does not claim those are all closed.
Single-file local compilation passed without warnings. `deliver3.py K2
Sheaf.AlgebraicGeometry.SupportedOpenTensorDirectImageComparisons --no-push` printed
`OK (dry run)`: compilation and preflight pass except for the independent second
reading, which the second reader writes. Nothing was pushed. The delivery axiom
probe reported no forbidden axioms.

## No longer needed

The following planned direct proof dependencies are not needed or imported:

- `lem-pc-supported-open-pushforward`, module
  `Sheaf.AlgebraicGeometry.SupportedOpenPushforward`: its bundled statement needs
  same-w localizations on every over-site open. The supported unit needed here is
  proved directly from open base change, full faithfulness and local homology.
- `lem-pc-supported-derived-restriction-zero`, module
  `Sheaf.AlgebraicGeometry.SupportedDerivedRestrictionZero`: its same-w family of
  over-site localizations is unnecessary. The private exact restriction helper
  proves the needed vanishing in the independent target universe.
- `lem-pc-derived-pullback-open-restriction-universes`, module
  `Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`: uniqueness of
  left adjoints gives restriction of Lf^* along this single inclusion directly.
- `lem-pc-ringed-spaces-derived-pullback-composition`, module
  `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`: its global family of
  same-w scheme localizations and coherence data are unnecessary here.

These are removals from this node's direct proof route, not a claim that no other
target branch reaches them. All eleven added proof imports were checked by separately compiling a scratch
copy with that import removed; each removal failed. No pre-existing import was removed: all three original
public imports are required by the statement. The old ringed-space direct-image
composition node is still used transitively through the scheme-level
`derivedDirectImageComposition` wrapper and is not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged and is not disputed. The old plan's
supported-unit and support-vanishing interfaces demand same-w localizations on
all opens, which are not supplied by this theorem. Its global pullback composition
interface also demands localizations for all schemes. Those are interface
mismatches rather than mathematical obstructions; the proved private glue uses
standard localizations only on auxiliary opens and the existing independent-
universe open base-change and tensor comparisons.

Tag 08DX states preservation of quasi-coherent cohomology under derived tensor
and its affine computation; it is not itself the general open tensor comparison.
The imported comparison uses the K-flat construction, and the general restriction
argument is valid without quasi-coherence. No source statement is weakened.
The local checkout contains literature indexes but no fetched blueprint text;
the unit record was read and the relevant Stacks texts were checked online.

## Second reading by K2

1. **Interface unchanged — pass.** Read the full repository/sandbox diff and
   checked `stage3_delivery.diff_module`: `statement_changed = []`,
   `public_added = []`. The sole existing theorem signature is byte-for-byte
   unchanged, as are its visibility and three public imports. There are no
   adapted modules. Only private proved glue, proof imports and the documented
   local elaboration commands are added; no public definition changes.
2. **Proof and axioms — pass.** Independently compiled the delivered module
   locally using lcompile.py: exit 0, no warnings, 21.3 seconds. Compiled a
   scratch copy with explicit `#print axioms` for the target and all eight
   private declarations: every one uses only `propext`, `Classical.choice`,
   `Quot.sound`, with no `sorryAx`. There is no sorry, forbidden declaration,
   hollow definition or arbitrary existential witness chosen for data. The
   private stalk isomorphism is explicitly composed from existing isomorphisms.
   The supplied localizations on X, S and U remain in use; only auxiliary opens
   receive standard localizations.
3. **Split statements and small cases — pass.** No statements or holes are split
   off, and no new modules or nodes are added. Read every private helper: stalk
   vanishing implies sectionwise vanishing by section_ext; homology detects
   zero and invertibility; open base change preserves closed support; empty
   coproduct preservation makes tensoring preserve zero. Full faithfulness and
   the triangle identity invert the restricted unit, and the two-open cover
   gives its global invertibility. Empty U forces T empty and E zero; empty T,
   empty schemes, U total and zero E cause no exception. The argument assumes
   no boundedness of K. The final comparison uses uniqueness of left adjoints
   and does not assume a projection formula.
4. **Shortest route, imports and unit — pass.** Independently searched Mathlib
   with Loogle `DerivedCategory.homologyFunctor, CategoryTheory.Limits.IsZero`
   and rg on the derived-category sources and the library. The four Loogle
   hits are degreewise t-structure vanishing, not a replacement for the generic
   homology-zero helper. Read SupportedOpenPushforward,
   SupportedDerivedRestrictionZero, DerivedRestrictionIsIsoOpenCover and
   DerivedPullbackOpenRestrictionUniverses: their extra localization families
   or general two-open pullback comparison do not shorten this proof. Read the
   actual open base-change, tensor restriction, derived adjunction, composition
   and coproduct declarations used. Reviewed all eleven failed import-removal
   experiments; every added import supplies a required declaration or instance.
   The four bypassed planned nodes are all listed under No longer needed.
   The old ringed-space direct-image composition remains used through the
   scheme wrapper and is not pruned from the closure. Read
   dag/units/sk-thm-picard-duality.json: its statement, step and realized fields
   are untouched. The reviewed node is subordinate (`blueprint.is = null`);
   this support reduction does not replace the unit's Serre-duality step.
   Its pre-existing empty realized entries are not repaired by this delivery.
5. **DAG agrees — pass.** The only changed node fields are proof, proof_deps
   and proof_origin. The uses union is exactly proof_deps; the five steps
   follow the private support helpers, open base change, supported unit,
   tensor support and adjoint-uniqueness argument actually compiled. The
   statement, stmt_deps and lean signature record are unchanged. No new-node
   requirements apply. This closes one original hole and adds zero holes.

Second reading changed only the target's proof docstring: describe the actual
adjoint-uniqueness pullback comparison and retain the supplied U localization,
using standard localizations only on auxiliary opens. No proof repair was needed.
The independent axiom output also establishes that this compiled theorem has no
transitive sorry dependency, beyond the first reader's conservative report.
