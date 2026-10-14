## What changed

Closed the body of `SheafOfModules.fieldScalarRestriction_preservesInjectives` by a
complete Lean proof from a scalar-extension adjunction and monomorphism preservation.
Its declaration, visibility, and original two universe parameters are unchanged.
Only two private proof imports were added to the original module:
`Sheaf.AlgebraicGeometry.FieldScalarExtensionAdjunction` and
`Sheaf.AlgebraicGeometry.FieldScalarExtensionMono`.

Constructed the constant-presheaf structural ring map and the conversion from
ModuleCat-valued presheaves to modules over the constant ring presheaf. Constructed
scalar extension by Mathlib presheaf pullback followed by module sheafification.
Proved the full sheaf adjunction, including the inverse componentwise hom conversions
and naturality in both arguments. Proved monomorphism preservation for conversion,
then composed the inclusion, presheaf extension, and sheafification preservation results.
Finally applied Mathlib's adjunction criterion for preservation of injectives.

The larger-universe sheafification existence and local-bijectivity instances are proved
using Mathlib's filtered-colimit universe shrinking and an enlarged small site model.
Presheaf pullback is specified by its adjunction: its universal property determines it
up to unique natural isomorphism, and all downstream assertions are invariant under
that isomorphism. No arbitrary witness of a mere existence theorem is used to supply
unspecified algebraic data, and no definition contains a hole.

All seven delivered Lean modules compile together in import order without warnings,
using only lcompile.py. Updated the parent node's proof, proof_deps, and proof_origin.
No existing statement or definition was changed and no adaptation is needed.

## Proved and sorry left

Closed one original hole:
`SheafOfModules.fieldScalarRestriction_preservesInjectives`
(`lem-sc-field-scalar-restriction-injectives`).

Added exactly two lower holes, each a public named theorem with an entire proof in
words, a source, and its own new module and node:

- `SheafOfModules.fieldScalarPresheafPullback_isRightAdjoint`
  (`lem-sc-field-scalar-presheaf-pullback-exists`): existence of the presheaf adjoint
  for modules in Type(max u v), over an arbitrary ring k. Mathlib's existing general
  presheaf pushforward adjoint instance only covers its equal-universe specialization.
- `SheafOfModules.fieldScalarPresheafPullback_preservesMonomorphisms`
  (`lem-sc-field-scalar-presheaf-pullback-mono`): pointwise exactness of that presheaf
  scalar extension when k is a field. This has no sheafification or injectivity claim.

There is no remaining hole in the original module, the sheaf adjunction theorem,
the sheaf-extension monomorphism theorem, the universe-adjustment proofs, or any
private helper. This delivery is a decomposition: one upper hole closed and two
strictly lower holes added, net -1. It is not a claim of an axiom-free proof of the
original result; the final theorem still depends transitively on these two obligations.

The lower statements were checked mathematically for empty X, zero section rings,
noncommutative R and noncentral alpha. The tensor uses the right action
r*c = r*alpha_U(c), which commutes with left multiplication by R(U). Thus the
statements do not assume an algebra structure or commutativity absent from the item.

## No longer needed

No original import, node, or module was removed: the original node had no proof
dependencies and the original four public Mathlib imports support its statement.
There are consequently no existing DAG nodes or modules to prune in this delivery.

The stalk computation and tensor/stalk filtered-colimit interchange in the old
natural-language plan are unnecessary. Pointwise monomorphisms of presheaves and
left exactness of module sheafification replace those steps. No stalk or Ext API
was imported. The lower presheaf exactness module imports only the presheaf-adjoint
module and the Functor.EpiMono API, not the sheaf scalar-extension construction.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically usable but did not expose its two remaining
presheaf obligations. It also did not highlight two typing requirements: the item
has an inferred second universe parameter, and R is RingCat rather than CommRingCat.
Mathlib's commutative extendScalars API therefore does not implement its full
signature. The delivery preserves both requirements rather than specializing the item.

The unit `sk-prop-av-cube` and its route are unchanged. Its realized arrays are empty;
this auxiliary scalar-restriction item lies strictly below the unit-level cube argument.

The local repository contains the literature lists but not the Stacks source files or
the unit's referenced literature file. Canonical Stacks pages for Tags 0095, 0096,
02N4, 02N5, and 015Z were read online. The new presheaf construction proofs and the
universe adjustments are marked as agent-written expansions of those arguments.
WANTED: local Stacks sheaves.tex, modules.tex, cohomology.tex and homology.tex,
Tags 0095, 0096, 02N4, 02N5 and 015Z, for the new nodes and their parent.

## New nodes

`def-sc-field-scalar-presheaf-ring-map` records the explicit natural structural map
from the constant ring presheaf to R; its module is FieldScalarPresheafRingMap.

`def-sc-module-presheaf-constant-modules` records the explicit componentwise
conversion functor, in the same definition module FieldScalarPresheafRingMap.

`lem-sc-field-scalar-presheaf-pullback-exists` records the first lower obligation,
with the balanced tensor construction and its universal property, in its own
module FieldScalarPresheafPullbackExists.

`def-sc-field-scalar-extension` records the sheaf scalar-extension functor assembled
from conversion, universal-property presheaf pullback, and module sheafification,
with proved universe adjustments, in FieldScalarExtension.

`lem-sc-field-scalar-extension-adjunction` records the proved natural hom-bijection
composition, in FieldScalarExtensionAdjunction.

`lem-sc-field-scalar-presheaf-pullback-mono` records the second lower obligation,
proved in words using pointwise injections and field tensor exactness, in its own
module FieldScalarPresheafPullbackMono.

`lem-sc-field-scalar-extension-mono` records the proved composition of monomorphism
preservation statements, in FieldScalarExtensionMono. All nodes retain the parent's
chapter and unit and record all three kinds of Mathlib search; LeanSearch was
unavailable, while LeanFinder and direct source inspection supplied the usable APIs.

## Second reading by M2

1. Compared every delivered module against its repository path. Only
   FieldScalarRestrictionInjectives exists in the baseline; its sole declaration's
   signature, visibility and universe binder are byte-for-byte unchanged. The diff
   contains two private imports, a revised proof explanation and the proof body.
   The other six modules are new. No existing definition or target was changed.
   Verdict: pass.
2. Compiled all seven modules in dependency order with lcompile.py, without errors
   or warnings. Searched all delivered sources for forbidden declarations and holes:
   exactly the two reported public named theorems contain `by sorry`. Printed axioms
   of all ten public declarations in a temporary scratch copy. The structural map,
   constant-module conversion and both sheafification universe results use only
   propext, Classical.choice and Quot.sound; the other declarations additionally use
   sorryAx, accounted for by the two reported lower obligations. Definitions contain
   no holes. The chosen pullback has a determining adjunction universal property,
   and its downstream adjunction and monomorphism assertions are invariant under
   natural isomorphism. Verdict: pass as a decomposition, not a complete proof.
3. Read both lower statements and their entire docstring proofs. The adjoint-existence
   obligation works for arbitrary rings using the balanced additive tensor quotient;
   the monomorphism obligation uses sectionwise injections and field flatness.
   Checked empty X, the zero section ring, k = F_2 with R = k, and noncentral embeddings
   into noncommutative R: right multiplication through alpha commutes with the left
   R-action by associativity. The tensor hom-bijection determines the chosen left
   adjoint, and natural-isomorphism transport justifies the exactness assertion.
   Neither statement repeats the injective-preservation conclusion. Independent
   LeanFinder, Loogle and grep searches used different queries, and the upstream
   constant-ring sheaf restriction API was inspected: it requires commutative
   constant target rings and does not supply this varying-R result. Mathlib's general
   presheaf adjoint instance requires equal universes; its identity-ring-map instance
   does not cover alpha. No quick existing result closes either hole. Verdict: pass.
4. Read the proof from the original theorem downward. The final proof uses Mathlib's
   adjunction criterion directly. Its lower composition avoids stalk and Ext APIs.
   Both private new imports are used. Corrected three proof-only public imports in
   FieldScalarExtension to plain imports: Sites.LeftExact, Sites.Equivalence and
   Grp.FilteredColimits. Their APIs are needed only in the proved universe helpers,
   not in public signatures or definition data. The original node's proof_deps was
   empty, so the existing No longer needed section omits no old dependency. The
   sk-prop-av-cube unit has empty realized arrays and its route is unaffected.
   Verdict: pass after import repair.
5. Checked each node's statement, Lean declaration, proof steps, proof_deps union,
   proof_origin, source, blueprint ancestry and new-node metadata. Both remaining
   holes have separate matching nodes and modules. Replaced the seven new nodes'
   flattened lean.statement strings with the actual declaration signatures verbatim (from def/theorem, excluding modifiers);
   in particular the letI newline in the presheaf monomorphism statement is retained.
   Existing-node changes are confined to stage-3-owned proof fields. Spot-checked
   source Tags [0095](https://stacks.math.columbia.edu/tag/0095),
   [0096](https://stacks.math.columbia.edu/tag/0096),
   [02N4](https://stacks.math.columbia.edu/tag/02N4) and
   [015Z](https://stacks.math.columbia.edu/tag/015Z). They support the cited adjunction
   and flatness arguments; the noncommutative and universe extensions are explicitly
   attributed to the agent rather than asserted to be literal Stacks statements.
   Verdict: pass after metadata repair.

Second-reading changes: three proof-only imports made private, seven new-node Lean
signatures recorded verbatim, and this review appended. No proof, statement,
definition, hole count or dependency route was changed. One original hole is closed
by reduction to two strictly lower holes; net holes closed minus added remains -1.

Dry-run metadata correction: the first dry run rejected four signature records.
The signatures now use the project parser to retain the complete letI expression
and to omit noncomputable modifiers, as its canonical def/theorem signatures require.
No Lean code or mathematical statement changed.
