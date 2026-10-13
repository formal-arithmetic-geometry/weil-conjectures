## What changed

Replaced the sole sorry in
`Sheaf.Algebra.Homology.HomTensorNaturalityComponent`, declaration
`CategoryTheory.homTensorDegreewiseMap_natural_component`, with a compiling reduction.
The statement and existing public import are unchanged. The proof eliminates `p+n=q`,
applies localized pure-tensor extensionality, substitutes `p=i+j` on each summand,
and specializes a pure-tensor naturality lemma using the two existing currying
specifications. Its two new imports are private proof imports.

Added `Sheaf.Algebra.Homology.HomTensorLocalizedExt` and
`Sheaf.Algebra.Homology.HomTensorCurryNaturalPure`, one theorem per module, each
with a source, complete proof in words and matching DAG node. Updated the item's
proof, proof dependencies and proof origin to match this decomposition.

The first remaining theorem is a general universal-property statement for arbitrary
maps into internal Hom out of a total tensor; it mentions neither chosen currying
maps nor the maps of complexes f,g,h. The second concerns arbitrary maps satisfying
the currying equations and asserts only their evaluation on a single localized
pure tensor. Neither is a renamed copy of the projected morphism equality. Their
combination in the item's module is the actual reduction of morphism equality to
all tensor summands and all their local pure-tensor evaluations.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.homTensorDegreewiseMap_natural_component`
(node `lem-sc-hom-tensor-naturality-component`). No sorry remains in the item's module.

Added two holes, both complete public theorem proofs `:= by sorry`:

- `CategoryTheory.homTensorLocalized_ext`
  (`lem-sc-hom-tensor-localized-ext`, module `Sheaf.Algebra.Homology.HomTensorLocalizedExt`).
- `CategoryTheory.homTensorCurry_natural_pure`
  (`lem-sc-hom-tensor-curry-natural-pure`, module
  `Sheaf.Algebra.Homology.HomTensorCurryNaturalPure`).

This delivery is a decomposition, not a complete proof: one hole closed, two holes
added, net -1 before any changes in the existing transitive dependency closure.
The proof also uses the existing `homTensorDegreewiseMap_spec` and hence the
existing unproved `homTensorDegreewise_exists`; these are not newly added holes.

All three delivered modules compile together in import order with lcompile.py.
The new statements were checked against zero complexes, zero input sections,
zero maps f/g/h, and identity maps: bilinearity makes the zero cases consistent,
and identity maps give the original currying equation on both sides. Arbitrary
integer degrees and arbitrary sites are retained; no boundedness, finite support,
sectionwise surjectivity of the sheafification unit or generation by global pure
tensors is assumed. The extensionality hypothesis ranges over every object of the
localized site, which is essential for tensors whose sheaf sections are only
locally represented.

## No longer needed

No import or module is pruned. The original public import remains necessary.

The original node's direct proof dependencies
`def-pur-hom-complex`, `def-pc-tensor-complex-sheaves`, and
`lem-pc-sheaf-modules-tensor-closed` are replaced by the two smaller statements.
They remain transitive proof dependencies through those statements, so their
modules are not claimed as pruned. The original dependency
`lem-sc-hom-tensor-degreewise` remains directly used through the two
`homTensorDegreewiseMap_spec` applications.
No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the item's statement was found. The planned argument
requires two substantial glue steps not previously stated as reusable declarations:
localized pure-tensor extensionality through sheafification and coproducts, and the
pointwise compatibility of the Hom projection equations with the tensor comparison.
These are now explicit independent items.

The existing source-library tensor comparison naturality lemmas in
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed` have a single
universe for the site, its morphisms and coefficients. This item allows independent
site object and morphism universes. They cannot be applied directly without further
work. The pure-tensor node records a proof using general tensorator/counit/unit
naturality instead; no universe or signature was changed.

Attempts at the direct component calculation exposed the outer/inner projection
formulas, but reductions of the large chosen Hom projections and sheafification
instances were expensive. Those unfinished attempts are confined to the sandbox
scratchpad and are not delivered. No expensive library definition was changed and
no partial or private sorry is delivered.

LeanSearch returned Internal Server Error for both new statements. Its attempts
are recorded as unavailable without a mathematical verdict; LeanFinder, Loogle,
Mathlib grep and the local source searches supplied the other search checks.
The Stacks source files named by the existing node are absent from this machine's
checkout, so the cited text was checked at the official sources:
[Tag 0A90](https://stacks.math.columbia.edu/tag/0A90) and
[Section 03EK](https://stacks.math.columbia.edu/tag/03EK).
The component proof is an agent expansion of the omitted functoriality proof,
as recorded in proof_origin.

## New nodes

`lem-sc-hom-tensor-localized-ext` records the universal-property argument recovering
an internal-Hom morphism equality from all localized pure-tensor evaluations on
all total tensor summands. Its module is
`lean/Sheaf/Algebra/Homology/HomTensorLocalizedExt.lean`.

`lem-sc-hom-tensor-curry-natural-pure` records the scalar evaluation calculation
using the currying conditions, the Hom-complex componentwise functoriality formula,
`HomologicalComplex.ι_mapBifunctorMap`, and naturality of the sheafification tensor
comparison. Its module is
`lean/Sheaf/Algebra/Homology/HomTensorCurryNaturalPure.lean`.

Both inherit chapter `sec-picard-framework` and unit `sk-thm-picard-duality`, and
serve the original degreewise functoriality route. No change record is required:
no existing statement, definition or public import was changed.


## Second reading by A4

1. **Unchanged interface — pass.** Read the repository and sandbox versions and
   their diff. The only existing Lean file changes are two plain proof imports
   and the body of `homTensorDegreewiseMap_natural_component`.
   Its full signature, universes, implicit instances, notation, visibility and
   original docstring are unchanged. The declaration-diff check reports no
   statement or public-import changes. No existing definition is modified,
   and no change record or forced adaptation is needed.

2. **Kernel check and holes — pass as a decomposition.** Compiled all three
   modules together through lcompile.py in import order (about 20 seconds total),
   with no errors or warnings. Scratch copies with explicit print-axioms checks
   for each delivered theorem report only propext, Classical.choice, Quot.sound,
   and sorryAx. The two new public named theorems are exactly the two remaining
   holes; the original theorem has none. There are no definitions in the new
   files and no axiom, unsafe, opaque, extern or implemented_by declarations.
   The chosen currying maps use the existing unique-existence specification,
   so no arbitrary witness is introduced. Removed the scratch probe sources.
   One original hole closed and two added is net -1, not a complete proof.

3. **New statements — pass.** Read both statements, their complete docstring
   arguments, matching nodes, HomTensorDegreewise.lean, the actual definition
   of localized internal Hom in InternalHom.lean, and the tensor comparison
   and adjunction in Monoidal.lean and MonoidalClosed.lean. Checked the sources
   at [Tag 0A90](https://stacks.math.columbia.edu/tag/0A90) and
   [Section 03EK](https://stacks.math.columbia.edu/tag/03EK):
   the first states the functorial comparison and omits its proof; the second
   defines the sheaf tensor by sheafification and gives its bilinear universal
   property. The new nodes correctly mark their detailed arguments as agent
   expansions, rather than attributing those details to an explicit source proof.

   Localized extensionality quantifies over every U, source section s, and
   further object W over U. On each fixed (i,j) summand tensor extensionality
   identifies the maps before sheafification; the adjunction then identifies
   the sheaf maps. Localization preserves these tensors and coproducts;
   coproduct and Hom-section extensionality finish. This works for arbitrary
   X and N and does not assert global generation of sheaf tensor sections.
   If K or L is zero, the total source is zero and its Hom is zero, consistent
   with the empty family of nonzero generators. If X or N is zero, equality
   is forced. The empty site also causes no exception.

   Pure naturality uses arbitrary a and a' only through their two displayed
   currying conditions. Applying those conditions and the two Hom projection
   formulas produces the same value after f, g and h. The total-map summand
   formula and naturality of the canonical presheaf-to-sheaf tensor comparison
   justify the right-hand input. The degrees i+j+n and (i+n)+j agree without
   a sign or differential calculation. Zero x/y or any zero f/g/h gives zero
   on both sides, and identity maps reduce to the two currying equations.
   Extensionality has no naturality conclusion; pure naturality has only a
   single-tensor conclusion, without extensionality. They are strictly separate
   parts of the argument and are combined in the original theorem.

   Repeated searches with different phrasing through msearch.py: LeanFinder
   for local elementary-tensor determination and for bifunctorial adjunction
   evaluation; Loogle for tensor_ext and the total tensor-map inclusion;
   Mathlib grep for tensor_ext, sheafification extensionality, curry naturality
   and tensorator naturality. Also searched lean/Sheaf, the source sheaf-Hom
   and tensor modules, and the corresponding DAG nodes. Found the ordinary
   module tensor_ext, HomologicalComplex.ι_mapBifunctorMap, abstract closed
   adjunction naturality and the one-universe source tensorHomEquiv formulas.
   None supplies either complete localized statement at the original independent
   universes. The required remaining glue does not close in a short application;
   retained both named holes rather than duplicating an existing result.

4. **Route and imports — pass after report repair.** The proof eliminates hpq,
   applies localized extensionality, eliminates hij, and supplies the two
   currying specifications to pure naturality. It uses both new private imports
   and the existing public import; the new public imports supply types and
   definitions in their own statements. No unused import was found.
   Read dag/units/sk-thm-picard-duality.json: its realized statement list and
   sole realized step list are empty. This local reduction does not replace
   any realized unit step, nor change the unit's statement or route.
   Corrected No longer needed to name all three replaced direct dependencies
   and explicitly retain them transitively; no module is pruned.

5. **DAG agreement — pass.** The existing node changes only proof, proof_deps
   and proof_origin. Its two steps track the actual extensionality application
   and pure-tensor specialization with homTensorDegreewiseMap_spec. For all
   three nodes the union of step uses equals proof_deps. Both new nodes have
   matching Lean declarations and statements, source, statement dependencies,
   proof origin, searches, creation record, split status, blueprint ancestry,
   and the inherited chapter/unit. Their proof plans cite the Hom, total tensor,
   tensor-closed and currying dependencies needed by their prose arguments.
   No statement, unit, source or maintainer field was changed on an existing node.

Second reading changed the two new module titles and added their missing module
blueprint tags, removed an extra space before the original theorem's proof,
and corrected the dependency-pruning report. The mathematical proof and the two
new theorem signatures needed no repair. No additional hole was closed.
