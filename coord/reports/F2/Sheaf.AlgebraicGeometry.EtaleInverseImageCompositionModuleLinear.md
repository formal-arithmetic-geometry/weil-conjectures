## What changed

`AlgebraicGeometry.etaleInverseImageCompositionModuleLinear` retains its original signature.
Its proof obtains existence and the three compatibility equations from the new
`AlgebraicGeometry.etaleInverseImageCompositionModuleLinearCore`, then proves uniqueness
componentwise by injectivity of `(aU.comp aV).homEquiv`. The core asserts only existence and
compatibility, without uniqueness. Its import is private. The parent keeps the local heartbeat
option needed to elaborate its dependent application.

Removed the redundant private imports of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` and
`Sheaf.CategoryTheory.RingedSiteModules` from both delivered modules: all the statement's
infrastructure is already exported by the existing public import
`Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`.

## Proved and sorry left

Closed the direct hole in `AlgebraicGeometry.etaleInverseImageCompositionModuleLinear`
(node `lem-weil-pbc-inverse-image-composition-module-linear`). Added one direct hole in
`AlgebraicGeometry.etaleInverseImageCompositionModuleLinearCore`
(node `lem-weil-pbc-inverse-image-composition-module-linear-core`). The latter is the only
remaining sorry in the delivered files. This is a decomposition, not a completed proof of
module linearity: one hole closed, one added, net zero. The new work in Lean is the uniqueness
argument; the site-specific existence and compatibility proof remains open.

## No longer needed

Removed the two private imports named above from both modules. No whole-library module pruning
is claimed; the public import was retained unchanged.

The parent's old direct proof dependencies are no longer direct dependencies of its proof:
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-weil-pbc-inverse-image-composition`, `def-weil-pbc-direct-image`,
`def-weil-pbc-constant-sheaf`, `def-weil-pbc-etale-site`,
`lem-weil-pbc-constant-sheaf-maps-global-sections`,
`def-weil-sheaf-of-modules-category`, `def-weil-pbc-composite-adjunction`, and
`def-weil-pbc-inverse-image`. They remain dependencies of the core's proof plan, so none is
claimed to have left the target closure. The parent's sole direct proof dependency is the core.
No maintainer tool approval was removed from the existing node.

## Where the brief, the DAG or earlier work was wrong

The submitted core node incorrectly proposed constructing d by uniqueness of right adjoints
from `aUV` and `aU.comp aV`, whose left adjoints differ. That construction is not available.
The corrected plan first proves compatibility of the constant-ring maps, lifts the direct-image
comparison by linearity of restrictions, and then obtains the inverse-image comparison by the
module adjunction. Agreement with the abelian comparison follows from the given hom-equivalence
identities. The core's docstring and node now describe this argument consistently.

The copied Mathlib searches in the new node were replaced by searches actually run for F2.
The earlier report did not distinguish decomposition from a net hole reduction and omitted the
parent's removed direct DAG dependencies. Both points are corrected here. Stacks 03D8 states the
composition isomorphisms and says they are clear from definitions; it has no final uniqueness
argument. That argument is ours, using Mathlib's adjunction hom-equivalence.

## New nodes

`lem-weil-pbc-inverse-image-composition-module-linear-core` records the strictly smaller existence
and compatibility part, in
`lean/Sheaf/AlgebraicGeometry/EtaleInverseImageCompositionModuleLinearCore.lean`.
Its statement introduces the schemes, constant ring, module categories, lifts, and compatibility
equations, and omits the uniqueness conclusion established in the parent. Its docstring gives
the five-step proof with Stacks 03D8/03D7 as source. No definition or existing statement changed;
there is no change record.

## Second reading by F2

1. Compared the parent with the shared repository by `diff`. Its declaration signature and
   docstring are byte for byte unchanged; only proof code, the local heartbeat option, and
   private imports differ. The core module is new, with no existing users. There are no changed
   definitions, target statements, or modules held by other groups. Verdict: pass.
2. Compiled both files in import order through `lcompile.py`, without errors or warnings.
   Inspected the full files for forbidden declarations and hidden holes: there is one public
   named theorem with whole proof `by sorry`, the core, and no definitions that select data from an unproved existence theorem. Checked both declarations with `#print axioms` in scratch copies; both use exactly `propext`, `Classical.choice`, `Quot.sound`, and the transitive
   `sorryAx` from the open core. Verdict: decomposition,
   not a sorry-free theorem.
3. Checked the core against the unchanged parent clause by clause: it has identical hypotheses
   and the first three conclusion clauses, but omits uniqueness. The parent supplies a real
   proof of the omitted clause by `Iso.ext`, `NatTrans.ext`, and adjunction injectivity.
   Checked identity morphisms, the zero coefficient ring, and empty schemes: neither the
   linearity construction nor the categorical uniqueness argument requires nonemptiness or a
   nonzero ring. Read Stacks `lemma-push-pull-composition-modules` (03D8) and
   `lemma-adjoint-pullback-pushforward-modules` (03D7) in sites-modules.tex. Repeated LeanSearch,
   LeanFinder, Loogle, and grep searches; inspected Mathlib `pushforwardNatIso`,
   `pushforwardCongr₂`, `pullbackComp`, `conjugateIsoEquiv`, and
   `unit_conjugateEquiv_symm`. These give construction ingredients, but none states the core's
   compatibility with the arbitrary supplied abelian comparisons. Also searched the project's
   etale and adjunction modules. Verdict: true, smaller obligation; no exact existing match.
4. Checked the shortest categorical route for uniqueness: the proof directly uses the hom-set
   equivalence's injectivity, with no auxiliary lemma. Removed the two redundant private imports
   and listed every old direct proof dependency above. Read `dag/units/sk-thm-p1.json`: neither
   this node nor the core replaces a realized unit statement or step; all original site-specific
   dependencies stay in the core plan. Verdict: route retained; no global pruning claimed.
5. Read both DAG nodes against the Lean. The parent names the core as its only proof dependency;
   the new core node now has a self-contained statement and the original five-step existence
   argument, with `proof_deps` exactly the union of its steps' uses. Corrected its false empty
   dependency list and adjoint-uniqueness plan, its copied search records and blueprint path,
   and the parent's inaccurate source attribution. Verdict: consistent after repairs.

Second reading changed the core proof documentation and DAG plan, search records, private imports,
and report accounting. The parent uniqueness proof was retained.
