## What changed

Replaced the hole in `AlgebraicGeometry.Etale.etale_limit_open_boundary_transform`
with a complete algebraic construction of the four maps and their five properties.
The existing theorem's signature, visibility, docstring, and public imports are preserved.

The private `diagramPairEquiv` identifies each evaluated diagram biproduct with
its product by the two projections; the inverse is the sum of the inclusions.
The private `exact_transport` proves image/kernel transport through additive
bijections. The fully proved private `algebraic_boundary_transport` takes bundled
abelian-group families, constructs the difference and boundary transformations,
and proves their naturality, the three exactness assertions, and the two squares.
The parent specializes it to the supplied diagrams and canonical maps.

Two strictly smaller geometric obligations are stated in separate modules.
`EtaleLimitOpenDifferenceNaturality` supplies additive stage/limit differences
with an equation specifying their value on every input, and their transition/leg
naturality. Those equations uniquely determine the maps by `AddMonoidHom.ext`.
`EtaleLimitOpenCompatibleBoundaries` takes these actual differences, with their
value equations, and supplies exact boundaries compatible with the canonical
maps. It does not construct any of the transported diagrams or transformations.
The witnesses are used only inside the parent's proof. No data definition chooses
an arbitrary existence witness; no new public data definition or axiom is introduced.
The private product equivalence is an explicit construction with proved inverse laws.

Read [Stacks Tag 0A50](https://stacks.math.columbia.edu/tag/0A50) and
[Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ). The extension from coefficient
naturality to all restricted transition/cone maps is explicitly agent-written in
the new nodes and their complete proof docstrings. The earlier sandbox searches
used LeanFinder, Loogle, source rg, and blueprint search; LeanSearch was unavailable.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.etale_limit_open_boundary_transform`
(node `lem-weil-pbc-etale-limit-open-boundary-transform`). There is no `sorry`
in the item's module. All its private helpers are fully proved.

Added two holes, each exactly `:= by sorry`, in separate modules:

- `AlgebraicGeometry.Etale.tailOpenDifference_naturality`, node
  `lem-weil-pbc-etale-limit-open-difference-naturality`.
- `AlgebraicGeometry.Etale.tailOpenCompatibleBoundaries`, node
  `lem-weil-pbc-etale-limit-open-compatible-boundaries`.

This is a decomposition: one upper hole closed, two narrower holes added, net -1
before pruning. It does not claim the geometric Mayer--Vietoris argument is proved.
The additive differences are uniquely fixed, whereas connecting maps are only
chosen in this existential proof. Checked empty/coincident opens, zero coefficients,
degree zero, and arbitrary coefficient maps: neither new statement assumes
coefficient identity/composition laws or a canonical formula for `G.map`.

## No longer needed

Removed these direct proof imports from the parent and replaced its direct DAG
proof dependencies by the two new nodes:

- `Sheaf.AlgebraicGeometry.EtaleMayerVietoris`.
- `Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback`.
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`.

The parent does not use the corresponding three nodes directly:
`lem-weil-pbc-etale-mayer-vietoris`,
`lem-weil-pbc-etale-mayer-vietoris-pullback`, and
`lem-weil-pbc-cohomology-pullback-functorial`.
The latter theory remains needed below the new geometric nodes and in existing
cohomology-map imports. These are direct-route removals, not a claim that these
modules leave every target's import closure. No global closure pruning count is
claimed. Evaluation's biproduct comparison and `biprodIsoProd` are also unnecessary:
the private product equivalence is proved directly from the biproduct identities.
The boundary module also omits an unnecessary import of the difference-naturality
module: its supplied maps are specified by their value equations, and its statement
uses only the existing canonical cohomology and restriction interfaces.
The exploratory extra import of `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
was removed. No fixed unit-level statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox ended with an unverified specialization exceeding 60 seconds.
The corrected algebraic transport uses bundled abelian-group families rather than
six raw families with separately synthesized dependent group instances. A diagnostic
with reduced recursion depth pinpointed those six instance searches. The bundled
specialization compiled in 43.7 seconds in the diagnostic sandbox. The production
sandbox compile of all three modules passed without warnings: 14.0, 20.2, and
47.5 seconds, respectively (final-all.log). After pruning the boundary import and
removing the parent's local attribute command, the final compile also passed:
boundaries 29.5 seconds, differences 18.7 seconds, parent 59.1 seconds
(final-clean-all.log).

Constructing a concrete bundled difference on `Sheaf.H` also repeatedly expanded
the transferred `Ext` group structure in the kernel. The final geometric statement
instead fixes additive maps by explicit pointwise restriction equations, which
uniquely determine their data, and supplies their naturality. The geometric modules
then compiled in 16.1 and 18.5 seconds before formatting cleanup. No compiler limit,
launcher script, repository file, or existing definition was changed.

The prescribed `deliver3.py J3 Sheaf.AlgebraicGeometry.EtaleLimitOpenBoundaryTransform
--no-push` printed OK (final-clean-dryrun.log): the commit compiles and passes
preflight except for the second reading, which the script explicitly leaves to
the second reader on this first-worker dry run. Nothing was pushed. The parent's
local attribute command was removed after the first preflight treated it as an
interface command change. The original signature and public imports remain intact.

The original plan's phrase "the same connecting transformation" requires a single
boundary family compatible simultaneously with all arrows and cone legs. Separate
choices from the pairwise existential pullback theorem do not establish this.
The compatible-boundaries node fixes resolutions before considering arrows and
states all the needed equations. This is an interface gap, not a disputed statement.
The arbitrary supplied transports, product leg, and restriction row are handled
by the fully proved algebraic argument. No forced adaptation or change record is needed.

## New nodes

`lem-weil-pbc-etale-limit-open-difference-naturality` supplies the uniquely
characterized additive differences and their canonical map/leg naturality. It
requires neither a cover nor connecting maps and excludes all transported diagrams.

`lem-weil-pbc-etale-limit-open-compatible-boundaries` supplies the fixed-resolution
boundary family, its three local exactness properties, and its canonical map/leg
compatibility. Its supplied difference maps have their exact value equations,
so they cannot be arbitrary maps. It excludes the transported transformations,
exactness transport, and supplied cocone squares proved in the parent.

Both nodes inherit the parent's chapter and unit and retain the recorded blueprint
ancestor chain. There are no change records because no existing interface changes.

## Second reading by J3

1. Compared each delivered module with the repository version. The target
   declaration and all existing signatures are unchanged; only proof code and
   proof imports changed. The two additional modules are new split-off nodes.
   Verdict: pass.
2. Compiled all three modules with `lcompile.py --all`; compilation completed
   without errors or warnings. The parent has no `sorry`; the only remaining
   holes are the two named split-off theorems, each exactly `:= by sorry`, with
   matching DAG nodes and complete proof docstrings. No forbidden declarations
   or hollow definitions were found. Verdict: pass.
3. Read both split-off statements and checked edge cases (empty or equal opens,
   zero coefficients, degree zero). The difference equations uniquely determine
   additive maps, while the boundary theorem supplies only the geometric
   existence still required by the parent. Neither statement merely restates
   the parent target, and searches found no duplicate declaration. Verdict: pass.
4. Checked the parent proof route and imports. The private product equivalence
   and exactness transport are explicit; removed imports are listed above. The
   unit route and realized node chain are retained. Verdict: pass.
5. Compared the three DAG nodes with the Lean declarations: proof steps and
   dependencies name the two split nodes, node statements match the displayed
   interfaces, and the new nodes contain source, origin, searches, blueprint,
   and Lean records. Verdict: pass.

Changed during second reading: added this review record only. No Lean or DAG
source was altered after the first-worker delivery.
