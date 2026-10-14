## What changed

The proof of `AlgebraicGeometry.exists_selfTor_ordinary_localized_comparisons` is
complete, with its original signature and public imports unchanged. It now reduces
an arbitrary, possibly unbounded K-flat resolution to a nonpositive termwise flat
resolution of the single closed-structure sheaf. The new module
`Sheaf.AlgebraicGeometry.SelfTorNonpositiveFlatSections` contains precisely the
remaining bounded affine calculation and its normalized restriction square.

The main module proves the general tensor-quasi-isomorphism cone argument, constructs
a common K-flat refinement of two resolutions using Mathlib's derived-category roof
API, and obtains an isomorphism of their ordinary tensor homology sheaves. It composes
the bounded chart coordinates with the linear equivalences on sections of this one
sheaf isomorphism. Naturality of that morphism proves the restriction equation.
The quotient homomorphism and the two augmented chain maps are constructed by the
already proved `exists_quotient_resolution_tensor_comparison`, after the actual
`ideal_le_comap_ideal` containment is proved. No new data definition is introduced.

The cone arguments reuse the proved generic-site argument in
`OpenKFlatTensorHomologyComparison`; its public theorem has different localized-site
endpoints, so it cannot directly provide this ambient isomorphism. All private
helpers in the delivery have complete proofs.

Both modules compiled together using `lcompile.py --all`: approximately 5 seconds
for the new statement module and 20 seconds for the assigned module. No compiler
errors or warnings remained. Declaration-local settings allow 800000 heartbeats for the main theorem and
large tensor/bounded-replacement instance terms, within the unchanged 60-second
file limit. All elaboration settings are local to individual declarations; the
interface checker reports no changes for the assigned module. The standard source tags 08DX, 06YB, 06YS and 00LS were also read from
the Stacks Project pages while checking the reduction.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_selfTor_ordinary_localized_comparisons`
(node `new-h3-self-tor-ordinary-localized-comparisons`). There are no sorries in the
assigned module.

Added one named hole, with proof exactly `:= by sorry`:
`AlgebraicGeometry.exists_selfTor_nonpositive_flat_sections`
(node `new-n4-self-tor-nonpositive-flat-sections`), in its own new module. Its
statement assumes actual flatness of every term and actual vanishing in all positive
degrees; it does not assume the original arbitrary K-flatness hypothesis and does
not construct algebraic comparison maps. Its docstring gives the augmented tensor
zigzag, its affine normalization, the restriction-square argument, and the edge
cases. These assumptions genuinely restrict the input complexes: the original
complex can be unbounded or have nonflat terms. The main proof establishes the
reduction rather than repackaging that hypothesis.

This is a decomposition, not a complete proof free of reachable sorries: one upper
hole is closed and one specialized geometric hole is added (net zero newly closed
holes). The substantive completed parts are arbitrary-unbounded-resolution
invariance, transport of the restriction equation through a sheaf isomorphism,
and algebraic comparison existence. Existing dependencies may still rest on their
own named sorries; no additional holes are introduced there.

## No longer needed

The proof no longer needs `lem-pc-open-kflat-tensor-homology-comparison` or its
module `Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison`. Its public
localized-site theorem is unnecessary for the bounded augmented zigzag, whose two
quasi-isomorphism legs follow directly from K-flatness, tensor-cone comparison, and
the acyclic-cone criterion. Both delivered modules omit that import. This prunes
the dependency from this item's branch; other target branches may still need it.

The complete list of old parent-node dependencies removed from its direct
`proof_deps` is:
`lem-pc-affine-chart-total-tensor`, `lem-pc-kflat-open-restriction`,
`lem-pc-open-kflat-tensor-homology-comparison`,
`lem-sc-affine-quotient-resolution-sheafification`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, and
`lem-weil-pbc-spec-module-tilde-sections`. All except the open K-flat homology
comparison remain dependencies of the new bounded subproblem; only that comparison
is pruned from this branch.

The assigned module no longer directly imports:

- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`;
- `Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction`;
- `Sheaf.AlgebraicGeometry.AffineChartTotalTensor`;
- `Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison`.

The first three imports, and their corresponding nodes, are retained for the
bounded geometric subproblem in the new module. They are relocated dependencies,
not pruned ones. The fourth import is removed entirely from this delivery. The algebraic quotient-comparison module stays in the
main proof; the bounded subproblem assumes supplied comparisons and does not import
it. The proof imports added to the main module are the flat replacement and K-flat
resolution modules, tensor closedness, the tensor-cone and acyclic-cone APIs,
`Mathlib.Algebra.Homology.BifunctorFlip`, and the new specialized module. The
section-linear-equivalence API is already available through the original public
ideal-sheaf-module import; its redundant extra import was removed. Every added import supplies a used declaration or instance.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The original DAG proof did not
expose the distinction between the arbitrary unbounded K-flat comparison and the
nonpositive flat affine calculation. The reduction separates them and proves the
first part in Lean. The existing affine quotient sheafification theorem provides
existence of a quasi-isomorphism, but its signature alone does not expose the
normalized augmentation/restriction square needed for the new geometric hole;
its future proof must construct the normalized comparison described in the docstring,
not choose unrelated chart equivalences from existence.

The unit `sk-thm-picard-duality` has empty realized statement/step lists in its
record. This delivery does not modify any unit or bypass a realized unit node.
The new statement was checked against zero rings, unit ideals, degree zero, and
empty basic opens. For unit ideals the quotient tensor complex has zero terms;
K-flatness makes the tensor with the corresponding zero restricted coefficient
acyclic, and both coordinate modules are zero.

## New nodes

`new-n4-self-tor-nonpositive-flat-sections` states only the nonpositive termwise flat
case of the affine geometric comparison, for supplied augmented algebraic maps.
Its proof follows the original affine zigzag route, with flatness and the bound
explicit. Its source is Stacks Tags 08DX(2), 06YG, 06YB, 01I9 and 00LS; its searches
record the actual LeanFinder/Loogle/grep results and the unavailable LeanSearch
service. Its blueprint ancestor, chapter and unit are inherited from the assigned
node. The assigned node's proof, dependencies and proof origin now describe the
bounded replacement, common-refinement tensor homology isomorphism, and section
naturality proof. No definition/signature changes, forced adaptations, deletions,
or change records are required.

## Second reading by N4

1. Compared the delivered parent with the repository using `diff -u` and separately
   compared the complete theorem signature as text: byte-identical. All eight
   original public imports remain identical. The only existing node fields changed
   are `proof`, `proof_deps`, and `proof_origin`. There are no changed definitions,
   target statements, forced adaptations, or undeclared interface changes. Verdict:
   pass.

2. Read every helper and the parent proof, then compiled both modules with the
   authorized `lcompile.py --all`. Both compiled without warnings (5.5 and 21.9
   seconds in the initial review build). The cone isomorphisms have the correct
   tensor orientation; braiding is applied before total-complex flipping. In the
   roof argument both legs become quasi-isomorphisms because their derived images
   are invertible. Both are then precomposed with a K-flat resolution before the
   tensor comparison. The final equation uses naturality of a single sheaf map,
   rather than unrelated equivalences on each chart. No forbidden declarations,
   data definitions, or hidden holes occur. The sole added hole is the named public
   theorem `exists_selfTor_nonpositive_flat_sections`, with its node and docstring.
   The scratch `#print axioms` check showed only `propext`, `Classical.choice`,
   and `Quot.sound` for all five private helpers. The parent additionally showed
   `sorryAx`, expected from the explicitly open geometric statement. The delivery
   probe also checks every declaration. Verdict: valid reduction, not a sorry-free closure.

3. Read the new statement and every clause of its docstring against the supplied
   comparison maps. The nonpositive and termwise-flat hypotheses restrict the
   input; the parent genuinely proves the reduction from arbitrary K-flat input.
   The universal comparison clause is true: the quotient equation determines the
   coefficient restriction, the augmentation equation determines the map after
   passage to the derived category, and the pure tensor formula determines k on
   generators. Thus the normalized augmented zigzag gives the same square for
   every supplied lift. The bounded result does not also have to construct those
   lifts. Checked degree zero, the identity inclusion, empty basic opens, zero
   rings, and the unit ideal. Degree zero is the quotient augmentation calculation;
   for the unit ideal both sides are zero by acyclicity of the tensor with a K-flat
   resolution. No case needs a nonzero ring or a regular immersion.

   Independently read [08DX(2)](https://stacks.math.columbia.edu/tag/08DX),
   [06YB](https://stacks.math.columbia.edu/tag/06YB),
   [01I9](https://stacks.math.columbia.edu/tag/01I9), and
   [00LS](https://stacks.math.columbia.edu/tag/00LS). The first is the affine derived
   tensor identification, 06YB is the stalk criterion supporting restriction,
   01I9 supplies functorial affine change of rings, and 00LS gives augmented lifts
   and homotopy uniqueness. The new theorem is their specialized calculation,
   not a verbatim assertion of a single tag. Independently searched with LeanFinder
   for affine Tor sections of bounded above flat resolutions, Loogle for
   `"mapBifunctor", "QuasiIso"`, and grep for Tor/sheaf and flat/sections, plus
   local `rg` through `lean/Sheaf/AlgebraicGeometry` and upstream algebraic geometry.
   No direct theorem was found. The nearby ambient self-Tor comparisons depend on
   this item, and the generic-site helper in OpenKFlatTensorHomologyComparison is
   private; its public localized-site theorem has different endpoints. The affine
   sheafification and total-tensor statements give components but not normalized
   restriction compatibility. The remaining hole cannot be closed by a short
   application of either. Verdict: true, strictly specialized subproblem.

4. Followed the proof from the parent downward and checked the original dependency
   list. Added the full six-node removal list above: five dependencies are relocated
   to the bounded problem and one is removed from this branch. The generic cone
   arguments have no public upstream replacement with these endpoints. Checked
   `dag/units/sk-thm-picard-duality.json`: its realized statement and sole step
   lists are empty; no realized node is bypassed or edited. Changed the new module's
   KFlat import experimentally from public to plain. The dry-run compiler showed
   that its public tensor-zero-morphism instances are required to elaborate the
   total tensor in the statement. A direct public BifunctorShift import exposes
   the total-tensor declaration but not these instances. Restored the original
   public KFlat import: it is a statement dependency despite absence of an explicit
   IsKFlat hypothesis. Original public imports
   are preserved. Verdict: route retained and pruning accurately reported.

5. Opened both node JSON files and compared them with Lean. The parent steps match
   bounded replacement, roof/tensor invariance, and quotient comparison plus
   section naturality. Each node's `proof_deps` is exactly the union of its steps'
   uses. The new node includes the source, self-contained hypotheses and quantified
   comparison clause, proof steps, search records, creation provenance, blueprint
   ancestor, chapter/unit, and verbatim Lean statement. Its supplied-map clause
   agrees with Lean's universal quantifiers. The original statement is unchanged.
   Verdict: pass.

Second reading changed only reporting: the exhaustive removed dependency list and this independent review.
One original hole is closed, one strictly specialized hole is added, net zero;
the decomposition remains explicitly reported as such.
