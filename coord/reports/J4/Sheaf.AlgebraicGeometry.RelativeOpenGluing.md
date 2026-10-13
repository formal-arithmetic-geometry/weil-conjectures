## What changed

Repair of the duplicate-theorem return: removed both private helper copies
from `AmbientOpenGluingObject.lean`. Added non-public
`import all Sheaf.AlgebraicGeometry.DerivedOpenGluingObjects` and call its
existing `AlgebraicGeometry.isIso_fiber_projection` (twice) and
`AlgebraicGeometry.compatible_of_difference` directly. The `all` form is
necessary because those existing helpers are private. No library module,
visibility or signature changes are needed. The ambient node records this
reuse, and the pruning claims below are corrected accordingly. The retained
second-reading section records the earlier delivery and predates this repair.

Replaced the original sorry in
`AlgebraicGeometry.Scheme.exists_relative_open_gluing` with a complete Lean proof
combining object extension and Hom gluing between two fixed ambient objects.
Its original signature is unchanged; the second reading updated its proof docstring
to describe the actual reduction. The proof expands
functoriality, substitutes the given map compatibility, postcomposes the object
transition equation, and glues the resulting maps on the union. It then composes
the object identifications with the canonical restriction comparisons.

Added `Sheaf.AlgebraicGeometry.AmbientOpenGluingObject` with the proved theorem
`exists_ambient_open_gluing_object`, using the existing private categorical helpers
from `DerivedOpenGluingObjects` without redeclaring them.
Its proof constructs a distinguished fiber triangle from the difference diagram,
compares each restricted triangle with a split biproduct triangle to prove its
projection invertible, and derives the transition equation by precomposing the
difference identity with the triangle's first map. This cone calculation reuses
the existing source of `DerivedOpenGluingObjects`; it is compiled here without
any covering hypothesis and requires no derived category on the union.

Added `Sheaf.AlgebraicGeometry.RelativeOpenDifferenceDiagram` with one named
geometric theorem, and `Sheaf.AlgebraicGeometry.OpenUnionHomGluing` with one named
fixed-object Hom theorem. Each has its own node and a full source-based proof
plan. Updated the original node's proof, proof_deps and proof_origin. The three
new nodes match their declarations. All proof imports in the item are non-public.
No existing definitions, signatures or public imports changed, and no forced
adaptations were needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_relative_open_gluing`
(node `lem-sc-relative-open-gluing`); its combining proof has no sorry.
Also proved the newly introduced
`AlgebraicGeometry.Scheme.exists_ambient_open_gluing_object`
(node `lem-sc-ambient-open-gluing-object`), by applying the existing categorical
helpers. The duplicate local helper declarations were deleted; no holes were
added or removed by this repair itself.

This is a decomposition of the original hole, not a completed proof independent
of new holes: one original upper hole closed, two strictly smaller holes added.
The two remaining sorries added by this delivery are exactly:

- `AlgebraicGeometry.relative_open_difference_diagram`, node
  `lem-sc-relative-open-difference-diagram`, in `RelativeOpenDifferenceDiagram.lean`.
- `AlgebraicGeometry.Scheme.exists_open_union_hom`, node
  `lem-sc-open-union-hom-gluing`, in `OpenUnionHomGluing.lean`.

Both proofs are exactly `:= by sorry` and have complete natural-language plans.
The first supplies maps between explicitly constructed direct-image objects and
split local normal forms; it neither constructs the glued fiber nor supplies any
map to a target E. The second glues local morphisms between two already fixed
ambient objects on the union; it has no arbitrary local objects A, B, overlap
isomorphism c, or constructed local identifications. The proved object-extension
theorem and the original theorem perform the categorical steps combining these
strictly separate inputs. No data is chosen from mere existence in a definition.

Edge cases checked mathematically: empty W or V, empty union, disjoint opens,
W contained in V, and W=V=X. In the difference diagram, an empty overlap makes
the overlap direct image zero; the local matrices remain invertible. If both
opens equal X, the diagonal matrix construction gives the usual split triangle.
Fixed-object Hom gluing promises a map only on the union, not on all of X.
The same Hom universe w is retained throughout. Extra local derived categories
needed by the remaining transport plan are provided by the existing localization
lemmas. No quasi-compactness, perfectness, support or boundedness is introduced.

All four delivered modules compile without warnings through lcompile.py. The
proof and signature checks are also run by deliver3.py --no-push. The original
unit record's realized lists are empty for this utility route and are unchanged.

## No longer needed

Removed the item's direct proof imports:

- `Sheaf.AlgebraicGeometry.DerivedOpenGluing`
  (`lem-sc-derived-open-gluing`);
- `Sheaf.AlgebraicGeometry.DerivedOpenLocalization`
  (`lem-pc-derived-open-localization-universe`);
- `Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction`
  (`lem-pc-open-derived-localization-adjunction`).

`DerivedOpenGluing` is no longer a direct proof dependency of the item.
`DerivedOpenGluingObjects` is now imported by `AmbientOpenGluingObject` to use
its two already-proved private categorical helpers. Its covering difference
module `DerivedOpenDifferenceDiagram` therefore remains in the import closure;
neither module is claimed pruned. The geometric covering theorem itself is
not applied: the relative difference diagram supplies the unrestricted input.
The duplicate local declarations `AlgebraicGeometry.Scheme.isIso_fiber_projection`
and `AlgebraicGeometry.Scheme.compatible_of_difference` are removed entirely.

The two localization lemmas remain in the plan of the open-union Hom node,
which also uses `lem-sc-scheme-derived-hom-gluing`. Thus they are no longer
direct dependencies of the original combining proof but are not certified
globally unreachable. No other modules are claimed globally pruned. The public
statement import `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps` remains.

## Where the brief, the DAG or earlier work was wrong

The original plan hides the ambient-change transport between X and W union V.
`derived_open_gluing` and `scheme_derived_hom_gluing` only handle opens covering
their ambient scheme; they cannot be applied on X for arbitrary W and V.
The docstring of `derived_open_difference_diagram` expressly says its local
construction uses no covering hypothesis, while its signature retains one.
Its source calculation indeed uses only restriction of direct images, counits
and invertible local triangular matrices. The new relative difference node
states this actual local calculation without altering the existing module.

The delivery makes the fiber-triangle and transition parts into real Lean,
leaving the geometric matrix calculation and fixed-object Hom transport as
separate items. Neither remaining theorem restates the original assertion.
No original statement is disputed, weakened, or changed. The returned delivery had duplicated two categorical helper statements and
proofs already present in `DerivedOpenGluingObjects`. This repair imports and
uses those existing private helpers directly. Their signatures have no cover
premise, so the ambient-object proof remains applicable to arbitrary opens.

## New nodes

`lem-sc-relative-open-difference-diagram` records the explicit direct-image
sum, overlap direct image, difference map, local projections and split normal
forms, sourced to Stacks 08DG and 08FE. Its module is
`Sheaf.AlgebraicGeometry.RelativeOpenDifferenceDiagram`. It is the geometric
part of the proof, strictly before completing its fiber triangle.

`lem-sc-ambient-open-gluing-object` records ambient extension of local object
data with its transition, sourced to Stacks 08DG. Its module is
`Sheaf.AlgebraicGeometry.AmbientOpenGluingObject`. Its theorem is proved in this
delivery from the relative difference diagram and categorical triangle axioms;
it is not a new sorry.

`lem-sc-open-union-hom-gluing` records fixed-object local Hom gluing on the
union, sourced to Stacks 08BW. Its module is
`Sheaf.AlgebraicGeometry.OpenUnionHomGluing`.

Searched the full blueprint for gluing and for the difference arrow, and the
existing DAG for ambient object extension and open-union Hom gluing. Existing
covering statements were read and compared against the required signatures.
Each new node has logged LeanFinder, Loogle and Mathlib grep searches; no exact
match was found. LeanSearch returned HTTP 500 and is recorded as unavailable,
with the other search methods used instead. No change records are needed.

## Earlier second reading (a previous round; superseded)

1. Compared the existing module with the repository by diff and compared node
   JSON fields. The existing theorem signature is byte for byte unchanged; no
   definition or public import changed. Only proof, proof_deps and proof_origin
   changed in the existing node. The other three modules and nodes are new.
2. Compiled all four delivered modules in dependency order through lcompile.py,
   with no errors or warnings. Only the two reported public named theorems have
   sorry. There are no definitions in this delivery, forbidden declarations or
   hidden holes. Explicit axiom probes and the delivery axiom check confirm only
   propext, Classical.choice, Quot.sound and the expected upstream sorryAx.
   Read both private categorical helpers: the first completes a triangle map
   and uses two-out-of-three; the second precomposes the difference equation and
   uses triangle zero composition and naturality. The final proof correctly
   postcomposes the transition equation and uses the Hom restriction equations.
3. Read the new statements against Stacks 08DG, 08FE and 08BW, fetched directly
   from their tag pages because this clone has no cohomology.tex. Checked empty
   opens/union, disjoint opens, nested opens and W=V=X. The difference matrix has
   diagonal (1,-1) on W and an invertible direct image of c on V; the Hom result
   requires equality on the overlap and asserts neither uniqueness nor a map on
   all X. Each remaining hole is strictly a part of the argument, with its own
   proof docstring and node, and neither restates the original theorem. Repeated
   searches with Mayer--Vietoris surjectivity, biproduct invertibility, and
   restriction/pushforward terms using LeanFinder, Loogle and Mathlib grep, plus
   rg through both Lean roots. Found underived sheaf and adjunction results,
   but no shorter complete derived statement. The existing difference theorem
   has an unavailable cover premise, and scheme_derived_hom_gluing needs the
   ambient-change transport left in the Hom hole. Neither hole closes in a
   short independent proof.
4. The route starts with the actual target reduction, then the fixed direct-image
   triangle calculation and fixed-object Hom gluing. No unit realization is
   bypassed: sk-thm-picard-duality has empty realized lists, unchanged. All three
   old direct proof dependencies are listed under No longer needed. Localization
   is still needed by the new Hom plan; no global unreachability is asserted.
5. Checked each node's statement against its Lean signature, proof steps and
   proof_deps union, proof_origin, sources, search records, created fields and
   blueprint provenance. They agree with the delivered reduction. New node Lean
   signatures match their declarations verbatim. Verdict: a valid decomposition,
   one old hole closed and two smaller holes added, not a completed target proof.

Changed the original proof docstring to match the actual ambient-object/Hom
reduction. Added non-public proof-plan imports for DerivedDirectImageOpenRestriction
in RelativeOpenDifferenceDiagram and the three stated dependencies of
OpenUnionHomGluing, so that its future worker can use the DAG plan's declarations.
No proof or statement repair was needed. These imports are needed by the remaining
proof plans and do not change any public interface.

## Second reading by J4

This reading is of the repaired delivery, including the non-public `import all`
that replaces the duplicate private categorical helpers.

1. Compared the item with the repository version and verified its existing
   theorem signature byte for byte by extracting the text before `:= by`.
   No existing definition, statement, visibility or public import changes.
   The three other modules are new. The existing node changes only `proof`,
   `proof_deps` and `proof_origin`. Verdict: unchanged public contract.
2. Compiled all four modules in dependency order with lcompile.py: no errors
   or warnings. Read the full ambient cone proof, both existing private
   categorical helpers, and the final compatibility/restriction calculation.
   The only delivery holes are the two named theorems listed above; no
   definitions or forbidden declarations were introduced. A fresh scratch
   module printed axioms of all four delivered theorems: only propext,
   Classical.choice, Quot.sound and expected sorryAx. Verdict: the two
   combining proofs are valid, conditional on the reported smaller holes.
3. Read the split statements and their proof docstrings against Stacks
   [08DG](https://stacks.math.columbia.edu/tag/08DG),
   [08FE](https://stacks.math.columbia.edu/tag/08FE) and
   [08BW](https://stacks.math.columbia.edu/tag/08BW). Checked empty opens,
   empty intersection/union, nested opens and both opens equal to X.
   The difference diagram fixes its two objects as direct-image constructions;
   the local triangular matrices remain invertible without a cover premise.
   Hom gluing fixes both ambient objects and asserts a map only on the union.
   Neither hole restates the original gluing assertion. Repeated searches via
   LeanFinder (compatible derived morphisms over a union), Loogle (split
   biproduct triangles), Mathlib grep (Mayer--Vietoris), and rg in both library
   roots. Results give ordinary sheaf gluing and the already-used categorical
   lemmas, not these derived statements. The covering difference and Hom
   theorems still require the missing ambient transport. Verdict: true,
   strictly smaller inputs; neither admits a short direct closure found here.
4. Checked the proof from its original upper hole down to object extension
   and fixed-object Hom gluing. The repaired import reuses the original
   helpers without applying their covering theorem. All three old direct
   proof dependencies are accounted for under No longer needed. The original
   unit has `realized.statement = []` and `realized.steps = [[]]`; its route
   is unchanged. No globally pruned module is claimed. Verdict: valid
   decomposition, one old hole closed and two holes added, not a net proof gain.
5. Checked all four node Lean statements verbatim against the declarations,
   and checked each proof_deps equals the union of its proof steps' uses.
   Read the proof steps, proof_origin, sources and new-node provenance/search
   records against the actual reduction and helper reuse. Verdict: consistent.

Changes in this second reading: appended this current review to supersede the
historical review. No further Lean, node, import or signature repair was needed.
