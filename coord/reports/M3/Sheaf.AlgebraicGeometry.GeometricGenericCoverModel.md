## What changed

Reduced `AlgebraicGeometry.exists_geometric_generic_cover_model` to two strictly
smaller statements, in new modules
`Sheaf.AlgebraicGeometry.CompatibleEtaleGenericFibreModel` and
`Sheaf.AlgebraicGeometry.ClosedFamilyGeometricFibreShrink`.
The first spreads only the supplied field extension and compatible generic fibre
maps. It has no closed cover or nongeneric irreducibility conclusion. The second
shrinks a fixed finite family of closed subsets with geometrically irreducible
generic traces. It neither constructs an étale model nor assumes a cover or proves
incidences. All existing signatures and visibility are unchanged.

The main proof constructs the closed subsets as `closure (a '' A i)` and proves
`a ⁻¹' C i = A i` using the embedding closure formula. It transports their generic
geometric irreducibility through the supplied isomorphisms, uses the existing
closed-cover shrinking theorem for their finite union, and intersects that open
with the irreducibility open. It proves closedness and coverage after restricting
the model. A fully proved private helper,
`geometric_fibre_subset_isIrreducible_of_isPullback`, handles geometric fibre
transport for any pullback square using residue-field maps and pullback pasting.
The generic incidences are proved by the range formula for `pullback.map`, followed
by the commutative square and injectivity of the open inclusion. The empty-index
case uses the already proved model-data theorem and empty-index elimination.

Added proof-only imports of the two new modules,
`Sheaf.AlgebraicGeometry.GenericFibreClosedCoverSpread`, and
`WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`.
Updated only proof, proof_deps and proof_origin of the main existing node.
No adaptations, definitions, target statements or public interfaces changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_geometric_generic_cover_model`
(node `lem-sbc-geometric-generic-cover-model`). There are no sorries left in the
item's module. The previously proved
`AlgebraicGeometry.exists_geometric_generic_cover_model_data` is retained.
The new private geometric-fibre transport helper is fully proved.

Added exactly two named public theorem holes:

- `AlgebraicGeometry.exists_compatible_etale_generic_fibre_model`, in
  `Sheaf.AlgebraicGeometry.CompatibleEtaleGenericFibreModel`, node
  `lem-sbc-compatible-etale-generic-fibre-model`.
- `AlgebraicGeometry.exists_open_closed_family_geometric_fibre_shrink`, in
  `Sheaf.AlgebraicGeometry.ClosedFamilyGeometricFibreShrink`, node
  `lem-sbc-closed-family-geometric-fibre-shrink`.

Both have exactly `:= by sorry`, sources and complete natural-language proof
sketches in their docstrings and nodes. This is a decomposition, not a completed
proof without sorry dependencies: one hole closed, two holes added, net -1.
The existing closed-cover and closed-avoidance dependencies are already proved.
All sandbox modules compile cleanly with lcompile.py; the dry run is the final
mechanical check. No axiom or hollow definition was introduced.

## No longer needed

No existing imports were removed; all are used by statements or proofs.
The existing model-data and closed-avoidance route is used for the empty-index
case. The former arbitrary-cover refinement node
`new-lem-sbc-geometric-generic-cover-model-refinement` remains unused and withdrawn;
it has no Lean module or declaration and was not reintroduced. No proof uses
`Sheaf.AlgebraicGeometry.GenericClosedSubsetFibreNonempty` or
`lem-sbc-generic-closed-subset-fibre-nonempty`: the requested incidence conclusion
is only at the generic point, and is proved directly without spreading incidence
images. Those modules may still be needed by the later cover-spreading theorem;
this is local pruning, not a claim that the whole target closure drops them.

## Where the brief, the DAG or earlier work was wrong

The main node had empty proof/proof_deps following withdrawal of a false
arbitrary-cover refinement. Thus there was no numbered dependency plan to
instantiate. Its docstring supplies the source argument. The proved model-data
theorem has no generic compatibility requirement; refining its arbitrary output
would repeat the previous mistake. This proof uses it only in the empty-index
case, where the remaining requirements are vacuous. For a nonempty index type,
the new compatible model gives an embedding of the supplied generic fibre, and
the exact generic-trace identity is proved before using irreducibility shrinking.

Edge cases checked mathematically: a field base and identity extension give the
identity fibre model, an empty X gives empty compatible fibres without choosing a
point, and an empty family permits the entire base in the shrinking lemma. An
empty member of a nonempty family cannot satisfy its geometric irreducibility
hypothesis. In particular the earlier Spec k / Bool counterexample with an empty
C_false is excluded by that hypothesis. Arbitrary overlap patterns of A are
allowed: each common point is lifted directly, so no equality of intersection
patterns or nongeneric incidence persistence is assumed. Nonreduced irreducible
bases are handled in the model via the generic nilradical and in shrinking via
reduction; no noetherianity or quasi-separatedness was added.

Searches: LeanFinder, Loogle and Mathlib grep found no exact scheme-level statement.
Both relevant LeanSearch calls returned HTTP Internal Server Error and are recorded
as unavailable. Repository search found the proved ring-level theorem
`exists_ne_zero_forall_isIrreducible_fiber` in
`WeilConjectures.RingTheory.GenericIrreducibility`, which assumes a noetherian domain
and an affine ring presentation and does not give the required general scheme
statement in one step. Existing generic finite étale model theorems concern
Noetherian integral bases or torsors; they do not specialize to this unrestricted
irreducible base. Online Stacks Tags 0551, 055G, 0559, 054X and 0557 were read.
The supplied unit record has empty realization lists; no unit statement, step or
route was removed or bypassed.

## New nodes

`lem-sbc-compatible-etale-generic-fibre-model` states only the étale model and
its compatible geometric generic fibre identifications. Source: Tag 0551's
monic-polynomial construction, used in Tag 055G. Its generic quotient is Spec L;
flatness supplies the generic point, and pullback pasting supplies the fibre
maps. Module: `Sheaf.AlgebraicGeometry.CompatibleEtaleGenericFibreModel`.
The node records actual searches, including the unavailable LeanSearch service.

`lem-sbc-closed-family-geometric-fibre-shrink` states only simultaneous geometric
irreducibility near a generic point for a fixed finite closed family. Source:
Tag 0559, second proof, and Tag 055G's finite shrinking, using Tags 054X and 0557.
Its proof sketch includes reduction, finite presentation shrinking, the affine
hypersurface reduction and finite factorization-algebra specialization argument.
Module: `Sheaf.AlgebraicGeometry.ClosedFamilyGeometricFibreShrink`.
The node records actual searches, including the unavailable LeanSearch service.
No change record is needed because no existing definition or statement changed.

## Second reading by M3

1. **Existing interfaces — pass.** Diffed the sole existing module against the
   repository and compared the raw signature slices of both public declarations:
   `exists_geometric_generic_cover_model_data` and
   `exists_geometric_generic_cover_model` are byte for byte unchanged. The data
   theorem's proof is unchanged too. The only existing node changes are `proof`,
   `proof_deps`, and `proof_origin`. No existing definition, visibility, target
   statement, or change-record-requiring interface was altered.

2. **Kernel proof and holes — pass as a decomposition.** Compiled all three
   modules together with lcompile.py, in import order, without errors or warnings.
   Read every proof in the item, including the private fibre-transport helper.
   In a scratch copy, `#print axioms` gave exactly propext, Classical.choice,
   and Quot.sound for the model-data theorem and the private helper. The main
   theorem and the two new statements additionally use sorryAx; these are the
   two explicitly reported named holes. Scanned the delivered files: no axiom,
   unsafe, opaque, implemented_by, extern, or sorry in data. The local witnesses
   obtained in the main existential proof do not define any public data. Closures,
   restrictions, and pullback maps are actual constructions. One original hole
   is closed by reduction to two new holes: this is not a completed proof of the
   item without sorry dependencies, and the reported net remains -1.

3. **New statements — pass.** Read the monic-polynomial model construction in
   [Tag 0551](https://stacks.math.columbia.edu/tag/0551) and the closed-family
   shrinking in [Tag 055G](https://stacks.math.columbia.edu/tag/055G), together
   with [Tag 0559](https://stacks.math.columbia.edu/tag/0559),
   [Tag 054X](https://stacks.math.columbia.edu/tag/054X), and
   [Tag 0557](https://stacks.math.columbia.edu/tag/0557).
   The compatible-model statement needs no finite type condition on X: construct
   the finite etale model from the specified finite separable field extension,
   then base-change by X. Flat generalization and its one-point generic fibre
   give the unique generic point. The residue-field identification must respect
   yη, and its base changes give exactly the commuting equality consumed by
   hCgeom. It asserts neither a cover nor irreducibility of nongeneric fibres.
   For the shrinking statement, the reduced closed subscheme of each C_i is
   finite type and quasi-compact over the reduced integral base; its field fibres
   embed with precisely the inverse-image sets in the statement. Tag 0559 thus
   applies without noetherianity or quasi-separatedness. Its finite intersection
   of opens supplies the conclusion, including nonemptiness. It asserts neither
   an etale model nor coverage or incidence. Both are true proper parts of the
   argument, not restatements of the item. Checked empty I (whole base), empty X
   (compatible model still exists; a nonempty family cannot meet hgeom), the
   field base with identity extension, and nonreduced irreducible bases. An empty
   member C_i is excluded by the identity field test in hgeom.
   Repeated searches with different wording: LeanFinder for realizing a function
   field extension as an etale generic residue field, and for open geometric
   irreducibility; Loogle with IsIrreducible/IsClosed/IsGenericPoint; Mathlib grep
   for geometricallyIrreducible and finite separable constructions. Searched
   repository and upstream Lean as well. No exact match was found. In particular
   `exists_ne_zero_forall_isIrreducible_fiber` requires a noetherian domain and
   ring presentation; `exists_spread_finite_separable_extension` also requires
   a noetherian domain; `GaloisCover.exists_generic_open_finiteEtale_model` requires
   an integral noetherian base and a torsor. These cannot close either unrestricted
   new statement in a few minutes. Both new statements have a docstring argument
   and a matching new node.

4. **Route and pruning — pass.** Read the proof top down. The embedding closure
   formula proves the exact generic traces a⁻¹(C_i)=A_i before any shrinking;
   the compatible isomorphisms then transport hgeom. The proved closed-cover
   theorem is used on the finite closed union, while the independent shrinking
   theorem supplies geometric irreducibility. Restriction to the intersection
   preserves the generic point. The helper's cartesian-square pasting handles
   arbitrary residue-field tests, and pullback.map's range formula lifts the
   original generic intersections directly. The empty-family branch uses the
   unchanged proved model-data theorem. Every import is used by a statement or
   by these proofs; all added proof imports are plain import. The old main node
   had empty proof_deps, so there is no old dependency omitted from 'No longer
   needed'. The withdrawn arbitrary-cover refinement is not used. Read
   dag/units/sk-prop-normal-form.json: its statement and two steps have empty
   realization lists, and the generic-model/closure/shrinking route remains
   within the component argument of Tag 055G. No unit realization or step changes.

5. **DAG agreement — pass.** Matched all four steps of the main node to the
   empty-family branch, compatible-model closure construction, simultaneous
   shrinking and restriction, and fibre/incidence transport respectively.
   proof_deps is exactly the union of their uses. The two new nodes have the
   item's chapter/unit, source, creation and blueprint ancestry records, actual
   search records, and Lean statements verbatim from their respective modules.
   Their proof_deps likewise equals the union of uses; the compatible-model node
   names the primitive-element Mathlib leaf. Their proof_origin records the
   source arguments, rather than claiming kernel-complete proofs.

**Second reader's changes:** clarified the shrinking theorem's docstring and its
node proof: finite presentation uses Stacks Proposition 29.28.1 on the reduced
scheme, not a bare flatness conclusion; supplied the denominator scaling for the
purely inseparable field generators and the monic coordinate change plus finite
factorization-algebra argument. No Lean statement, proof term, import, or hole count
changed. Added this independent reading and kept the proof/decomposition accounting.
