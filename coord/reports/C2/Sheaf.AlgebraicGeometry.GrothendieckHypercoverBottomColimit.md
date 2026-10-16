## What changed

Replaced the sole proof hole in
`Sheaf.AlgebraicGeometry.GrothendieckHypercoverBottomColimit` without changing its
public statement, universes, hypotheses, or visibility. The proof uses the actual
injective-resolution section bicomplex, checks the signed total-flip and
refinement identities, and implements the finite descending staircase for
arbitrary source objects in the coefficient category. It proves that the
comparison images generate the target and that each comparison kernel is
contained in the supremum of refinement kernels. Degree one is monic directly.
AB5 on the filtered homotopy cohomology diagram then makes the displayed
`colimit.desc` monic and epic.

Added two modules. In the repair, the duplicate module-level `sigma_qs` and
`cofan_qcqs` declarations were removed from `GrothendieckHypercoverLocalPrimitives`;
the existing geometric argument is now kept as local proof terms inside
`hypercover_term_qcqs`, avoiding public/private duplicate declarations already present
in `Sheaf.Paper.FiniteSplitReplacementGeometry`. The module still proves the geometric
local-primitive detector: hypercover terms are qcqs, sheaf sections glue over
finite colimiting cofans, and the existing finite-refinement theorem converts
covering-sieve lifts into primitives on a refinement.
`GrothendieckEtaleLocalEpimorphism` states the one remaining general-coefficient
local lifting theorem. The original module imports the new local-primitive
module only for its proof; that module imports the local lifting theorem only
for its proof. No existing definition or public signature was changed.

Updated the original node's proof, proof dependencies, and proof origin to match
this route, and added nodes for both new public declarations. The unit's route
is preserved. The additional AB5 instance is scoped inside the colimit proof;
quasi-isomorphism helper instances are supplied locally from private lemmas.
There are no forced adaptations. The textual change to proof-scoping commands
is recorded in `coord/changes/grothendieck-hypercover-bottom-proof-scopes.md`;
no existing statement or public definition changes.

The current second reading additionally removes the redundant direct public
import `Mathlib.AlgebraicGeometry.Sites.Etale` from the new
`GrothendieckEtaleLocalEpimorphism` module. Its required site API is already
exported by the retained `GrothendieckAbelian.Sheaf` import.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck.isIso_colimit_comparison_positive`
(node `lem-weil-pbc-grothendieck-hypercover-bottom-colimit`). Its proof is complete
Lean, with no remaining `sorry` in that module.

The new declaration
`AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck.eq_zero_of_refinement_primitives`
(node `lem-weil-pbc-grothendieck-hypercover-local-primitives`) also has a complete
proof. Its finite-cofan gluing, qcqs arguments, kernel factorization, and
refinement glue are proved in the same module.

Added exactly one hole, and left no others in the delivered Lean files:
`AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck.eq_zero_of_locally_liftable_maps`
(node `lem-weil-pbc-grothendieck-etale-local-epimorphism`). This is a decomposition,
not an unconditional proof or a net reduction in the number of holes: one upper
hole closed, one lower hole added. The lower statement has no hypercovers,
complexes, resolutions, derived functors, or cohomology. It concerns only an
epimorphism of sheaves on a qcqs etale object and source maps admitting local
lifts.

What remains for that hole: formalize the filtered union of the subobjects
`L_C` defined by pointwise image membership on finite qcqs covering families;
prove that the union is a subsheaf, hence equals the target because the original
map is epic; pull this directed union back along the given source map; and use
finite products and pullbacks of image epimorphisms to produce the locally
liftable source maps. The theorem's docstring and node give the complete
argument, including empty covers. AB5 is used for filtered unions and their
pullbacks; arbitrary jointly epic families are not assumed stable under
pullback. I attempted the general-coefficient reduction in this session and
proved the intervening hypercover geometry and the whole staircase, rather
than handing on an unproved staircase statement.

The proof also uses existing finite-refinement, injective-row, resolution, and
filtered-model declarations. These were not changed or restated in this
delivery. In the current shared sources, both the finite-refinement theorem
`exists_refinement_solving_local_requirements` and the injective-row declaration
have proofs; any transitive obligations in those existing dependencies remain
outside this delivery. The final theorem depends on the single new local
lifting obligation as well as those existing dependencies.

Validation: all three delivered modules compile through `lcompile.py --all`.
No new definition contains a proof hole, and all private helpers are proved.
Scratch checks proved the new lifting statement when the map on sections is
epic, by pulling that map back along x, and for an empty etale object, where
the section objects are terminal. Both checks use only `propext`,
`Classical.choice`, and `Quot.sound`. The simultaneous lifting construction
for a finite family of epimorphisms also compiles with those permitted axioms, using a product and a pullback.
A separate module-coefficient check works under the usual local-surjectivity/sheafification assumptions. These checks
are not extra delivered obligations or claimed proofs of the general case.
The proof plan for the remaining general case explicitly uses matching-object
kernels and the colimit universal property; it never assumes a map from an
arbitrary source factors through one member of a filtered union.

## No longer needed

The current second reading removed the redundant direct public import
`Mathlib.AlgebraicGeometry.Sites.Etale` from
`GrothendieckEtaleLocalEpimorphism`; the retained public
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf` dependency supplies
the same site API. The scratch copy without this import compiles.

Removed provisional redundant proof imports from the bottom-colimit module:
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`,
`Mathlib.CategoryTheory.Limits.Connected`,
`Mathlib.CategoryTheory.Filtered.Connected`,
`Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`, and
`Mathlib.CategoryTheory.Subobject.Lattice`. From the new local-primitive module,
removed the provisional imports `Mathlib.AlgebraicGeometry.Limits` and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`. These APIs are already
available through needed public dependencies. Retained the total-complex
symmetry import and the limits-over import: removing them gives respectively
unknown signed-flip declarations and a missing preservation-of-coproducts
instance.

The current shared base also has direct proof imports of
`Sheaf.AlgebraicGeometry.GrothendieckHypercoverCohomology` and
`Sheaf.AlgebraicGeometry.GrothendieckHypercoverResolution`. These redundant direct
imports are removed: their APIs remain available through the needed comparison
cocone import, and their nodes remain proof dependencies.

The original public import of
`Sheaf.AlgebraicGeometry.GrothendieckHypercoverComparisonCocone` is retained.
The original node's planned dependency
`lem-sc-hypercover-bottom-refinement-descent`, module
`Sheaf.Paper.HypercoverBottomRefinement`, is not imported and was removed from
this node's proof dependencies. Its elementwise ModuleCat statement is replaced
here by the proved categorical staircase. Other parents still use that module;
this is removal from this item's route, not a claim that the whole module is
unreachable from every target. No existing module is withdrawn or globally
pruned. The resolution, comparison-cocone, injective-row, and homotopy-model
nodes remain needed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery was correctly rejected because its local-primitives module
introduced module-level declarations `AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck.cofan_qcqs`
and `...sigma_qs` duplicating the existing statements in
`Sheaf.Paper.FiniteSplitReplacementGeometry`. Those declarations are private in the
source module and therefore cannot be referenced by name from this module; the repair
inlines the needed proof terms locally, so no duplicate declarations are exported.

The planned bottom-refinement lemma is stated for `ModuleCat R`; it cannot be
instantiated with the arbitrary Grothendieck abelian category in this item's
unchanged statement. The proof must work with maps from arbitrary source
objects, permitting source changes. Neither a projective generator nor
commutation of a separator Hom functor with filtered colimits is assumed.

The raw category of refinements is not treated as filtered. The colimit argument
uses the existing filtered homotopy quotient and its cohomology diagram.

Mathlib's usual local-surjectivity criterion for epimorphisms is for concrete
coefficients with additional sheafification compatibility. It does not directly
prove the new general-coefficient lifting statement. Stacks Tags 00WL and 01H0
supply the image-subsheaf and hypercover local-primitive arguments for their
respective concrete coefficients. The extension using finite matching diagrams
and AB5 is explicitly agent-written, both in the new node provenance and in the
Lean docstrings. No stronger attribution to those sources is intended.

The delivery preflight classified an added file-local AB5 instance as a public
interface change. Its use is now confined to a `let` inside the private
colimit-monicity proof. The two new quasi-isomorphism helpers are private
lemmas rather than globally registered instances. No downstream adaptation
is involved. The checker also records the additional `open`, private-helper
`variable`, and per-lemma `omit` commands textually. Their scope and unchanged
public signature are documented in
`coord/changes/grothendieck-hypercover-bottom-proof-scopes.md`. The read-only
downstream scan found one external textual user of the public theorem,
`Sheaf.AlgebraicGeometry.GrothendieckHypercoverComparison`, which needs no
adaptation.

## New nodes

`lem-weil-pbc-grothendieck-hypercover-local-primitives`, module
`Sheaf.AlgebraicGeometry.GrothendieckHypercoverLocalPrimitives`, declaration
`AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck.eq_zero_of_refinement_primitives`:
proved from the existing finite-refinement theorem, the new local lifting
statement, and the sheaf axiom. It converts covering-sieve primitives to a
finite split refinement, and is strictly the local step of the staircase.

`lem-weil-pbc-grothendieck-etale-local-epimorphism`, module
`Sheaf.AlgebraicGeometry.GrothendieckEtaleLocalEpimorphism`, declaration
`AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck.eq_zero_of_locally_liftable_maps`:
the single new `sorry`, with the finite-cover image-subsheaf proof in its
node and docstring. It is a coefficient-category local lifting obligation,
strictly below the geometric primitive detector. Both nodes record three kinds
of Mathlib searches, exact Lean signatures, source provenance, and blueprint
ancestry. The proof-scoping command change is recorded in
`coord/changes/grothendieck-hypercover-bottom-proof-scopes.md`.

## Earlier second reading (a previous round; superseded)

1. **Signatures and accidental changes.** I diffed the delivered bottom-colimit
   module against the shared repository version and checked both newly added
   modules. The existing target declaration has the same name, universes,
   hypotheses, conclusion, and visibility. The two additional declarations are
   new split-off nodes, and the proof-scoping changes are covered by the listed
   change record. Verdict: unchanged existing interfaces and no undeclared
   statement change.

2. **Proof and axioms.** I compiled all three delivered modules with
   `lcompile.py --all`. The bottom-colimit and local-primitives declarations have
   no `sorry`; the only remaining hole is the named
   `eq_zero_of_locally_liftable_maps` theorem, exactly the split-off theorem
   listed above. I found no `axiom`, `unsafe`, `opaque`, `extern`,
   `implemented_by`, or hollow definition. Verdict: the delivered proofs
   compile, and the remaining open theorem is explicitly named and documented.

3. **Split-off statements.** I checked both new statements against the existing
   library by searching for equivalent declarations and by reading their exact
   signatures and edge cases (zero source, zero coefficients, empty covers, and
   identity refinements). The local-primitives theorem is the strict geometric
   reduction used by the staircase. The local-epimorphism theorem is the one
   strictly lower general-coefficient obligation and does not restate the target.
   Verdict: both nodes are true in the stated use and have the required
   provenance, searches, docstrings, and DAG records.

4. **Top-down route and pruning.** The target proof uses the comparison cocone,
   injective-row and resolution APIs, then the finite staircase, local primitive
   detector, and filtered AB5 image/kernel argument. I checked that removed
   imports are absent from the proof and are listed under “No longer needed”; the
   unit route remains represented by the comparison and refinement steps. Verdict:
   the route is coherent and pruned to proof-only imports.

5. **DAG agreement.** I compared the declarations and imports with the three
   node records. The target node records the staircase proof and its actual
   dependencies; each new node records its exact Lean declaration, split status,
   source, proof steps, searches, blueprint ancestry, and unit/chapter. Verdict:
   Lean and DAG metadata agree.

No second-reading repair was needed beyond this report section; the delivered
Lean files and node records were left unchanged after compilation.

## Second reading by C2

This is a fresh independent reading of the repaired delivery, including all
three Lean files, all three node files, the proof-scoping change record, the
current shared item, its dependencies, and the unit record. The earlier reading
above is historical and is not the review for this delivery.

1. **Existing interfaces: pass.** I diffed the item against the shared source
   and separately compared the complete text from `theorem
   isIso_colimit_comparison_positive` through its conclusion: it is byte for
   byte identical. Universes, surrounding class parameters, explicit `A`,
   visibility, and the public comparison-cocone import remain the same. The
   private staircase section ends before the public theorem. Neither new
   module exists in the shared source. There are no forced adaptations and no
   changed public definition. The existing node differs only in `proof`,
   `proof_deps`, and `proof_origin`. The additional scoping commands are covered
   by `coord/changes/grothendieck-hypercover-bottom-proof-scopes.md`.

2. **Proofs and axioms: pass, conditional on the listed open theorem.** I ran
   `lcompile.py --all` on the delivery: all three files compile without warnings
   (approximately 2, 3, and 6 seconds respectively). In separate scratch copies
   I appended `#print axioms` for every named declaration, including every
   private helper and definition, and compiled those copies in import order.
   Every helper has only `propext`, `Classical.choice`, and `Quot.sound`.
   The three public declarations additionally have `sorryAx`, as expected from
   the one open local-epimorphism theorem. A source scan found exactly its one
   `sorry`, no forbidden declaration or kernel-check bypass, and no hole in a
   definition. In particular the finite-refinement construction, injective-row
   result, signed flip, and private categorical staircase used here introduce
   no further axiom. The staircase and comparison objects are constructed from
   the given complex and canonical injective resolution; they are not arbitrary
   witnesses chosen from an open existence statement.

3. **New statements and remaining hole: pass as a decomposition.** I matched
   both new public signatures with their node statements and their exact Lean
   records. The primitive detector concerns a single exact differential pair;
   it is proved by kernel evaluation, the local-epimorphism detector, the proved
   finite-refinement theorem, and gluing on a finite coproduct. It is not a
   renamed colimit-comparison theorem. The sole open statement has only a
   sheaf epimorphism, a qcqs etale object, source maps and local lifts; it has
   no complex, hypercover, derived functor, or cohomology. I checked the written
   proof: finite qcqs covers give a directed family of local image subobjects;
   finite matching kernels and AB5 make their union a subsheaf. Epicity forces
   this union to be all of G. Pulling back that union along x and pulling back
   finite products of image epimorphisms gives the source maps tested by hkill.
   This argument uses the colimit universal property rather than a false
   assertion that an arbitrary map from B factors through one stage. No
   pullback stability of an arbitrary jointly epic family is assumed.

   I independently recompiled the scratch proofs for a pointwise epimorphism,
   an empty etale object, and simultaneous lifting through a finite family of
   epimorphisms. Their axiom lists contain only the permitted three axioms.
   The first case includes identity epimorphisms; zero sources and zero x are
   also immediate by testing the identity source with zero lifts. The empty
   coproduct is handled in the geometric gluing proof, with terminal sections
   on the empty scheme. These checks support the statement without claiming
   to close its general case. Its formal proof is not a few-minute repair.

   Fresh LeanFinder searches for local image subobjects over finite covers and
   source changes making cycles boundaries, a Loogle search for
   `CategoryTheory.Sheaf, CategoryTheory.Epi`, and grep searches in Mathlib,
   upstream, and `lean/Sheaf` found concrete-coefficient local-surjectivity,
   one-hypercover gluing, and private geometric helpers, but no duplicate of
   either new statement. These searches are recorded in `searches.jsonl`.
   The docstrings give complete natural-language arguments and identify the
   categorical extension as agent-written. I checked the cited
   [Tag 00WL](https://stacks.math.columbia.edu/tag/00WL) and
   [Tag 01H0](https://stacks.math.columbia.edu/tag/01H0): their coefficients are
   sets and abelian groups respectively, consistent with the limited source
   attribution in the report and node provenance.

4. **Top-down argument, imports and unit route: pass.** I read the finite
   induction, cycle/image argument, bounding-cochain/kernel argument, separate
   degree-one monicity proof, and final AB5 colimit-kernel argument. They use
   the actual comparison cocone and the filtered homotopy index, with source
   changes allowed throughout the induction. The proof does not assume that
   the raw refinement category is filtered. I compared the old and new
   `proof_deps`: the only removed node is
   `lem-sc-hypercover-bottom-refinement-descent`, already fully listed under
   “No longer needed”. Its ModuleCat statement cannot supply this item's
   arbitrary-coefficient argument. The other old proof dependencies remain
   used, and the sole added dependency is the primitive detector.

   I tested isolated scratch copies removing each retained import of
   `TotalComplexRowResolution`, `GrothendieckInjectiveHypercoverRow`,
   `TotalComplexSymmetry`, `LimitsOver`, and `EtaleDisjointCover`.
   Each fails with missing declarations or, for `LimitsOver`, the missing
   coproduct-preservation instance. The new local detector and refinement
   imports are used directly and are proof-only. An additional scratch check
   showed that the new local-epimorphism module compiles without its direct
   public import `Mathlib.AlgebraicGeometry.Sites.Etale`, because the retained
   Grothendieck-sheaf dependency exports that API. I removed this redundant
   import. The remaining public imports support statements or definitions.
   `dag/units/sk-prop-h2.json` has `realized.statement = []` and
   `realized.steps = [[]]`; its Kummer statement and step are untouched, and
   no realized unit node is removed or bypassed. No module is claimed to be
   globally pruned.

5. **DAG and counts: pass.** The original node records the implemented signed
   flip, finite staircase, image and kernel arguments, and filtered AB5 step.
   Its actual used dependencies agree with the Lean proof. Both new nodes
   have their exact signatures, source and agent provenance, proof steps with
   the stated dependency union, searches, split status, creation data,
   blueprint ancestry, and the item's chapter and unit. All dependencies have
   existing Lean declarations or the recorded Mathlib match. The counts are
   one original hole closed (`isIso_colimit_comparison_positive`), one new hole
   added (`eq_zero_of_locally_liftable_maps`), and no other delivered hole.
   `eq_zero_of_refinement_primitives` is proved conditionally on that lower
   hole. This is a decomposition with net zero holes removed, not a completed
   proof of the comparison theorem under the final axiom criterion.

**Changes in this reading:** appended this review with the independent
compilation, exhaustive axiom checks, edge-case checks, fresh searches,
import-removal checks, exact unit observation, and explicit conditional/net
count; removed the redundant direct public etale-site import from the new
local-epimorphism module and recompiled the complete delivered set successfully.
No proof, statement, or node repair was necessary. The initial dry run failed
only because the required fresh section with this exact heading was absent;
that report defect is repaired here.
