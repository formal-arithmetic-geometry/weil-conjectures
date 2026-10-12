## What changed

Replaced the sole sorry in
`AlgebraicGeometry.exists_isIso_canonicalModuleBaseChange_of_isFlatOver` with a complete
Lean proof from two new intermediate statements. The existing signature and visibility
are unchanged, and all imports added to the item are proof-only.

The proof extracts the counit of the recorded derived pullback, identifies the recorded
underived functor with `tensorPullback` using its object/map equations, and explicitly
constructs the degree-zero comparison. It proves its comparison predicate directly.
It constructs a covering of S' indexed by affine pairs (V,W) with W contained in g^{-1}V,
applies the affine calculation through the restriction lemma, and proves global
invertibility using exact restriction, derived homology, the over equivalence, and the
existing sheaf-module isomorphism locality theorem. The private local-to-global helper
is fully proved; its argument adapts the already-proved helper in
`Sheaf.AlgebraicGeometry.ProjectionFormulaLocalityLocalToGlobal` to arbitrary derived maps.

New modules are
`Sheaf.AlgebraicGeometry.AffineRelativelyFlatCanonicalModuleBaseChange` and
`Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeAffineLocality`. Their named statements
split the flat affine computation from compatibility with affine open restriction and
transport of cartesian squares. The second concludes only invertibility of the restricted
map on a specified affine open and takes the affine calculation as a hypothesis. It does
not assert global invertibility. The item's proof supplies the affine calculation and
proves the covering and global detection itself.

The existing node's proof, proof_deps and proof_origin now describe this Lean proof.
There are no interface changes, forced adaptations or change records. The unit record
`sk-thm-picard-f-representable` has empty realized entries; its statement and route stay.

Validation: all three modules compiled together in import order, without warnings.
The dry check printed OK: compilation in import order and the per-declaration axiom
probe passed. Preflight passed except for the second reading reserved for the next worker.
Nothing was pushed.
Two file-wide elaboration options initially triggered an interface-change check; they
were removed, and the item compiled again without them.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_isIso_canonicalModuleBaseChange_of_isFlatOver`
(node `lem-pc-relatively-flat-canonical-module-base-change`). No sorry remains in the item.
`isIso_of_open_restrictions` is a private, completely proved helper.

Added two holes, each with a sourced proof in words and its own module and node:

- `AlgebraicGeometry.canonicalModuleBaseChange_isIso_affine_of_isFlatOver`
  (`lem-pc-affine-relatively-flat-canonical-module-base-change`): the bounded flat
  alternating Cech calculation on the chosen square over Spec A and Spec B.
- `AlgebraicGeometry.canonicalModuleBaseChange_isIso_on_affine_open_of_affine_cases`
  (`lem-pc-canonical-module-base-change-affine-locality`): identification of the
  restricted canonical composite with the affine calculation, including transport
  from an arbitrary cartesian square.

This is a decomposition, not a completed axiom-free proof: one original hole closed,
two new holes added (net -1 before any change of import closure). All existing holes
in dependency modules are unchanged. The two new modules keep the imports of the
statements used by their pending proof plans.

Edge cases: the affine lemma allows empty X and zero G, computed by zero complexes;
the restriction lemma allows empty W. The proved covering/detection argument works for
empty S' without a nonemptiness hypothesis, and no finite-cover condition is imposed
on S or S'. Neither lemma requires flatness of G over O_X or invertibility of c itself.
In particular one must not apply a flat-O_X degree-zero theorem from mere relative
flatness. An illustrative algebraic case is A=k[t], R=A[x]/(tx), G=R/(x), B=A/(t): G is
A-flat, but the ambient base change is not Tor independent, so the derived-to-ordinary
comparison need not be an isomorphism. The lemmas concern the full composite instead.

## No longer needed

Removed from the item's direct imports:

- `Sheaf.AlgebraicGeometry.BaseChangeMapCech`
  (`lem-pc-base-change-map-cech`).
- `Sheaf.AlgebraicGeometry.CechResolution`
  (`lem-pc-cech-resolution`).
- `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`
  (`lem-pc-flat-complex-derived-pullback`).
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`
  (`lem-weil-pbc-module-pullback-affine-sections`).

These dependencies move to the new affine-computation module, where they are still
needed by the pending argument. They are not globally pruned. No node or module of
the previous proof plan is claimed to be unnecessary overall; globally pruned: none.
The unspecified isomorphism theorem in RelativelyFlatDerivedBaseChange is not used
or imported: an isomorphism between the objects does not identify the canonical map.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies do not expose enough equations to finish the calculation
by direct application. `baseChangeMap_cech` only gives existential complexes, a map
between them, and a canonical-module-map predicate; its Lean conclusion has no
termwise comparison formula, no invertibility of the tensor map, and no equation
identifying that map with a localization of the given composite.
`cech_resolution_derived_direct_image` uses the unnormalised finite-index Cech
complex, which is not bounded above merely because the cover is finite. Thus its
current interface cannot directly supply the bounded alternating complex required
by `flatComplexDerivedPullback`. These are interface gaps, not reasons to reject
unproved dependencies. The new affine node explicitly records the remaining
bounded-model and canonical-map identification argument.

The base-change restriction lemma currently available for ordinary modules does
not itself state the derived-mate restriction equation. The new restriction node
records that derived compatibility as the remaining part of Step 1. Existing
restriction isomorphisms identify functors but need the mate/counit equations to
identify this particular map. No existing statement or definition was changed.

Searches: LeanSearch returned Internal Server Error; LeanFinder returned flatness
and localization lemmas, not this canonical derived statement; Loogle did not
recognize `Functor.IsLeftDerivedFunctor`. Mathlib and both library roots were
searched for the canonical predicate, affine/local isomorphism criteria and
left-derived counits. The actual queries/results are in searches.jsonl and the nodes.
Blueprint searches found the existing overall relative-flatness statement and
Cech lemmas, but no separate affine calculation or derived canonical restriction
statement. Online Stacks Tags 0A1D and 08IB were read; the latter explicitly reduces
canonical base-change invertibility to affine base opens. The local blueprint
literature files are absent on this machine; the imported source proof is recorded
in the existing DAG node and was read in full.

## New nodes

`lem-pc-affine-relatively-flat-canonical-module-base-change` states the affine
calculation (Steps 2--5 of the source). It keeps all geometric hypotheses, uses the
chosen pullback and a specified comparison, and records the Cech flatness,
section-pullback and canonical-map identification proof. Changing a derived counit
changes its degree-zero comparison by an invertible ordinary-target automorphism;
this does not assert that the derived comparison is itself invertible.

`lem-pc-canonical-module-base-change-affine-locality` states the restricted-map
conclusion on W mapping into V (Step 1 of the source), conditional on the affine
calculation. It records exact restriction, canonical mate compatibility, affine
chart transport and arbitrary-square transport. Its conclusion omits the global
covering and global detection, both proved in the item. Both new nodes are in the
item's chapter/unit and cite the existing blueprint's exact proof steps.

## Second reading by D3

1. **Existing interfaces: PASS after a whitespace repair.** Compared the delivered item
   with the repository version using `diff`. The only existing public declaration is
   `AlgebraicGeometry.exists_isIso_canonicalModuleBaseChange_of_isFlatOver`. Restored
   the indentation of `IsIso` in its signature; its complete signature is now byte for
   byte equal to the repository's. Its docstring, public imports, options and visibility
   are unchanged. There are no new definitions or interface changes. The two other
   delivered modules are new; their theorem signatures equal their nodes' verbatim
   Lean statements. The existing node differs only in proof, proof_deps and proof_origin.

2. **Proof and trust: PASS as a decomposition.** Independently compiled all three files
   in import order through lcompile.py, with no errors or warnings. Read the comparison
   construction: it extracts a left-derived structure of the already recorded functor,
   identifies E with tensorPullback on both objects and maps, and constructs c by the
   counit and the single-complex comparison. It does not choose an arbitrary object
   from a bare existence assertion or introduce a definition. The locality helper
   proves invertibility via every homology sheaf, exact restriction, the over equivalence
   and sheaf isomorphism locality. Scanned every delivered file: precisely the two
   reported public theorems have `:= by sorry`; no other sorry or prohibited declaration
   occurs. The scratch #print axioms checks and the delivery tool's per-declaration
   probes check the allowed axioms, with sorryAx expected from open dependencies.

3. **Split statements: PASS.** Read both statements and their complete docstring proofs.
   The affine lemma fixes affine bases and the chosen fibre square; the locality lemma
   assumes the affine calculation and concludes invertibility only after restriction to
   a specified W. They are strictly separate parts of the source argument, not a
   renamed global target. Checked zero G, empty X, empty W, identity base change and
   non-Tor-independent base change: none requires intrinsic O_X-flatness or invertibility
   of c. For arbitrary witnessing counits, right Kan extension uniqueness gives an
   automorphism of Lg'^*, and nonpositive derived pullback of G[0] gives the induced
   automorphism on H^0 = g'^*G; this changes c by an invertible target map. Thus the
   quantification over every comparison in the new lemmas is valid. Relative flatness
   supplies flat sections on the finite affine intersections, and the ordered
   alternating Cech model is bounded. Re-read Stacks Tags
   [0A1D](https://stacks.math.columbia.edu/tag/0A1D),
   [08IB](https://stacks.math.columbia.edu/tag/08IB) (only its local reduction is used),
   and [08HY](https://stacks.math.columbia.edu/tag/08HY).
   Independent searches used LeanFinder query “derived tensor cohomology flat base
   change quasi coherent sheaf affine cover” and Loogle
   `CategoryTheory.Functor.IsLeftDerivedFunctor`, as well as rg searches for canonical
   comparison, counit, base-change and affine restriction in both library roots.
   Loogle found leftDerivedUnique and the right Kan extension interface; neither closes
   the geometric calculation or mate restriction identity. Inspected the affine derived
   module model and restriction/composition declarations: these identify objects or
   functors but do not supply the required canonical map equation. The existing
   nonempty_derivedBaseChange_iso_of_isFlatOver likewise identifies objects only.
   No duplicate statement or quick closure of either split was found.

4. **Top-down reduction and pruning: PASS.** The item's proof supplies c, constructs an
   affine-pair cover and proves global detection, leaving just the affine computation
   and its restriction compatibility. Public imports are precisely statement imports;
   the added item imports are proof-only. The new modules retain proof-plan imports
   for their pending calculations. Compared old and new proof_deps: all four removed
   dependencies are listed under No longer needed, and remain in the affine module;
   no globally pruned module is claimed. The unit sk-thm-picard-f-representable has
   empty realized entries and its record and route are unchanged. This delivery closes
   one hole and adds two, net -1 before import-closure changes; it is not an axiom-free
   proof of the target.

5. **DAG agreement: PASS.** Checked every new node's required fields, source, chapter,
   unit, blueprint provenance, status, creation record and verbatim Lean signature.
   Each proof_deps is the union of its proof steps' uses. The item's three steps follow
   the explicit comparison construction, affine restriction on the constructed cover,
   and the proved homology-sheaf detection argument. Its new dependencies and origin
   describe that proof. No statement, statement dependency or unit record was changed.

Second reading changed only the existing signature's indentation and appended this
independent review. The proved code and the two mathematical splits were retained.
