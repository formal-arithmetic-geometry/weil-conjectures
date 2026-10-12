## What changed

Proved `AlgebraicGeometry.Etale.finite_pushforward_H_one_lift_of_henselianLocalRing`
without changing its signature. The finite abelian constant-pushforward restriction is
surjective by the existing henselian H1 comparison, finite exchange, and the two edge-map
base-change declarations. A proved constant-sheaf comparison transports this to the
underlying module pushforward. The final proof lifts the class and uses adjunction unit
naturality and `cohomologyMap_map` to obtain the specified equality for arbitrary J and ψ.

Added `Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison`, proving that the
particular comparison adjoint to the underlying module unit is invertible. Its proof
composes Mathlib's Kan-extension and sheafification isomorphisms, checks their unit
factorizations, and identifies the composite with the displayed adjoint. This closes the
comparison gap of the earlier attempt without a bridge between the three module encodings.
All new proof imports are ordinary imports; the existing public imports are preserved.
Updated the item's node to follow the actual argument.

Both delivered modules compile cleanly with lcompile. The construction of the comparison
was also checked for the identity morphism, zero sheaf, zero coefficient ring and empty
scheme: no additional geometric or coefficient hypothesis occurs, and the same unit
factorizations apply. The finite lifting retains the properness and henselian hypotheses
needed by the existing H1 comparison. The unit sk-thm-p1 route is preserved: this is its
finite/torsor lifting subargument, not a replacement for its curve or henselian comparisons.

## Proved and sorry left

Proved the item's only original sorry:
`AlgebraicGeometry.Etale.finite_pushforward_H_one_lift_of_henselianLocalRing`
(node `lem-weil-pbc-henselian-finite-pushforward-h1-lift`).

Also proved `AlgebraicGeometry.Etale.isIso_moduleAbelianInverseImageComparison`
(node `lem-weil-pbc-module-abelian-inverse-image-comparison`).

No sorry remains in either delivered module, and no sorry was added. The proof uses the
existing stage-3 declarations
`bijective_cohomologyMap_one_constantSheaf_of_henselianRing`,
`cohomology_edgeMap_baseChange` and `bijective_edgeMap_baseChange`; their existing proof
obligations remain with their nodes. All private helpers and the private isomorphism
construction are complete.

## No longer needed

Removed the trial proof import `WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen`:
the finite edge-map assertions are supplied by the existing edge-map base-change interface.
No public import was removed.

The actual proof does not directly require these dependencies of the old plan:

- `lemma-constructible-pullback-constant`, module
  `WeilConjectures.ConstructibleSheaf.Defs`: no separate constant pullback rewrite is used.
- `lem-weil-pbc-finite-pushforward-cohomology`, module
  `WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen`: used below the edge-map
  base-change interface, not directly by this item.
- `thm-weil-pbc-finite-etale-lifting`, module
  `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale`: used below the existing H1
  torsor comparison, not directly; this module stays imported for the H1 comparison.
- `lem-weil-pbc-cohomology-pullback-functorial`, module
  `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`: source-library
  `cohomologyMap_map` supplies the naturality used here; no import of the broader
  Sheaf interface is needed. That node remains a dependency of the edge-map interface.
- `prop-weil-pbc-inverse-image-modules-exact`, module
  `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`: the precise ModuleCat-valued
  comparison is now proved from Mathlib, so this item's proof needs no import of this
  SheafOfModules-valued interface or its encoding bridge.

These are removals from this item's direct proof dependencies; the transitive uses noted
above and uses by other targets are preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt treated the missing concrete comparison as a tool failure and left the
item unchanged. The existing inverse-image exactness declaration is in the SheafOfModules
encoding, whereas this item uses sheaves valued in ModuleCat. The comparison can be proved
directly in the latter encoding by Mathlib's Kan-extension and sheafification comparisons.
Its naturality follows directly from adjunction naturality and the module unit.

Automatic search for the constant-module sheafification-preservation instance recursed
through the essentially-small-site transfer instance. Applying
`GrothendieckTopology.instPreservesSheafification` directly resolves it without raising any
heartbeat limit or changing a definition. LeanSearch was unavailable (HTTP 500); Loogle,
LeanFinder and source searches were recorded. No mathematical statement correction or
change record is needed.

## New nodes

`lem-weil-pbc-module-abelian-inverse-image-comparison`:
`lean/Sheaf/AlgebraicGeometry/ModuleAbelianInverseImageComparison.lean`, declaration
`AlgebraicGeometry.Etale.isIso_moduleAbelianInverseImageComparison`. This is a fully proved
structural comparison for every scheme morphism and every module sheaf. It contains no
henselian, finite, cohomological, or ψ-dependent lifting assertion. Its source is Stacks
03D2/03D3; its formal proof uses Mathlib's unit-characterized Kan-extension and
sheafification comparisons. No new proof obligation is split off. No change record.

## Second reading by Q1

1. Statement preservation: PASS. Diffed the item against the repository and checked
   the declaration table: its only existing theorem signature and docstring are
   byte-for-byte unchanged, all original public imports remain, and no definition
   used by another module changes. The other module is new and introduces only the
   fully proved comparison theorem. No statement change record is required.
2. Proof integrity: PASS. Compiled both modules in import order with lcompile, with
   no errors or warnings. Neither delivered file contains sorry, axiom, unsafe,
   opaque, implemented_by, extern, or a hollow definition. Scratch copies with
   #print axioms show only propext, Classical.choice and Quot.sound for the new
   comparison; the item additionally has sorryAx from the existing henselian H1
   comparison and edge-map obligations listed above. Thus this is a complete local
   reduction, not yet an axiom-free proof of the transitive closure.
3. New statements: PASS. No statement is split off with sorry. Read the comparison
   theorem and its unit-factorization proof in full: it proves invertibility of
   the particular adjoint in the item, not an unrelated isomorphism. Identity i,
   zero J, the zero coefficient ring and the empty scheme require no exception;
   all three unit identities hold in these cases. The finite lifting works for
   M = 0 and psi = 0 as well; no injectivity assumption on J was added. Independent
   Loogle, LeanFinder and grep searches, plus source searches in Mathlib, upstream
   and Sheaf, found the existing structural comparison ingredients but no theorem
   of this exact mate. Checked Stacks 03D2/03D3 and the finite lifting paragraphs
   of 0A5H against their online source pages.
4. Route and pruning: PASS after import cleanup. Read the lifting proof from its
   conclusion down: comparison surjectivity, finite constant restriction,
   henselian H1, finite exchange and the two finite edge maps. The old constant
   module dependency is the Mathlib leaf constantCommuteCompose and remains used.
   All five removed old proof dependencies are listed under No longer needed.
   The sk-thm-p1 realized nodes and its curve/strict-henselian route are unchanged;
   this only supplies its finite lifting subargument. Removed redundant ordinary
   Mathlib imports: FilteredColimits and PreservesSheafification from the item,
   and KanExtension.Preserves, FilteredColimits and PreservesSheafification from
   the comparison module. Both modules compile together without all five. The
   retained Finite.BaseChange import is necessary: removing it makes
   isIso_baseChangeMap_of_isFinite unknown. The other three ordinary imports
   provide the explicitly applied H1, edge-map and comparison declarations.
5. DAG agreement: PASS after metadata repair. Existing node changes are confined
   to proof, proof_deps and proof_origin, whose steps match the helpers and final
   proof. The new node has its source, complete proof steps, dependency union,
   searches, creation and verbatim Lean statement. Repaired its missing nearest
   blueprint ancestor to prop-weil-pbc-p1-acyclicity (as identified by the parent
   H1-image node), with the degree-one finite-lifting step specified, and added
   the independent LeanFinder search. No new mathematical obligation is hidden.

Second-reading changes: removed five redundant proof imports; repaired the new
node's blueprint ancestor and recorded the independent search; added this review.
No proof or existing statement needed repair.
