## What changed

Proved `AlgebraicGeometry.Etale.restrictScalars_baseChange_comparison` without changing its
signature or docstring. The already proved arrow-category packaging remains unchanged.
The item imports `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsExchange` for its proof only.

Constructed canonical coefficient comparisons rather than choosing arbitrary endpoint
isomorphisms. Direct image commutes sectionwise with restriction. For inverse image, the
restriction/coextension adjunction and the inverse/direct-image adjunction exhibit the two
composites as left adjoints of the same right adjoint. `Adjunction.leftAdjointUniq` gives
the underived isomorphism, and exact derivation gives its bounded-below counterpart.
The direct-image comparison is the existing `rightDerivedFunctorPlusBaseChange` on the
sectionwise identity. Its invertibility is proved using the existing acyclicity criterion
and the new restricted-injective acyclicity statement. The derived source and target
isomorphisms are then explicit composites of these comparisons.

The item's proof transports the derived exchange equality across the coefficient comparison
for the single functor using naturality of base change. It applies homology to this square,
then uses naturality of the exact-functor homology comparison to obtain the asserted
commutative square. This is a real assembly of two smaller obligations, not an application
of the original assertion under a new name.

All four delivered modules compile locally in dependency order. New definitions contain
no `sorry`; proofs needed by definitions are named theorems. The two remaining theorem
bodies are exactly `:= by sorry` in separate modules.

## Proved and sorry left

The one original `sorry` is closed:
`AlgebraicGeometry.Etale.restrictScalars_baseChange_comparison`
(node `lem-sbc-base-change-restrict-scalars-comparison`).
`AlgebraicGeometry.Etale.exists_baseChangeHomologyMap_restrictScalars_arrow_iso` remains proved.
Also proved `AlgebraicGeometry.Etale.isIso_derivedLowerStarRestrictScalarsMap`
(node `lem-sbc-canonical-restrict-scalars-functor-comparisons`).

Exactly two new sorries remain:

- `AlgebraicGeometry.Etale.restrictScalars_injective_lowerStar_rightAcyclic`, in
  `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAcyclic`, node
  `lem-sbc-restrict-scalars-injective-direct-image-acyclic`. This is the acyclicity
  input for a single direct-image functor, independent of any cartesian square.
- `AlgebraicGeometry.Etale.derivedBaseChange_restrictScalars_exchange`, in
  `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsExchange`, node
  `lem-sbc-restrict-scalars-derived-exchange`. This asserts only equality of two
  morphisms for the already constructed canonical isomorphisms; it supplies no
  existential witnesses or endpoint invertibility.

The statements were checked mathematically for identity coefficient maps, quotient maps
(which need not preserve injectives), zero coefficient rings, empty schemes, zero sheaves,
and negative homology degrees. The acyclicity claim uses the underlying abelian sheaf and
claims acyclicity, not preservation of injectives. The exchange statement imposes neither
smoothness nor any base-change-isomorphism assumption. Homology transport works for all
integer degrees, including negative degrees. The original target and intermediate signatures
are unchanged.

## No longer needed

None of the original three public imports is removed: the base-change definitions,
sheaf restriction functor, and arrow category occur in the public statements.
The acyclicity import of the new functor-comparison module is proof-only and is now plain
`import`, rather than `public import`. Its proof dependency remains needed.
No pre-existing node or module is pruned. The original comparison node had no proof
dependencies to remove. Its two previously unnamed proof steps are now realized by the
canonical-comparison and exchange nodes.

No import of `SmoothBaseChange.Coefficients` is needed (and that module already depends
on the item). No unbounded coefficient-comparison theory is added. The proof only needs
bounded-below derived categories and the existing exact single/homology comparisons.
Exploratory cohomology imports are absent from the delivery.

## Where the brief, the DAG or earlier work was wrong

The comparison node's original two non-elementary proof steps had empty `uses` lists and
no Lean dependencies. Thus there was no existing named plan to apply directly. The delivery
makes both steps explicit, constructs the canonical endpoint data, and leaves only the
acyclicity and mate compatibility as independent proof items. The smooth-base-change unit's
coefficient-reduction route is preserved; no unit or chapter is bypassed.

LeanSearch returned an Internal Server Error for all three searches; this is recorded as
unavailable, not as evidence of absence. LeanFinder, Loogle, and Mathlib/source grep found
related scalar adjunctions but no matching sheaf derived coefficient comparison.

An attempt to close the acyclicity input via existing module/abelian cohomology and free-sheaf
derived-sections comparisons could not be compiled: the read-only source contains
`Sheaf.AlgebraicGeometry.EtaleFreeSheafDerivedSections`, but its object file is absent from
the compiled snapshot. Its declaration was not duplicated or compiled independently.
The incomplete experiment is kept only in `scratchpad/EtaleRestrictScalarsAcyclic.experiment.txt`,
which is not part of the delivery. The final acyclicity module has only its named theorem
and its complete sourced proof plan.

## New nodes

`lem-sbc-restrict-scalars-injective-direct-image-acyclic` supplies the direct-image acyclicity
input from the Stacks 03FD argument on étale slices, with 0D6J(3) as the derived comparison
reference. Its module is `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAcyclic`.

`lem-sbc-canonical-restrict-scalars-functor-comparisons` records the explicit underived,
derived, source, and target coefficient comparisons and the proved invertibility theorem.
Its module is `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons`.

`lem-sbc-restrict-scalars-derived-exchange` supplies the compatibility of those canonical
comparisons with the actual exchange transformation, following Stacks 07A7 and the natural
comparison of 0D6J. Its module is `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsExchange`.

No change record is needed: no existing definition, public statement, or public import
has changed; all three new modules are used through a proof-only import of the item.


## Second reading by V1

1. PASS: compared the item with the repository using `diff -u`. Both existing signatures
   and both existing docstrings are byte-for-byte unchanged; the arrow packaging is
   unchanged. The only item changes are its proof and a plain proof import. No existing
   definition or target statement changes, so no change record is required.
2. PASS: compiled all four modules locally in dependency order, including after the
   import repair. A scratch `#print axioms` check covers both original declarations and
   every new declaration. The underived comparisons, exact derived inverse-image
   comparison, and direct-image map use only propext, Classical.choice and Quot.sound;
   the remaining declarations additionally use sorryAx through the two listed open
   obligations. Exactly those two public theorem bodies contain `:= by sorry`; there
   is no hollow definition or forbidden declaration mechanism. Removed the scratch
   probe from the delivered modules.
3. PASS: read the two new sorry statements and their complete sourced docstring proofs
   against Stacks https://stacks.math.columbia.edu/tag/03FD,
   https://stacks.math.columbia.edu/tag/0D6J, and
   https://stacks.math.columbia.edu/tag/07A7. The first is single-functor acyclicity;
   the second is mate compatibility for specified canonical comparisons. Neither
   restates the existential degreewise comparison. Identity maps, nonflat quotient
   maps, the zero ring, empty schemes and zero sheaves introduce no exception; the
   homology assembly is valid for every integer degree. Independently searched with
   LeanFinder for injective module sheaves after forgetting coefficients, Loogle for
   adjoint uniqueness, and grep for coextension/acyclicity/comparison identities.
   Repository searches find existing underlying-abelian/global-section acyclicity
   and module-cohomology comparisons, but none is the arbitrary-f restricted-scalar
   direct-image acyclicity or canonical exchange statement. The former still needs
   the slice/evaluation and higher-direct-image bridge; it is not closed by applying
   a matching existing theorem. No few-minute closure was found.
4. PASS: read the proof downward. The item constructs endpoints, transports the
   single-functor comparison by base-change naturality, then applies homology and its
   coefficient naturality. Adjoint uniqueness and the existing derived comparison
   criterion supply the shorter available routes. Corrected the public acyclicity
   import in EtaleRestrictScalarsFunctorComparisons to plain `import`: it is used only
   in the invertibility proof. No old proof dependency is pruned (the original list
   is empty). Inspected dag/units/sk-thm-smooth-base-change.json: its realized lists
   are empty, and the coefficient-reduction route is retained without bypassing a
   unit step.
5. PASS: read all four delivered node records with the Lean modules. The item's
   proof_deps are the canonical-comparison and exchange nodes; the former depends on
   restricted-injective acyclicity, and the latter uses its canonical endpoints.
   Proof steps and proof_origin describe the actual construction. All three new nodes
   have source, searches, created/blueprint/unit/chapter and Lean records; the two
   open statements match their signatures and docstrings. No unreported old node is
   removed.

Second reading changed only the acyclicity import visibility and this report. The
original assembly proof and the new canonical constructions required no repair.
