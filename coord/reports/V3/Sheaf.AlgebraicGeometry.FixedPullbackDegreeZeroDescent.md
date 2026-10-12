## What changed

Replaced the saved section-descent restatement with the existing `etaleSetSectionLift`.
The original theorem signature and public imports are unchanged. Its proof identifies H^0
with global sections, lifts the underlying set section on the terminal etale object,
uses the coefficient comparison, cancels the composition isomorphism, and transports
back by the degree-zero pullback formula and naturality.

Added `Sheaf.AlgebraicGeometry.AbelianPullbackGlobalSectionsComparison`, containing one
independent coefficient-comparison theorem. It assumes no inverse system and asserts no
finite-stage descent. Its docstring gives the source and complete proof in words.
No definition, target signature, or other module was changed. No forced adaptations.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.fixed_pullback_degree_zero_descent`
(node `lem-weil-pbc-fixed-pullback-degree-zero-descent`). Its module contains no sorry.

Added one hole:
`AlgebraicGeometry.Etale.exists_abelianPullbackGlobalSectionsComparison`
(node `lem-weil-pbc-abelian-pullback-global-sections-comparison`).
This is a decomposition, with one hole closed and one added, not a net hole reduction.
The comparison is only the coefficient and composition step; all finite-stage descent
is obtained from an existing theorem. No data definition chooses an arbitrary witness.

## No longer needed

Removed the following direct proof imports and their direct DAG proof dependencies:

- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`
  (`lem-weil-pbc-affine-etale-site-colimit`).
- `Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`
  (`lem-weil-pbc-etale-qcqs-cofinal-finite-coverings`).
- `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`
  (`lem-weil-pbc-affine-etale-site-topos`).
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
  (`lem-weil-pbc-limit-affine-transition`).
- `Sheaf.CategoryTheory.ColimitSiteSections`
  (`lem-weil-pbc-colimit-of-sites-sections`).

Also removed the parent's direct DAG dependencies on
`lem-weil-pbc-colimit-initial-full-subcategory`,
`lem-weil-pbc-filtered-colimits-commute-finite-limits`, and
`lem-weil-pbc-pretopology-sheaf-condition`.
Their roles in finite-cover descent are delegated to the existing set-section lifting
route. These are direct-route removals; some remain transitive dependencies of lifting,
so no claim is made that all leave the targets' import closure.
The earlier saved `fixed_pullback_degree_zero_sections` and its incomplete node are
not delivered. The original public TopologicalInvariance import remains unchanged.
The item's node is not a realized unit statement or proof step of `sk-thm-p1`;
no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The saved attempt left a section-level reformulation of the same descent claim, in the
item's module, with an incomplete node and insufficient proof documentation. It also
retained unused imports. This delivery instead isolates coefficient compatibility in a
new module and uses the existing set-section lifting theorem.

The saved final proof applied global-section injectivity directly to a cohomology goal,
which triggered expensive unfolding and the reported 60-second timeout. The corrected
proof applies H.equiv₀ injectivity first and uses explicitly typed naturality equations.
No tool or timeout limit was changed. LeanSearch was unavailable; LeanFinder, Loogle and
source searches were used. Source tags 00YV, 03CB and 03CC were read directly.

## New nodes

`lem-weil-pbc-abelian-pullback-global-sections-comparison`: a simultaneous bijection
between abelian global sections and set inverse-image sections on the base-changed
terminal object, with compatibility for a commuting triangle. Source: Stacks 00YV(2),
03CB and 03CC. The statement has no limit diagram and is strictly the coefficient step
of the argument. Checked identities, zero sheaves and empty schemes; in the latter two
cases the section sets are singletons. Searches found the module-coefficient analogue
and the underlying abelian inverse-image isomorphism, but no exact abelian Gamma formula.
No change record is required because existing signatures and visibility are unchanged.

## Second reading by V3

1. **Interfaces: pass.** Compared the delivered descent module with the repository
   using `diff -u`, and separately compared the theorem text through `:= by` byte
   for byte. The signature, docstring, visibility and original public import are
   unchanged. Only its proof and private proof imports change. There are no changed
   definitions, target statements, adaptations or change records. The comparison
   module is new; its signature matches its new node verbatim.

2. **Proof and axioms: pass as a decomposition.** Both modules compiled in import
   order through lcompile.py, before and after the review repairs (about 4 and 23
   seconds). A scratch copy with explicit `#print axioms` for both declarations
   compiled: each uses only propext, Classical.choice, Quot.sound and sorryAx.
   The descent module has zero sorry; the new comparison theorem is the sole added
   sorry. No forbidden declaration, holed definition or arbitrary data construction
   occurs. The proof obtains a comparison witness only inside a proposition proof.
   Its terminal object is isomorphic to the identity etale object, so its structure
   map is quasi-compact and quasi-separated as required by etaleSetSectionLift.
   The Over witness reverses to exactly f:i → j, and c.w supplies the required
   triangle equation. The equation from comparison and lifting is cancelled using
   Gamma.mapIso, then H.equiv₀ injectivity and the two naturality equations recover
   the original cohomology equality with the correct hom direction.

3. **Split statement: pass.** Read Stacks Tags 00YV(2), 03CB, 03CC and 09YQ directly,
   and opened EtaleInverseImageAlgebraicStructures, EtaleInverseImageAbelianLift,
   EtaleSetInverseImageCompositionUnits, EtaleSetSectionComparison and GlobalSections.
   The new theorem assumes only X and an abelian sheaf F; it compares coefficients
   for all individual scheme maps, with unit/composition compatibility. It asserts
   no finite-stage representative or inverse-limit result. Thus it is strictly the
   coefficient part, not the descent target under another name. For f or h an
   identity, the unit equations give the same terminal restriction; for an empty
   scheme or the zero sheaf the section sets are singletons. Arbitrary nonzero
   sheaves require a unit-compatible comparison, which the cited algebraic-structures
   theorem supplies. Ran a fresh LeanFinder query `abelian sheaf forget underlying
   type inverse image compatible unit global section terminal` and Loogle query
   `"sheafForget"`; inspected rg results throughout the local Sheaf and SixFunctors
   sources and upstream SixFunctors. They give terminal-section equivalences and
   the coefficient isomorphism, not the full displayed abelian Gamma equation.
   ModulePullbackSectionComparison is a proved ModuleCat analogue, not an immediate
   specialization to AddCommGrpCat; transporting sheaves, inverse images, Gamma
   and composition through a coefficient equivalence would itself need proof.
   No few-minute closure of the remaining coefficient compatibility was found.

4. **Route and pruning: pass.** Read the complete set-section lifting theorem and
   degree-zero pullback formula. They provide exactly the two reductions used by
   the Lean proof. All eight old proof dependencies missing from the new parent
   list are enumerated under No longer needed, including the three which had no
   direct import. All five removed direct imports are enumerated there. These are
   direct pruning claims, not claims that the modules leave the import closure.
   Read sk-thm-p1.json, including its statement, all proof steps and realized lists:
   neither the parent nor the new coefficient lemma realizes a unit statement or
   step. The curve-calculation/strict-henselian/geometric-stalk route is preserved.
   EtaleInverseImageAlgebraicStructures (unit sk-def-exchange) is used as an existing
   coefficient tool: it has the unit-compatible abelian/set identification; the
   present unit has no substitute for that fact. No maintainer tool_uses field
   was edited. New public imports are required by the new statement; its added
   algebraic-structures import is private and records the remaining proof route.

5. **DAG: pass after repair.** Parsed both node records. The existing parent differs
   only in proof, proof_deps and proof_origin, and its three steps describe the
   actual Lean argument. The new node has its source, self-contained statement,
   statement dependencies, three search kinds, creation record, blueprint ancestry,
   chapter/unit and verbatim Lean record. Its dependency union equals its proof_deps.
   The initial new-node plan cited etaleInverseImageAbelianLift without supplying
   its finite-limit preservation hypothesis. Changed it to cite the existing
   etaleInverseImageAlgebraicStructures theorem, which supplies both that property
   and the unit-compatible coefficient isomorphism, and added its private import.

Changes made by this second reader: repaired that coefficient proof dependency and
its private import; added the new module's blueprint tag; rewrote the new theorem's
proof docstring to define the three bijection factors, specify their direction and
explain composition by the unit equation and fixed-sheaf uniqueness. Updated the
node's first two proof steps accordingly. The completed descent proof was retained.
The result still closes one original hole and adds one strictly smaller hole: net
zero, a decomposition. No existing signature, definition or unit route changed.
