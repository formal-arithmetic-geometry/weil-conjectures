## What changed

Replaced the original sorry in
`Sheaf.AlgebraicGeometry.StrictLocalTotalCohomologyExchange` by a complete proof that
composes two comparisons. The target signature and original docstring are unchanged.

`StrictLocalAbelianTotalExchange` isolates the geometric strict-local computation with
abelian coefficients, using the general `derivedBaseChangeMapPlus` construction.
`ModuleAbelianStalkExchange` isolates the coefficient comparison for an arbitrary
cartesian square and arbitrary separably closed geometric point. It asserts neither
strict-local geometry nor an identification with total-space cohomology. Each is a new
module with one named public theorem left sorry. The main proof obtains their
witnesses, composes the two pairs of additive equivalences, rewrites by the coefficient
compatibility, and applies the geometric compatibility. No equivalences are chosen
independently and then assumed compatible.

The original node now records this two-part route and its elementary composition.
All three modules compile locally without warnings, with autoImplicit disabled.
The main module has no sorry. No existing signature, definition, public import, or
unit realization is changed.

## Proved and sorry left

Proved from the two named obligations:
`AlgebraicGeometry.Etale.exists_addEquiv_strictLocal_totalCohomology_exchange`
(node `lem-weil-pbc-strict-local-total-cohomology-exchange`). This removes the one
original sorry in the item; it does not close its transitive axiom dependency.

The only two sorries in this delivery are:

- `AlgebraicGeometry.Etale.exists_addEquiv_strictLocal_abelian_total_exchange`
  in `Sheaf.AlgebraicGeometry.StrictLocalAbelianTotalExchange`, node
  `lem-weil-pbc-strict-local-abelian-total-exchange`.
- `AlgebraicGeometry.Etale.exists_addEquiv_module_abelian_stalk_exchange`
  in `Sheaf.AlgebraicGeometry.ModuleAbelianStalkExchange`, node
  `lem-weil-pbc-module-abelian-stalk-exchange`.

Both statements elaborate without implicit auto-bound variables. Edge-case review:
q = 0 gives the ordinary section-pullback mate and the ordinary coefficient-forgetting
comparison. For the zero coefficient ring, both underlying sheaves are zero, so the
coefficient comparison remains valid. For empty total spaces, both cohomologies and
both higher-direct-image stalks are zero. Neither obligation needs properness, torsion,
quasi-compactness or quasi-separatedness. The coefficient comparison is stated for
any separably closed point, not just an algebraically closed field. The geometric
calculation uses locality of the ring homomorphism explicitly.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.DerivedExchangeTermwise`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`
- `Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`
- `Sheaf.Paper.InverseImageStalkGerm`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective`

The direct proof dependency `lem-weil-pbc-cohomology-pullback-functorial` and its module
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial` are not needed along this
route: its stated functoriality does not supply the required derived/Ext calculation.
The remaining old proof dependency nodes are retained below the new obligations;
removing their direct imports does not claim their mathematics is unnecessary.
No other node is claimed globally unreachable, and no unit-route node is bypassed.
The parent's only direct proof dependencies are the two new nodes.

Deleted the uncommitted duplicate flat sandbox module and the earlier uncommitted
`strict-local-total-cohomology-exchange-interface` node. That interface repeated the
whole target under another name and is not used or delivered.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt moved the whole target to a sorry interface. This was not a
reduction, independently of the delivery-tool error previously reported. Its node
also lacked the required source, proof, and complete Lean record. It is replaced.
Its claim that sorry dependencies were unusable was wrong: they may be imported and
used in this stage.

The existing `Etale.baseChange` API has extra monoidal assumptions, so it cannot
simply be instantiated with `AddCommGrpCat` using the current imports. The abelian
obligation instead uses `derivedBaseChangeMapPlus`. The coefficient obligation
includes compatibility between the module mate `baseChange` and that abelian
construction; the existing `baseChange_eq_derivedBaseChangeMapPlus` comparison applies
to the module coefficients. This bridge must be checked when that obligation is
proved, rather than silently identifying the maps.

`InjectiveModuleAbelianAcyclic` is stated for sheaves of modules over a constant ring
of size u (with ULift), whereas the target uses ModuleCat-valued sheaves and a ring
of size u+1. The new coefficient obligation preserves the target universe and
category. Future work can use `ModuleSheafConstantRingEquivalence` and the newer
`EtaleModuleInjectiveForgetAcyclic`/`EtaleModuleCohomologyForget` modules; none of their
signatures alone states the needed exchange compatibility. The new node records
this comparison as a substantive remaining obligation, not an assertion that
forgetting preserves injectives.

The sources named by the DAG are not present in this clone's literature directory.
The Stacks pages for 03QO, 03FD and 095T were read online to check the cited argument;
no literature or source file in the read-only repository was changed.

## New nodes

`lem-weil-pbc-strict-local-abelian-total-exchange`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-strict-local-abelian-total-exchange.json`,
records the abelian strict-local calculation from 03QO and the map-on-stalks
calculation of 095T. Its module is
`lean/Sheaf/AlgebraicGeometry/StrictLocalAbelianTotalExchange.lean`.

`lem-weil-pbc-module-abelian-stalk-exchange`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-module-abelian-stalk-exchange.json`,
records the coefficient comparison using the acyclic argument of 03FD and the
termwise mate construction. Its module is
`lean/Sheaf/AlgebraicGeometry/ModuleAbelianStalkExchange.lean`.

Both inherit the parent's chapter, unit, and blueprint ancestry. Existing blueprint
and repository searches found related global-cohomology, inverse-image, and
strict-henselization statements, but none states either complete bridge. Their Lean
signatures are recorded verbatim after normalization. No change record is required:
all existing statements, definitions and public imports are unchanged.

## Second reading by J1

1. Compared the delivered main module with the repository version. The theorem signature and docstring are byte-for-byte unchanged; only the proof and proof imports changed. The two new modules contain the split statements documented above.

2. Compiled all three delivered modules with lcompile.py; compilation succeeds with no warnings. The main theorem has no sorry, axiom, unsafe, opaque, extern, or implemented_by. The two named split obligations are the only remaining sorries.

3. Checked both split-off statements against their node records, source descriptions, edge cases, and repository searches. They are strict intermediate comparisons and do not restate the parent target; neither duplicates an existing declaration.

4. The proof composes the two split obligations directly and is the shortest available route in the current library. The seven old proof-only imports removed from the main module are unused. The parent node's proof and proof_deps now match the written proof; the two new nodes record their proofs, sources, searches, and Lean declarations.

5. Checked the unit record and its realized statement and steps. The route stays below that unit and does not bypass any realized unit node.

Changed only the main proof/imports, the two new split modules and nodes, and this report. No statement or definition used by other modules was changed.
