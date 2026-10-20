## What changed

Repair of reviewer C-49c1d at returned head `49c1d2feb`:

- 6/C1(a): parent proof step 3 cites both
  `lem-sp-scalar-extension-dual-evaluation` and
  `lem-sp-scalar-extension-dual-local-iso`, in the requested order.
- 6/C1(b): step 3 uses the exact requested text identifying dual evaluation,
  contravariant naturality, rank-one preservation and dual tower compatibility.
- 6/C1(c): parent `proof_deps` includes both missing nodes, in the requested order.
- B: tower `stmt_deps` includes `lem-sp-scalar-extension-dual-evaluation`,
  which owns `scalarExtensionDualMap` used by its recorded declarations.

The retained packet contains these repairs. This resumption checked each against
explicit assertions and compared the packet with current shared sources. For all
six delivered nodes, `proof_deps` equals the union of proof-step `uses`.
The repair changes dependency metadata and its explanation; the completed Lean
proofs and signatures are retained. Actual delivered direct hole count is zero.
Fresh server validation for this resumption: `lcompile.py --all` compiled all six
modules with exit code zero (10.0, 25.3, 8.0, 23.9, 13.4 and 11.4 seconds in import
order). A fresh source comparison confirmed the unchanged original theorem
signature and six relocated declaration bodies, allowing only the recorded local
irreducibility attribute between declarations. A scan found no direct holes or
forbidden declarations in the six delivered modules.

Relocated the six existing definitions and structures, unchanged, to
`Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions` and publicly reexported them from the
item. This avoids an import cycle with the new construction modules. The original theorem's
signature is unchanged.

`Sheaf.Paper.ScalarExtensionBinaryCoherence` completely proves normalized binary comparisons.
It explicitly constructs scalar-extension multiplication, both unitors, the associator, the
binary comparison and its inverse. The sheafification adjunction, tensor generation and tensor
descent prove their formulas, inverse identities, coherence and bifunctor naturality. It also
proves uniqueness of the normalized binary core, scalar-extension functor laws, and constructs
all powers recursively with naturality proved by two-step induction.

`Sheaf.Paper.ScalarExtensionDualTowerCore` constructs the explicit dual and tower maps
and proves their unit, binary and dual tower squares. The original theorem derives
its power tower square by induction and assembles its required data directly from
these constructions. The redundant intermediate comparison record is removed.
The local rank-one result
constructs the extended basis and coordinate maps and an explicit inverse to the dual
map on each trivializing slice. The two inverse identities are proved on tensor
generators. The cover-local isomorphism criterion gives the global dual isomorphism.

Change record: `coord/changes/invertible-tensor-scalar-extension-definitions.md`.

## Proved and sorry left

Closed the original hole in
`SheafOfModules.exists_unique_invertibleTensorScalarExtensionData`
(node `lem-sp-invertible-tensor-scalar-extension`) by constructing the normalized binary,
power, dual and tower comparison data. Original holes: 1; closed: 1; added: 0; net: 1.
No `sorry` remains in any of the six delivered Lean modules.

The resumed theorem axiom probe reports `propext`, `Classical.choice`, `Quot.sound`,
and `sorryAx`: this closes the item's proof from existing library declarations,
not all transitive library holes. In particular, the existing imported
`SiteTensorFunctoriality` module still contains three theorem holes. No new axiom
or hole is introduced by this packet.

The previously unfinished local rank-one result
`SheafOfModules.scalarExtensionDual_localIsomorphism`
(`lem-sp-scalar-extension-dual-local-iso`) now has a complete proof. Its private helpers
construct a local basis, its dual coordinates, the extended basis isomorphism, and the
inverse dual map. Tensor generation, naturality, and basis coordinates prove both
inverse identities. `Sheaf.isIso_of_coversTop` glues the local isomorphisms, while
`isInvertible_of_forall_over_unit` gives rank-one preservation.

The split-off `SheafOfModules.exists_scalarExtensionTensorCore` is now fully proved,
including `scalarTensorBinaryForward_inverse`, `scalarTensorBinaryInverse_forward`, the
associator and both unitor compatibility squares, bifunctor naturality and
`scalarExtensionTensorCore_subsingleton`. It contains zero holes.

Additional completely proved declarations: `SheafOfModules.scalarExtensionUnitIso_tmul`,
`SheafOfModules.ScalarExtensionTensorCore.unit_tmul`, `SheafOfModules.scalarExtension_map_id`,
`SheafOfModules.scalarExtension_map_comp`, `SheafOfModules.scalarTensor_second_id`,
`SheafOfModules.ScalarExtensionTensorCore.first_natural`, and
`SheafOfModules.ScalarExtensionTensorCore.power_natural`,
`SheafOfModules.scalarExtensionTowerIso_hom`, and
`SheafOfModules.scalarExtensionTowerDual`. The `scalarExtensionUnitRawIso`,
`scalarExtensionUnitIso`, `power` and `withPowers` definitions contain no holes and choose no witness from any unproved existence statement.

## No longer needed

No module is claimed globally pruned. The unlanded
`ScalarExtensionDualTowerCore` record and `exists_scalarExtensionDualTowerCore`
wrapper are unnecessary and removed: the parent uses the explicit constructions directly. The following original proof imports are removed:

- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`

The binary construction instead uses the independent-universe tensor descent theorem
`PresheafOfModules.sheafification_tensorHom_isIso`
(`lem-weil-pbc-tensor-local-bijection-universes`) and the sheafification adjunction.
The dual construction restricts the locally bijective sheafification unit directly,
so it needs no localized tensor restriction comparison. The three original public imports
(SiteTensorFunctoriality, InternalHom, LocallyFree) move verbatim to the publicly imported
definitions module and remain publicly available.

The parent proof no longer directly needs
`lem-pc-sites-sheaf-tensor-bilinear-universal`,
`lem-pc-sites-module-sheafification-bilinear-extension`,
`def-weil-presheaf-modules-sheafification`, `def-pur-sheaf-hom`,
`def-pur-localized-ringed-site`, `lem-sfb-localized-site-tensor-restriction`, or
`def-weil-sheaf-of-modules-category`: their construction work is isolated in the smaller nodes.
The three obsolete parent `tool_uses` entries for the two bilinear universal properties and
localized tensor restriction are removed; the delivered constructions do not use those three tools.
The parent still uses tensor functoriality for its induction.

## Where the brief, the DAG or earlier work was wrong

The recorded tensor bilinear universal property requires the site object, site morphism and
coefficient universes all to coincide. The recorded bilinear sheafification extension requires
coefficient and module universes to dominate both site universes. Neither signature applies
directly to this item's independent universes. Existing independent-universe tensor descent is
relevant, but supplies neither the complete normalized binary structure nor the local-dual API.
The retained tower induction had a reversed tensor-naturality rewrite. It is now forward,
with both morphisms explicit. The retained binary and parent modules had compiled within the 60-second limit.
Resumption found expensive expansion of scalar-extension and tensor construction bodies
while checking the comparison structures. The definitions module now keeps these bodies
locally irreducible during statement elaboration. A redundant intermediate comparison record caused repeated expansion of the same
constructions. It is removed, and the original data is assembled directly.
The tower isomorphism is irreducible and has a proved forward-component API,
which the unit, tensor and dual tower calculations use. Tensor induction uses
explicit component linear-map identities. The local-dual proof keeps the explicit dual
map locally irreducible, using its proved evaluation API; this avoids expanding the
construction during inverse calculations. Explicit linear-map identities and
selective transparency confine unfolding to the constructors that need it
(clean compile: 45.7 seconds).
The sectionwise constructors use explicit
rewrites through ring-sheaf wrappers, while the dual tower calculation keeps the construction values closed.
Every relocated signature and body was compared with current sources and is unchanged.
The consumer scan was refreshed: 602 transitive callers retain the same public interface.
The four other short-name matches are qualified uses of
`SemilinearSections.scalarExtensionSection`, a different declaration. All six delivered modules compile; the original theorem
compiles in 35.8 seconds and the tower module in 46.8 seconds. Full delivery validation
passed: deliver3.py --no-push reported OK at dry-run commit 28379bad1f.
Earlier submission attempts crashed in the delivery tool's temporary-worktree checkout;
their complete packet was retained. On resumption on 2026-10-20, the required current-source
dry run passed at commit `45e21ec1c2`. A fresh source comparison confirms the original
theorem signature and all six relocated declaration bodies are identical to current sources.
The preflight noted four axiom-probe timeouts (binary, evaluation, local isomorphism and tower
modules); it nevertheless reported that the packet compiles and passes preflight. A separate
theorem axiom probe compiled in 7.0 seconds, with the dependency qualification recorded above.
No launcher code was modified.

No false statement was found. Empty tensors (degree zero), degree one, arbitrary modules in the
binary construction, and the zero target ring are retained.
The explicit unit comparison uses only the sheafification adjunction and the ordinary tensor
right-unit equivalence; its normalization holds also for the zero ring. No flatness assumption is added.
The scalar-extension action is on the first tensor factor throughout.

## New nodes

`def-sp-scalar-tensor-comparison-data`: records only the relocated existing definitions, not a
new mathematical construction. Its six declaration bodies are unchanged.

`lem-sp-scalar-extension-binary-coherence`: the normalized binary construction is completely
proved, including its explicit inverse and all coherence/naturality squares. The power recursion
and naturality are proved in the same module. No `sorry` remains in this node.

`lem-sp-scalar-extension-dual-tower-core`: the explicit tower construction, its inverse,
unit/binary squares and the explicit dual tower identity. The original item derives
power tower identities by induction and assembles its original data directly.

`lem-sp-scalar-extension-dual-evaluation`: constructs the dual map through the locally
bijective sheafification unit on slices and proves its formula and naturality.

`lem-sp-scalar-extension-dual-local-iso`: proves invertibility of the explicit map and
rank-one preservation using explicitly constructed local inverse maps and the cover-local
isomorphism criterion. This module has zero holes. Independent universes and empty-cover
cases are retained.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
