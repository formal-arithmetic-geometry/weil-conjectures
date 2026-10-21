## What changed

Filled both coefficient-flatness instances and the finite-extension derived pushforward
instance in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`.
All existing signatures, attributes, public imports and non-hole definition bodies are preserved.

The finite proof constructs continuous coordinates for a finite E-basis of F, proves the
inverse module morphism identities on continuous-map presheaves, and transports the
isomorphism through sheafification. The necessary private helpers follow the already proved
construction in `Sheaf.Paper.CondensedFlatCoefficientCalculus`; importing that downstream
module would form a cycle. The private generic `scheme_basis_from_point` construction in
`Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisSections` supplies exactness and coherent
ordinary unit decompositions. Its existing public closure-basis theorem supplies closure
flatness directly.

For finite-extension pushforward, the private generic `qbar_isIso_unit` lemma in
`Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisUnitOfSections` descends the ordinary unit
isomorphism to unbounded derived objects. Coherent scalar actions and
`isIso_iff_unitCoproductComparison` reduce the canonical comparison to a finite copower
comparison. Additivity of the right derived functor makes that comparison invertible.
Exact restriction reflects isomorphisms after derivation, by the homology criterion.
All additional imports are private proof imports. Single-file server compilation passed
without errors or warnings; the required delivery preflight provides the final checks. The three node proof records now follow
these constructions. No module is withdrawn and no new public declaration is introduced.

Edge cases: the generic coordinate and copower proofs include rank zero, the identity
extension, empty indexing families and the empty scheme. Finite intermediate fields have
positive actual rank, so the generic rank-zero case adds no assumption. No completeness of
the algebraic closure and no properness of the scheme morphism is used in the finite proof.

Change records required by preflight for the filled proposition-valued instances:

- `coord/changes/M4-preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap.md`
- `coord/changes/M4-preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl.md`
- `coord/changes/M4-isIso_derivedPushHom_padicSubfieldRingObjMap.md`

## Proved and sorry left

Closed three of the item's four original holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`
  (`lem-sfb-subfield-flat`).
- `AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl`
  (`lem-sfb-qlbar-flat`).
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjMap`
  (`lem-sfb-subfield-push-iso`).

One original hole remains unchanged:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper`
  (`lem-sfb-qlbar-push-iso-proper`).

Holes added: zero. Split off: zero. All new private helpers are proved. This is a partial
proof delivery, with no new mathematical assumptions or replacement statement.

## No longer needed

No existing public import is removed. No existing declaration or module is removed.
The unit route is preserved. The following are removed as direct proof dependencies
of the two flatness nodes; this does not claim that they are globally unused, and some
remain dependencies of the reused generic constructions or of other declarations.

lem-sfb-subfield-flat: `sk-def-sfb-module-objects`, `sk-def-sfb-sheaf-tensor`, `sk-def-sfb-pullback-from-point`, `def-weil-sheaf-of-modules-category`, `lem-weil-pbc-module-sheaves-limits-sectionwise`, `sk-def-sfb-change-of-scalars`.

lem-sfb-qlbar-flat: `sk-def-sfb-module-objects`, `def-weil-sheaf-of-modules-category`, `sk-def-sfb-sheaf-tensor`, `sk-def-sfb-change-of-scalars`, `def-pur-sheaf-tensor-product`, `det-def-sfb-qlbar-condensed-subextensions`, `sk-prop-sfb-qlbar-colimit-x`, `lem-sfb-subfield-coefficient-map-comp`, `def-sfb-subfield-coefficient-map`, `sk-def-sfb-pulled-back-coefficients`, `lem-sfb-directed-ring-sheaf-module-colimit`, `sk-def-sfb-ring-object`, `lem-weil-pbc-independent-sheaf-tensor-colimits`, `lem-sfb-subfield-flat`, `lem-weil-pbc-module-sheaves-colimits-forgetful`, `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`, `lem-weil-pbc-module-sheaves-limits-sectionwise`.

The closure-flatness proof uses the established scalar-basis exactness clause instead of
rebuilding the sectionwise internal-module/sheaf-of-modules bridge and filtered tensor
colimit argument. Finite flatness uses the existing generic copower construction after
constructing its finite point basis. In particular no import of
`Sheaf.CategoryTheory.DirectedRingSheafModuleColimit`,
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`,
`Sheaf.Paper.CompletedCondensedCoefficients`, `Sheaf.CategoryTheory.RingedSiteModules` or
`Sheaf.CategoryTheory.SheafTensor` is added. No globally pruned module is claimed.

## Where the brief, the DAG or earlier work was wrong

The finite-push node cited flatness alone for its finite-free decomposition. Its Lean
flatness declaration only returns `PreservesFiniteLimits`, so the proof must construct
the basis decomposition explicitly; the delivery does so without changing that signature.

For the remaining proper closure comparison, the available
`condensedSubfield_bounded_copower_comparison` and the existing bounded-below push theorem
only apply to bounded-below inputs. They do not prove the assigned statement on arbitrary
unbounded inputs. The node's assertion that proper direct image has an unbounded right
adjoint is an additional substantial input, not a consequence of the flatness or finite
comparison declarations. This delivery leaves that original hole and statement unchanged;
it neither assumes this missing continuity result nor asserts that the statement is false.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
