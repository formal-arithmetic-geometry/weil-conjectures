## What changed

Filled seven original proofs in `Sheaf.Paper.SystemTensorMateArrows`:
`base_continuous`, `coefficient_existsUnique`, `direct_additive`,
`system_kInjective`, `laxTensor_existsUnique`, `directComp_existsUnique`, and
`Operations.ordinaryOpenUnit_isIso`.

The coefficient map is assembled from the constant-section maps at each quotient;
sheafification gives uniqueness. The tensor map is constructed from the presheaf
pushforward's lax monoidal map and the module-sheafification adjunction. Its pure-tensor
formula follows from the presheaf formula; sheafification and tensor induction prove
uniqueness. Direct-image composition uses fibre-product pasting and the scalar
normalization of the coefficient map.

The ordinary open-unit proof lifts the open-composition/base-change adjunction
from sites to module systems. Its invertible counit makes direct image fully
faithful; the adjunction-triple criterion gives the supplied open unit. The
coefficient identities are checked on constant sections. Local transparency
settings keep the coefficient construction from being repeatedly expanded.

The existing node's proof plan and proof dependencies now record these arguments
and the three retained obligations. No unit route is bypassed.

All helpers and proof imports are private. In particular, `commRingSheafify` is a
private instance, so this proof support adds no public declaration to importers.
No existing statement or definition was changed.

`coord/changes/H8-system-tensor-mate-proof-scopes.md` documents the private
instances and declaration-scoped commands flagged by the preflight. The three
downstream modules retain their interfaces and require no edits.

## Proved and sorry left

Closed seven of the ten original holes, in namespace `WeilConjectures.SystemTensorMate`:

- `base_continuous`
- `coefficient_existsUnique`
- `direct_additive`
- `system_kInjective`
- `laxTensor_existsUnique`
- `directComp_existsUnique`
- `Operations.ordinaryOpenUnit_isIso`

Three original holes remain, in the same namespace:

- `tensorOperations_nonempty`
- `Operations.alpha_existsUnique`
- `TensorOperations.deltaInv_isIso`

All three remain attached to `def-pur-system-tensor-mate-arrows`, with their original
statements and proof plans. No holes were added or split off. The delivery runs the
compiler and its complete declaration axiom audit.

## No longer needed

None. The original public imports support the retained interfaces and remaining
geometric and tensor steps. The new imports are private proof support;
no node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous packet declared a sheafification instance inside the public section.
Making it private repairs the delivery gate without changing any public interface.
The previous report's blocked axiom-audit status is superseded by this delivery.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
