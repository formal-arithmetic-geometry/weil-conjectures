## What changed

Proved `AlgebraicGeometry.sheaves_killed_by_n_zmod_modules` with its existing signature,
including literal uniqueness of the module-sheaf object over the fixed abelian sheaf.
All helper lemmas are private and proved; no new public declarations or definitions.

The proof follows the current DAG plan. A unital ring map sends integer constants to
integer scalars, proving the prescribed action and sectionwise annihilation. Every
additive map is linear after restriction to the constant ring presheaf; Mathlib's
`PresheafOfModules.restrictHomEquivOfIsLocallySurjective` extends this to the sheafified
ring, giving fullness. For existence, construct the constant-ring module presheaf using
`AddCommGroup.zmodModule`, `ULift.module`, and `ZMod.map_smul`, then apply
`PresheafOfModules.sheafify` with the identity abelian sheafification. This constructs
data on the original sheaf rather than choosing an arbitrary existence witness.

Private equality lemmas show that a module map over an abelian identity forces equality
of module structures and restriction maps. Applying fullness to that identity proves
literal object uniqueness. Sectionwise additive isomorphisms preserve annihilation,
which proves the essential-image claim. Fullness and faithfulness lift isomorphisms.

Proof imports are Mathlib's module-presheaf sheafification construction, ZMod modules,
and ULift modules. Public imports and all existing signatures are unchanged. The unit's
route is unchanged, and no consumer adaptations or change records are needed.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.sheaves_killed_by_n_zmod_modules`
(node `lem-weil-pbc-sheaves-killed-by-n-zmod-modules`).

Zero holes remain. Zero holes added. Zero statements split off.
All six clauses are proved from existing, proved Mathlib declarations. This is a proof,
not a decomposition onto further unproved statements.

## No longer needed

Removed the unused proof imports `WeilConjectures.AlgebraicGeometry.EtaleSheaves` and
`Sheaf.CategoryTheory.RingedSiteModules`. The latter's abbreviation is unnecessary:
the statement and proof use Mathlib's `SheafOfModules` directly. The former supplies no
lemma used here. No claim is made that these modules are globally unreachable.

The proof uses `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify`, rather than the
larger `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`: it needs the action
on an already fixed abelian sheaf, not the functorial sheafification adjunction.

No current DAG proof dependencies are pruned: the proof uses the group-level ZMod
leaf, the module-sheafification interface, and the stated definitions. In particular,
it realizes the current five-step DAG proof rather than the older eight-step argument
still recorded in the Lean docstring. The older finite-product and underlying-set
sheafification lemmas named in that docstring require no additional imports here;
the generic Mathlib module-sheafification construction already provides the action.

## Where the brief, the DAG or earlier work was wrong

The existing Lean docstring describes the older finite-product sheafification route;
the current DAG already replaces it by the direct module-sheafification interface.
The proof implements the current DAG. No mathematical statement was corrected.

The hypothesis `1 ≤ n` is preserved, although the constructed proof also works for
`n = 0`. For `n = 1`, the killed section groups are zero; the same construction applies.
It also handles zero sheaves, the empty scheme, and disconnected objects: it never
assumes sections of the constant ring sheaf themselves are constant.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
