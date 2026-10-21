## What changed

Reconstructed the existing DAG route for both coefficient-flatness instances and the
finite-extension derived pushforward instance in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`.
Every existing signature, attribute, public import and non-hole construction is preserved.
The added constructions are private and proved; proof imports are private.
The generic finite comparison is checked with its coefficient rings abstract, then
specialized to the finite p-adic inclusion; this keeps concrete coefficient constructions
folded during elaboration without changing any public definition or signature.

A finite E-basis of F has continuous coordinates: restrict each coordinate to Q_ell and
apply finite-dimensional continuity over the complete field Q_ell. Its coordinate maps and
finite sum give inverse internal-module maps on continuous-function presheaves.
Monoidal sheafification gives the point finite-free isomorphism.
The existing generic `scheme_basis_from_point` theorem transports it to schemes and proves
exactness and coherent ordinary scalar-unit decompositions. The closure version already
supplies closure flatness. The existing generic `qbar_isIso_unit` theorem descends the finite
ordinary decomposition to arbitrary unbounded derived objects.

The mate/coproduct criterion identifies the canonical finite pushforward comparison with
the finite copower comparison. Additivity of derived pushforward makes that comparison
invertible; exact restriction reflects derived isomorphisms by the homology criterion.
The private finite-coordinate construction follows the established construction in
`Sheaf.Paper.CondensedFlatCoefficientCalculus`; importing that downstream file or
`Sheaf.FieldTheory.CondensedSubfieldBasis` would close an import cycle, as checked with
`tools/import_direction.py`.

Edge cases: the coordinate and copower arguments include the identity extension, rank zero
in the generic construction, and the empty scheme. They require neither completeness of
the algebraic closure nor properness of the scheme morphism for finite pushforward.
No new public declaration, new node or new mathematical assumption is introduced.
The point copower witness is packaged once to avoid repeatedly comparing the canonical
normed-field and intermediate-field structures. Local transparency settings keep derived
adjunctions folded; the concrete specialization has a documented heartbeat allowance.
The complete module compiled on the project server in 19.9 seconds. The delivery runs the
independent compilation and axiom checks against the current published build.

The three proof-instance change records are:

- `coord/changes/M3-preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap.md`
- `coord/changes/M3-preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl.md`
- `coord/changes/M3-isIso_derivedPushHom_padicSubfieldRingObjMap.md`

## Proved and sorry left

Closed three of four original holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`
  (`lem-sfb-subfield-flat`).
- `AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl`
  (`lem-sfb-qlbar-flat`).
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjMap`
  (`lem-sfb-subfield-push-iso`).

One original hole remains:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper`
  (`lem-sfb-qlbar-push-iso-proper`). Its signature and sorry body are preserved.

Holes added: zero. Split off: zero. Private helpers have no sorry. This is a partial proof
delivery, with the unresolved all-unbounded assertion explicitly reported below.

## No longer needed

No public import, declaration, module or DAG dependency is removed; no globally pruned
module is claimed. The three completed proofs follow the currently recorded DAG route.
In particular no filtered-colimit bridge is rebuilt for closure flatness: the existing
scalar-basis exactness clause supplies precisely the required finite-limit preservation.
The dependency providers retain their own imports and obligations unchanged.

## Where the brief, the DAG or earlier work was wrong

The current source contains four sorries although the node records and landed M4 change
records describe proofs of three of them. This delivery reconstructs that recorded argument
against the current source interfaces rather than assuming that stale audit implies a proof.

The proper closure comparison's second proof step asserts that properness supplies arbitrary
coproduct preservation of ambient unbounded derived direct image, but names no Lean result.
The source's module docstring instead asserts an ambient exceptional right adjoint. Neither
justification is supplied by the dependencies. The main-20261015 blueprint's
`sec-six-functors/sk-rem-sf-fullcd-scope.md` explicitly warns that an ambient exceptional
right adjoint and unrestricted coproduct continuity fail in general, and
`WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts` formalizes the
ordinary-coefficient warning. Its category is different from this precise internal
condensed-coefficient category, so no counterexample to this exact instance is claimed.

The available `condensedSubfield_bounded_copower_comparison` only handles inputs with a
lower cohomological bound. The existing bounded comparison in
`Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`
has the same restriction. Proper localizing coproduct theorems apply to the localizing
constructible subcategory, with further geometric hypotheses; they do not supply the
missing ambient assertion for every scheme and every unbounded object.

The scalar-basis and mate argument reduces the missing step to copower continuity on each
unbounded input. Substituting either bounded or localizing continuity would change the
statement. Introducing an unproved universal ambient-continuity theorem would hide that
same mathematical gap and conflict with the blueprint warning. The upstream boundary
forbids removing the original declaration or weakening its signature. It is retained with
an explicit explanatory comment and reported as an unresolved original hole, not a proof.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
