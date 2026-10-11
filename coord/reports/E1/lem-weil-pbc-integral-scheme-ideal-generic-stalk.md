## Reviewer fix (R-igs1221)

The delivered statement encoded the quasi-coherent ideal sheaf as an abstract
`(I : X.Modules) [I.IsQuasicoherent] (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]`
and the module stalks as `TopCat.Presheaf.stalk` of abelian groups. Quasi-coherent ideal
sheaves have one notion in this project: Mathlib `Scheme.IdealSheafData` with its ideal sheaf
`J.toModules` and inclusion `J.toModulesι` (upstream `IdealSheaf/Module`), as landed G1
e9aa3e2d8 and C1 7f9de320b use; module stalks are `RingedSpace.moduleStalkFunctor`
(def-pc-module-stalk-functor). The fix restates with `(J : X.IdealSheafData)` (quasi-coherence
is built into IdealSheafData, so no separate binder): field `IsField (X.presheaf.stalk
(genericPoint X))`; injectivity of the generic stalk map of `J.toModulesι`; (a) `J ≠ ⊥`
(`ideal_bot`: ⊥ is the zero ideal on every affine, so this is I ≠ 0); (b) `J.ideal U ≠ ⊥` for
every nonempty affine open U (= I(U) ≠ 0 by `range_toModulesι_app`); (c) the generic module
stalk of `J.toModules` is nontrivial; (d) the generic stalk map of `J.toModulesι` is
surjective, i.e. its image ideal is all of O_{Z,η}. The proof sketch is unchanged.

## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk` states
`AlgebraicGeometry.Scheme.integral_ideal_generic_stalk`. Its sole theorem has `sorry`
as proof; it introduces no definitions. The node is unchanged except for `lean`.
The server compilation completed cleanly (2.0 seconds, exit 0).

Hypotheses and clauses, in the order of the node:

- The scheme Z is `(X : Scheme.{u})`; its integrality is `[IsIntegral X]`.
  Mathlib's integrality includes nonemptiness and domains on nonempty opens.
- The generic point η is `genericPoint X`. Integral schemes are irreducible and
  sober, so this is exactly the unique point with closure all of X; it introduces
  no restriction or independent choice. `X.functionField` is definitionally
  `X.presheaf.stalk (genericPoint X)`.
- The sheaf of ideals is `(I : X.Modules)` with
  `(ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]`.
  A submodule of the structure sheaf is precisely a sheaf of ideals. Presenting a
  subobject by a monomorphism does not change which ideal sheaves are quantified over.
  `[I.IsQuasicoherent]` is the quasi-coherence assumption; there is no finite-type,
  coherence, Noetherian, separatedness, or affine hypothesis on X.
- The parenthetical injectivity of the stalk inclusion is the
  `Function.Injective` conjunct for the map of `TopCat.Presheaf.stalkFunctor` induced
  by `ι.val` through `PresheafOfModules.toPresheaf`.
- The generic local ring is a field: `IsField X.functionField`. This is a
  proposition asserting the field property of the existing ring, without choosing
  a new field structure.
- (a), I ≠ 0: `¬ IsZero I`, nonvanishing of the module sheaf, rather than inequality
  with one chosen zero object in a category.
- (b), nonzero sections on EVERY nonempty affine open:
  `∀ U : X.Opens, IsAffineOpen U → Nonempty U → Nontrivial (I.val.obj (op U))`.
  An additive module is nontrivial precisely when it contains a nonzero element.
- (c), nonzero generic stalk:
  `Nontrivial ↑(TopCat.Presheaf.stalk I.val.presheaf (genericPoint X))`.
  This is the recorded module-stalk dependency's colimit of abelian groups.
- (d), the stalk as an ideal equals the entire local ring:
  `Function.Surjective` of the same inclusion on abelian-group stalks.
  The target is the stalk of `SheafOfModules.unit X.ringCatSheaf`, i.e. O_X viewed
  as a module. Its canonical identification with the additive group underlying
  the commutative-ring stalk preserves germs. Surjectivity is exactly equality of
  the image ideal with the entire ring. This avoids adding an arbitrary stalk
  identification as a hypothesis or defining a second stalk.
- All four are equivalent: three conjuncts `(a ↔ b) ∧ (a ↔ c) ∧ (a ↔ d)`.
  Together these assert precisely the node's equivalence of all four predicates.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Spec`;
  affine opens use Mathlib `AlgebraicGeometry.IsAffineOpen`, the existing notion
  of being an affine scheme on an open subscheme.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.Topology.Irreducible`: `IsIrreducible`, `irreducibleComponents`;
  the generic point is Mathlib `genericPoint`, used by `Scheme.functionField`
  in `Mathlib.AlgebraicGeometry.FunctionField`.
- `Sheaf.AlgebraicGeometry.Coherent` (the recorded module for `pqf-def-coherent`):
  its module documentation explicitly identifies the quasi-coherent clause with
  Mathlib `SheafOfModules.IsQuasicoherent`, in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
  `RingedSpace.IsCoherent` is not imposed: that is another clause of the dependency,
  not an assumption of this item. The dependency record is usable as documented.
- `Mathlib.Algebra.Category.ModuleCat.Stalk`: the module structure on
  `TopCat.Presheaf.stalk I.val.presheaf x`, with `PresheafOfModules.germ_ringCat_smul`;
  `Mathlib.Topology.Sheaves.Stalks`: `TopCat.Presheaf.stalk` and `stalkFunctor`.
  `PresheafOfModules.toPresheaf` supplies the underlying abelian-group map.

Edge cases checked before writing:

- The empty scheme is excluded by the node's integral hypothesis itself, not by
  an additional hypothesis. The empty affine open is excluded only in (b), exactly
  as the node requires; its zero sections cannot invalidate (b).
- The zero ideal has all four predicates false. The unit ideal has them all true:
  every nonempty affine section ring of an integral scheme is a nonzero domain.
- A nonzero proper ideal of an affine domain (e.g. (t) in k[t]) is allowed: its
  generic localization is the whole fraction field. No global unit is demanded.
- No Noetherian condition is needed; localization of any nonzero ideal in a
  domain at the zero prime gives its fraction field. Non-quasi-compact schemes
  and arbitrary characteristics remain allowed.
- `Scheme.{u}`, `X.Modules`, and `AddCommGrpCat.{u}` use the same explicit universe.
  The binder u is declared explicitly; no auto-bound variables or independent
  test-object universe are used.

Source check: the local Stacks checkout is absent on this machine, so I read
[Stacks 01YL](https://stacks.math.columbia.edu/tag/01YL), especially the paragraph
using a nonzero ideal on the integral component and asserting the quotient's
support is proper. This agrees with the node's extracted generic-stalk fact.
No statement correction, missing notion, or disputed statement was found.
The docstring transcribes all four proof steps and their supporting nodes.

Searches (all service searches executed via the prescribed msearch.py):

- `leanfinder`: "A quasi-coherent ideal sheaf on an integral scheme is nonzero if
  and only if its generic stalk is the entire function field". Eight hits include
  integral stalk domains, `Scheme.IdealSheafData.support_eq_top_iff`,
  `IsAffineOpen.primeIdealOf_genericPoint`, and the field instance on function fields.
  None states all four equivalences for a quasi-coherent ideal sheaf.
- `loogle`: `AlgebraicGeometry.Scheme.IdealSheafData`. Twelve hits give the ideal
  sheaf data structure and its algebraic operations, not this theorem.
- `grep` via msearch: `genericPoint|generic.*stalk|stalk.*generic` in
  `AlgebraicGeometry/IdealSheaf`: zero hits.
- `leansearch`: "quasi-coherent ideal sheaf on integral scheme nonzero if and only
  if generic stalk is the whole function field": service unavailable (Internal
  Server Error); this is recorded as unavailable, not a mathematical search verdict.
- Local `rg` on the project and upstream for `IdealSheafData`, generic/stalk
  combinations, and this node id found no existing statement. I read the upstream
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` bridge and the landed
  `IdealModuleProductStalk` and `InvertibleModuleGenericStalk` modules. They treat
  related constructions, not these four equivalences. The abstract monomorphism
  encoding is already used by `IdealModuleProductStalk`; no copy of the ideal
  sheaf data or of the module-stalk functor was introduced here.
- Full proposed declaration name `integral_ideal_generic_stalk` was searched in
  `dag/lean_names_upstream.json`, Mathlib, upstream `WeilConjectures`, and landed
  `lean/Sheaf`: no hits.

## Second reading by E1

Independent verdict: PASS. I read the node copy, its six statement dependencies,
their recorded declarations, and the delivered Lean. There are no new definition
nodes or dependency modules, and no statement_change. No mathematical mismatch
was found; the Lean module and node record are preserved. This section is the
only change made in the second reading.

Source reading: the local Stacks .tex checkout is absent. I read the actual
[coherent.tex source](https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex)
at label `lemma-property-irreducible-higher-rank-cohomological` (current source
lines 3051–3162), and [Tag 01YL](https://stacks.math.columbia.edu/tag/01YL).
The enclosing devissage lemma assumes a Noetherian ambient scheme, a closed
irreducible subset, and coherent sheaves. The extracted fact here is about an
integral scheme and a quasi-coherent ideal alone: its affine-local calculation
uses a domain and localization at zero, with no Noetherian step. Thus the node's
general formulation and the absence of a Noetherian Lean binder agree. The
source's nonzero-ideal and proper-support uses occur in the third proof paragraph.
The node is an extracted auxiliary fact, not the entire devissage lemma.

The node's objects, hypotheses, and conclusions, listed before comparison:

1. An arbitrary scheme Z: `(X : Scheme.{u})`. PASS. I opened Mathlib's
   `Scheme` in `AlgebraicGeometry/Scheme.lean`: a locally ringed space with local
   affine charts. This is def-pc-scheme's recorded object, not an affine
   specialization.
2. Integrality of Z: `[IsIntegral X]`. PASS. The dependency def-pc-integral-scheme
   records Mathlib `AlgebraicGeometry.IsIntegral`; I opened its two fields in
   `Properties.lean`: nonemptiness and domain sections on each nonempty open.
   Its affine-local equivalent is exactly the dependency's meaning.
3. The unique generic point eta: `genericPoint X`. PASS. I read Mathlib's
   `IsIrreducible` and generic-point declarations in `Topology/Irreducible.lean`
   and `Topology/Sober.lean`, and `Scheme.functionField` in `FunctionField.lean`.
   Integrality supplies irreducibility, and schemes are sober and T0. The chosen
   point has closure the whole space and is the unique such point, so no
   independent generic-point binder is needed.
4. An ideal sheaf I contained in O_Z: `(I : X.Modules)` and
   `(ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]`. PASS. I opened
   `Scheme.Modules`, `SheafOfModules.unit`, and `PresheafOfModules.unit`:
   the target has section module O_X(U), with the structure-sheaf restrictions.
   An O_X-linear monomorphism into it presents exactly an ideal subsheaf;
   its image does not depend on presenting that subobject by a particular carrier.
   The already-landed IdealModuleProductStalk uses this same representation.
5. Quasi-coherence of I: `[I.IsQuasicoherent]`. PASS. I read dependency
   pqf-def-coherent and its module `Sheaf.AlgebraicGeometry.Coherent`, which
   explicitly delegates this clause to Mathlib `SheafOfModules.IsQuasicoherent`.
   I then opened that class in `ModuleCat/Sheaf/Quasicoherent.lean`: local
   presentations by free modules. On schemes this is the affine-local
   associated-module notion in the node. The coherent and finite-type clauses
   of that dependency are not hypotheses of this item.
6. The generic module stalk I_eta and its injective inclusion: the stalk is
   `TopCat.Presheaf.stalk I.val.presheaf (genericPoint X)`, and the first
   `Function.Injective` conjunct applies to the inclusion's stalk map. PASS.
   Dependency def-weil-pbc-module-stalk records precisely this abelian-group
   colimit. I opened `stalk`, `stalkFunctor`, `PresheafOfModules.toPresheaf`,
   the module instance in `ModuleCat/Stalk.lean`, and `germ_ringCat_smul`.
   The map acts on germs by ι and is linear for the stalk-ring action; no
   different stalk or unrestricted map is substituted.
7. O_{Z,eta} is a field: `IsField X.functionField`. PASS. The functionField
   abbreviation is literally `X.presheaf.stalk (genericPoint X)`. `IsField`
   asserts a property of that existing commutative ring. Its Field instance
   already exists in Mathlib, but the full conjunction and equivalences do not.
8. Clause (a), I is nonzero: `¬ IsZero I`. PASS. Categorical nonzeroness
   expresses failure to be the zero sheaf, independently of a chosen zero object.
9. Clause (b), nonzero sections on every nonempty affine open:
   `∀ U : X.Opens, IsAffineOpen U → Nonempty U → Nontrivial (I.val.obj (op U))`.
   PASS. The quantifier is universal, not existential. I opened `IsAffineOpen`
   in Mathlib `AffineScheme.lean`: it means the open subscheme is affine,
   equivalently a spectrum, as dependency def-weil-affine-spectrum requires.
   Since modules have zero, Nontrivial means that a nonzero section exists.
10. Clause (c), nonzero generic stalk:
    `Nontrivial ↑(TopCat.Presheaf.stalk I.val.presheaf (genericPoint X))`.
    PASS. This is the same stalk as item 6, with nonzeroness of its additive group.
11. Clause (d), the generic ideal equals the entire local ring:
    the final `Function.Surjective` predicate on the very same inclusion map
    as item 6. PASS. The target is the additive-group stalk of the rank-one
    structure module. Forgetting rings preserves this filtered colimit, giving
    the canonical germs-to-germs identification with the additive group of
    O_{Z,eta}. Surjectivity therefore says precisely that its image ideal is
    the whole ring, not merely that the domain is abstractly isomorphic to it.
12. Equivalence of all four clauses: the three conjunctions `(a ↔ b)`,
    `(a ↔ c)`, `(a ↔ d)`. PASS. These assert exactly mutual equivalence of
    (a)–(d). There is no quantifier moved into the affine-open predicate and no
    strengthening to a global generator or global section.

Edge cases independently checked: the zero ideal gives false (a)–(d), while
its stalk inclusion remains injective and the ring remains a field. The unit
ideal gives true (a)–(d). The proper principal ideal (t) on Spec k[t] also gives
true (a)–(d); clause (d) is generic surjectivity, not global surjectivity. The
empty scheme is excluded by integrality itself. The empty affine open is
excluded only by Nonempty U in (b). There is no index family or n parameter,
so empty indices and n = 0 introduce no cases here. Positive and zero
characteristics, non-Noetherian domains, and non-quasi-compact integral schemes
are all allowed. The universe `u` is explicitly declared and arbitrary;
Scheme, its section modules, and the abelian stalks all live at this universe.
An ideal subsheaf has the structure sheaf's universe up to equivalence, so this
adds no mathematical size restriction. No variable or universe is unbound.

Independent searches, using different wording from the worker:

- Prescribed msearch `leanfinder`: "A submodule sheaf of the structure sheaf on
  an integral scheme vanishes if and only if its stalk at the generic point
  vanishes". Eight hits, including integral stalk domains, germ injectivity,
  and `ModuleCat.Tilde.smul_stalk_no_nonzero_divisor`. No full statement match.
- Prescribed msearch `loogle`: `SheafOfModules.unit`. Twelve hits describe the
  unit module, free sheaves, and sections. I opened the unit definitions and
  the forgetful functor; they validate the existing representation rather
  than suggesting a new definition.
- Prescribed msearch `grep`: `support_eq_bot_iff|support_eq_top_iff|genericPoint`.
  I opened both IdealSheafData support criteria in Mathlib `IdealSheaf/Basic`.
  They concern the closed subscheme's support, not the module's generic stalk
  or the four equivalences, and do not replace this theorem.
- Prescribed msearch `leansearch`: "An ideal subsheaf on an integral scheme is
  zero exactly when its generic stalk is zero". Service returned Internal
  Server Error; unavailable, with no no-match verdict attributed to it.
- Direct rg over Mathlib IdealSheaf, upstream WeilConjectures, and the project's
  lean/Sheaf searched generic/ideal combinations and nonzero/stalk combinations.
  I opened upstream `Mathlib/AlgebraicGeometry/IdealSheaf/Module.lean`: it constructs
  the module attached to IdealSheafData and identifies its affine sections,
  but contains no generic-stalk equivalence. The invertible-ideal material
  requires locally principal ideals and is a different statement. I also read
  the landed IdealModuleProductStalk module; it handles products and quotients,
  not this nonzero-ideal criterion. No existing full statement was found.

H5–H9 checks: there are no definitions to be hollow and the sole theorem has
exactly `by sorry`. The module and theorem docstrings name Stacks 01YL and
carry the required blueprint tag. The four proof steps track the node's
fraction-field calculation, affine ideal criterion, sheaf locality argument,
and nonzero ideals in a field, including their dependency names. Imports use
only the allowed prefixes and supply the recorded quasi-coherent notion,
function field, and module stalk. The namespace has no Sheaf prefix; lines
are within 100 characters. The Lean signature in the node is verbatim the
file's signature. No statement correction or missing notion was needed.

Validation: second-reader server compilation using the prescribed scompile.py
on the absolute sandbox module path completed in 2.0 seconds, exit 0, with
no diagnostics. The initial relative-path invocation did not locate the
sandbox file; rerunning with its absolute path resolved that invocation error.
