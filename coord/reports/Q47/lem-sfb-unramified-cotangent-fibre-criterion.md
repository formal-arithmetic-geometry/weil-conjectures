## Worker report

The module `Sheaf.AlgebraicGeometry.UnramifiedCotangentFibreCriterion` states
`AlgebraicGeometry.unramified_neighbourhood_iff_cotangent_fibre_zero`, with `sorry`
as its only proof. The node's natural-language statement and dependencies are unchanged.
No definitions, additional nodes, or dependency repairs are needed.

Source checked: Stacks Project, `literature/stacks-project/morphisms.tex`,
`lemma-unramified-at-point` (Tag 02GF), equivalence of (1) and (5), including its
proof. This is a lemma serving the inherited exceptional-fibre argument, not a
blueprint unit's own statement.

Hypothesis and clause correspondence:

- Schemes and their morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`; the explicitly
  declared universe `u` is arbitrary.
- Locally of finite type: `[LocallyOfFiniteType f]`. This imposes no
  quasi-compactness, finite presentation, Noetherianity, or flatness condition.
- The arbitrary point is `(x : X)`, without closedness or rationality hypotheses.
- An open neighbourhood is `∃ W : X.Opens, x ∈ W ∧ ...`.
- The restriction over the original target is `W.ι ≫ f`, and unramifiedness is
  exactly the recorded `IsUnramified (W.ι ≫ f)`.
- The relative differential sheaf is the recorded `f.relativeDifferentials`.
- Its local-ring module stalk is
  `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj f.relativeDifferentials`.
  This functor's object is the ordinary stalk of the module sheaf with its
  canonical action by `X.presheaf.stalk x`, the local ring O_(X,x).
- The residue field is the recorded `X.residueField x`; its quotient map is
  `X.residue x`. Mathlib defines this as the residue field and residue map of
  the stalk local ring, not a chosen field or scalar action.
- Base change to this residue field is
  `(ModuleCat.extendScalars (X.residue x).hom).obj` applied to the stalk.
  Its underlying module is κ(x) tensor_(O_(X,x)) Omega_(X/Y,x).
  `TensorProduct.comm` identifies this canonically with the node's order
  Omega_(X/Y,x) tensor_(O_(X,x)) κ(x), exactly as the recorded
  `def-weil-module-base-change` interface permits. There is no additional
  algebra structure quantified in the theorem.
- `Subsingleton` of that module says that it is the zero module: a module is
  inhabited by zero, so this is equivalent to every element being zero.
- The logical connective `↔` gives precisely both directions of the equivalence.
- No assumptions on equality, finiteness, separability, or perfection of the
  residue fields have been added.

Statement dependency declarations used, read with their source signatures and docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`. The node also records `QuasiCompact`,
  but only the local finite type part is a hypothesis here.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.residue`; the dependency's `Scheme.Hom.residueFieldMap` is not needed.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  already publicly imported through `UnramifiedMorphism` and `Differentials`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`,
  whose real definition is the conjunction of local finite type and an
  open-immersion diagonal.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `TensorProduct`,
  `LinearMap.baseChange`; the canonical ring-map-based tensor construction is
  `ModuleCat.extendScalars` from `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`.
- The auxiliary stalk interface is the existing
  `RingedSpace.moduleStalkFunctor` from
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`.

Proof dependency imports:

- `WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSections`:
  `AlgebraicGeometry.relativeDifferentials_affine_sections`.
- `WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed`:
  `AlgebraicGeometry.Scheme.Modules.finite_type_module_support_closed`.
- `Mathlib.RingTheory.LocalRing.Module`: `IsLocalRing.map_mkQ_eq_top` and
  `IsLocalRing.map_tensorProduct_mk_eq_top` (the Mathlib match for Nakayama).
- `Mathlib.RingTheory.Etale.Kaehler`:
  `KaehlerDifferential.isLocalizedModule_map`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffineOpen` basic-open and
  localization lemmas; the residue-field basic-open lemma is already public.
- The remaining proof dependencies are statement dependencies, already public.
- `lem-trf-relative-differential-sheaf-base-change` has no recorded Lean module
  or Mathlib match in the read repository, so there is no module for it to import.
  It is only a proof prerequisite, not needed to type this statement. Its role
  remains explicit in the theorem's five-step proof docstring.

Edge cases checked mathematically before writing:

- Empty source: no `x : X`, hence the universally quantified assertion is vacuous.
- Identity and arbitrary open immersions: relative differentials vanish and the
  whole source supplies an unramified neighbourhood.
- Affine line over a field, including its nonclosed generic point: the
  differential fibre has rank one and there is no unramified neighbourhood.
- A nontrivial finite purely inseparable field extension: the differential
  vector space is nonzero, and the one-point morphism is not unramified.
- Finite separable field extension: differentials vanish even though the two
  residue fields differ, and the morphism is unramified.
- A closed immersion from an arbitrary quotient A/I, including I not finitely
  generated and A non-Noetherian: the map is locally finite type (generated by
  the empty family as algebra) and unramified, with zero relative differentials.
  This checks that finite presentation was not silently imposed.
- No index type or independent smaller universe is used, and no local-ring or
  residue-field scalar structure is supplied as an extra assumption.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “A locally finite type scheme morphism has an
  unramified neighbourhood of x if and only if the relative differential stalk
  tensor residue field is zero”. Eight hits: scheme formal unramifiedness,
  ring unramified loci and their support characterizations, and a ring local
  criterion. None states this scheme-sheaf fibre/neighbourhood equivalence.
- `msearch.py ... loogle`: `AlgebraicGeometry.FormallyUnramified, TensorProduct`.
  Successful query, zero hits.
- `msearch.py ... grep`, Mathlib `AlgebraicGeometry`:
  `unramified.*(cotangent|[Ff]ibre|relativeDifferentials)|relativeDifferentials.*unramified`.
  Successful query, zero hits.
- `msearch.py ... leansearch`: “An unramified neighbourhood of a point of a
  locally finite type scheme morphism is equivalent to vanishing of the
  relative differential residue fibre”. Eight hits on formal unramifiedness,
  `Algebra.Unramified`, `Algebra.formallyUnramified_iff`, and the ring locus.
  No exact scheme-fibre statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the same regular
  expression and the node id found only related statements and proof citations.
  In particular `RationalUnramifiedCotangentCriterion` concerns rational points
  and a different cotangent-surjectivity condition; `ConormalSurjectionUnramified`
  cites the present criterion but does not state it.
- `rg` of both project roots and `dag/lean_names_upstream.json` for the new full
  declaration's short name found no existing declaration with that name.

No node fault or disputed mathematical statement was found.

Validation: the prescribed `scompile.py Q47
lem-sfb-unramified-cotangent-fibre-criterion` invocation passed on the final module
against the current server sources (1.8 seconds, 60-second file limit). The
server's cache attempt reported a disk-space error, but its automatic
confirmation against current sources succeeded with exit code zero and no
compiler errors or non-sorry warnings. The initial scalar-action inference
error was repaired by using extension of scalars along the actual residue map.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
