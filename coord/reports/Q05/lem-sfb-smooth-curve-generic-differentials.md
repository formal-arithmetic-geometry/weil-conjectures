## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.SmoothGenericDifferentials` states
`AlgebraicGeometry.Scheme.Hom.smooth_curve_generic_differentials`, with a single
`sorry` proof. No definitions, additional nodes, dependency repairs, or statement
corrections are introduced. The original node changes only in `lean`.

Clause-by-clause correspondence:

- The field k is `{k : Type u} [Field k]`.
- The k-scheme Z and its structure morphism are `{Z : Scheme.{u}}`
  and `p : Z ⟶ Spec (.of k)`.
- The separated integral finite-type dimension-one curve condition is precisely
  `[IsIntegralCurve p]`. Its parent `IsVariety` supplies integrality,
  separatedness, local finite type and quasi-compactness. `[Smooth p]` is
  smoothness over k; no projectivity, properness, algebraic closedness or
  characteristic hypothesis is imposed.
- The unique generic point is the canonical `genericPoint Z`; `genericPoint_spec`
  certifies it has closure all of Z. Fixing this canonical representative does
  not restrict the node: scheme sobriety and T0 give uniqueness.
- F is exactly `Z.functionField`, definitionally the structure-sheaf stalk at
  `genericPoint Z`, with Mathlib's field instance. `[Algebra k Z.functionField]`
  together with `hk` specifies its canonical k-algebra structure, namely the
  composite k -> Gamma(Spec k, top) -> Gamma(Z, top) -> F. This is a presentation
  of the induced field structure, not an independent mathematical hypothesis:
  that composite's `RingHom.toAlgebra` always supplies it. An arbitrary action
  without `hk` would say the wrong thing.
- The source is `(RingedSpace.moduleStalkFunctor Z.toRingedSpace
  (genericPoint Z)).obj p.relativeDifferentials`. This is the existing module
  stalk with the actual structure-stalk scalar action, not a tensor replacement.
- The target is `Ω[Z.functionField⁄k]`, Mathlib `KaehlerDifferential`.
- `∃! α : source ≃ₗ[Z.functionField] target, ...` asserts existence and uniqueness
  among all F-linear isomorphisms satisfying the specified normalization.
- For every nonempty open W, the generic point belongs to W; conversely an open
  containing it is nonempty. Thus the binders `(W : Z.Opens)` and
  `(hW : genericPoint Z ∈ W)` cover exactly the nonempty opens, and
  `(a : Γ(Z, W))` covers every regular function. The left side is α applied to
  the module germ of `p.relativeDifferentialsDerivation.d (X := op W) a`.
  The right side is `KaehlerDifferential.D k Z.functionField` applied to the
  structure germ of a. Both germs use exactly the same W, point and membership.
- The two `Module.finrank ... = 1` conjuncts state the two dimensions. Positive
  finrank excludes infinite-dimensional spaces (whose finrank is zero).
  The two `Nontrivial` conjuncts explicitly retain both nonzero assertions.

Dependency declarations read and used:

- `Field` in Mathlib, the match of `def-weil-field`.
- `AlgebraicGeometry.IsVariety` and `IsIntegralCurve` in
  `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`.
- `AlgebraicGeometry.Smooth` in `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `IsGenericPoint`, `genericPoint`, `genericPoint_spec` in `Mathlib.Topology.Sober`.
- The integral-scheme clause of `def-sc-function-field` uses
  `AlgebraicGeometry.Scheme.functionField` from
  `Mathlib.AlgebraicGeometry.FunctionField`. The recorded
  `WeilConjectures.AlgebraicGeometry.FunctionField` is imported; its
  `Scheme.functionFieldOfComponents` is for the general component-product clause
  and is deliberately not substituted for the integral generic stalk.
- `Scheme.Hom.relativeDifferentials` and `relativeDifferentialsDerivation` in
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`.
- `PresheafOfModules.moduleStalkFunctor` in the recorded
  `WeilConjectures.Topology.PresheafModuleStalkFunctor`; for schemes the sanctioned
  sheaf specialization is `RingedSpace.moduleStalkFunctor` in
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`. Its object carrier is the
  same abelian presheaf stalk. This version exposes the CommRingCat stalk scalars
  needed by `Z.functionField` without a new definition or new assumption.
- `KaehlerDifferential`, `KaehlerDifferential.D`, and
  `KaehlerDifferential.linearMapEquivDerivation` in
  `Mathlib.RingTheory.Kaehler.Basic`.

Every stated proof-dependency module is imported, with plain imports for proof-only
material: `Sheaf.AlgebraicGeometry.Curve.SmoothCotangentGenericIsomorphism`,
`Mathlib.AlgebraicGeometry.FunctionField`, `Mathlib.AlgebraicGeometry.Modules.Tilde`,
`WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization`, and
`Mathlib.RingTheory.Etale.Kaehler`. Their declarations are respectively
`Scheme.Hom.smooth_curve_cotangent_generic_isomorphism`,
`functionField_isFractionRing_of_isAffineOpen`, `tilde`/`tilde.toOpen`/
`tilde.toOpen_res`, `Scheme.isLocalizedModule_affine_germ`, and
`KaehlerDifferential.isLocalizedModule_map`. Statement dependencies already imported
publicly are not imported again. The complete five-step proof is in the docstring.

Sources read: local Stacks `curves.tex`, lemma-generically-etale, especially its
first proof paragraph; `algebra.tex`, lemma-differentials-localize, part (2) and
its quotient-rule proof. Also read the current blueprint direct-image statement
and proof under `literature/blueprint/latest/blueprint/sec-six-functors-basics/`.
This item is an auxiliary lemma in the recorded curve route, not the unit itself.

Edge cases checked before drafting: the empty scheme and dimension-zero spectra
are excluded by integral dimension-one curves; empty opens are excluded precisely
by generic-point membership. Arbitrary nonaffine nonempty opens are included.
On the affine line, the formula sends d(t) to dt and d(1/t) to -t^-2 dt.
In characteristic p it sends d(t^p) to zero without asserting every nonconstant
function has nonzero differential. Imperfect fields are allowed: smoothness is
retained, and is not replaced by regularity. There is no hypothesis that the
scheme be geometrically integral. All universes and variables are explicit;
`autoImplicit` and `relaxedAutoImplicit` are false.

Searches (all through the authorized wrapper or read-only source searches):

- `msearch.py ... leanfinder "The generic stalk of relative differentials of a
  smooth integral curve is uniquely isomorphic to the one dimensional Kahler
  differentials of its function field compatibly with germs"`: eight hits,
  mostly standard smooth algebra freeness, not this normalized geometric result.
- `msearch.py ... loogle "KaehlerDifferential, finrank"`: zero hits; the service
  also reported unknown identifier `finrank`.
- `msearch.py ... grep
  "(functionField|genericPoint).*([Kk]aehler|[Dd]ifferential)|([Kk]aehler|[Dd]ifferential).*(functionField|genericPoint)"`:
  zero hits in Mathlib.
- `msearch.py ... leansearch "Generic stalk of differential sheaf is isomorphic
  to Kahler differentials of the function field"`: eight hits, including
  `ModuleCat.Tilde.stalkIso`, structure-sheaf stalk isomorphisms, and the
  differential presheaf object formula; none is the node statement.
- `rg` across `lean/WeilConjectures` and `lean/Sheaf` for differential/function-field
  and differential/generic-point combinations: found
  `finrank_kaehlerDifferential_functionField` in Curve/FiniteMapToLine (only the
  dimension clause), `differentialsToGeneric` in Curve/AdelicDifferentials (a
  sheaf map, without the unique stalk isomorphism or dimension conclusion), and
  `finiteLocallyFree_principalParts_differentials` in
  Sheaf/AlgebraicGeometry/Curve/VectorBundlePrincipalParts (a compatible stalk
  isomorphism with lattice properties, without uniqueness or dimension one).
  All were inspected; none states this whole node.
- `rg` for the item id in `lean/WeilConjectures` and
  `dag/lean_names_upstream.json` found no existing attachment.

Validation: `scompile.py Q05 lem-sfb-smooth-curve-generic-differentials <module>`
compiled both sandbox and library module modes successfully (2.2s and 2.1s).
The first probe identified a scalar-category interface mismatch; switching to
its sanctioned ringed-space specialization resolved it without changing the
mathematical statement. No new node faults or disputed statement were found.

## Second reading by Q05

Author self-check, not an independent agent review: the dispatcher explicitly
forbids starting other agents and assigns independent review to the maintainer.
I reopened both the original node and the final Lean file and checked the field,
curve and smoothness hypotheses, the function-field identification and canonical
base action, both stalks/germs, the universal open and function quantifiers,
uniqueness, both dimensions and both nonzero clauses as detailed above.
The only mismatch in the first draft was Lean's failure to identify ring-category
and commutative-ring-category stalk scalars in the presheaf functor interface;
the existing `RingedSpace.moduleStalkFunctor` fixed it. There was no mathematical
statement change. Independent maintainer review remains the delivery's review.
