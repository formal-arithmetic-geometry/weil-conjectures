## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion` states
`AlgebraicGeometry.smooth_at_point_iff_smooth_fibre_at_point`, with its only proof
postponed by `sorry`. No definition, helper, dependency repair, or statement correction
is needed. The source is Stacks Project, Morphisms, Tag 01V9,
`lemma-smooth-at-point`, equivalence (1) and (2); I read the statement and proof in
`literature/stacks-project/morphisms.tex`, lines 7263–7355. Flatness in condition (2)
is already an explicit hypothesis of the node, so the asserted equivalence is exact.

Clause-by-clause correspondence:

- Schemes and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Locally of finite presentation: `[LocallyOfFinitePresentation f]`.
- Point and its image: `(x : X)` and the expression `f x`, respectively. The image
  is substituted directly throughout; no independent point or equality is needed.
- The local homomorphism of local rings: `(f.stalkMap x).hom`, whose domain is the
  stalk of `S` at `f x` and whose codomain is the stalk of `X` at `x`. Scheme morphisms
  already supply its local-homomorphism instance.
- Flatness at this point alone: `(hflat : (f.stalkMap x).hom.Flat)`. This is the
  ring-homomorphism flatness predicate, meaning flatness of the target module over
  the source via this ring map, precisely the recorded dependency's stalkwise form.
  There is no global `[Flat f]` assumption.
- Smoothness at `x`: `∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)`. Here `U.ι` is the
  canonical open-subscheme inclusion, so the composite is exactly the restriction
  of the source of `f` to this neighbourhood, with target still `S`.
- The fibre over `s = f(x)`: `f.fiber (f x)`; its morphism to `Spec κ(s)` is
  `f.fiberToSpecResidueField (f x)`, with the actual residue field of `S` at `f x`.
- The point corresponding to `x`: `f.asFiber x`. Its definition uses the inverse of
  the canonical `fiberHomeo`; `fiberι_asFiber` states that its first projection is `x`.
- Smoothness of the fibre at that point: the right-hand existential over
  `V : (f.fiber (f x)).Opens`, with `f.asFiber x ∈ V` and
  `Smooth (V.ι ≫ f.fiberToSpecResidueField (f x))`. No condition is imposed on the
  rest of the fibre.
- “If and only if” is the displayed `↔`, with neither implication omitted.

The six statement-dependency records and their full source declarations/docstrings
were read. They are used through public imports:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`
  (`def-pc-scheme`).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`
  (`def-sbc-locally-finite-presentation`).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and
  `Flat.iff_flat_stalkMap`; the latter identifies its stalkwise formulation, used
  directly here as `(f.stalkMap x).hom.Flat` (`def-weil-flat-morphism`).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (`def-sbc-smooth-morphisms`). No relative-dimension or étale clause is needed by
  this item. The equivalence with formal smoothness plus local finite presentation
  is already recorded on that dependency, via Stacks 02H6.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberToSpecResidueField`,
  `asFiber`, `fiberHomeo`, `fiberι_asFiber` (`def-pc-scheme-fibre`).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` (`def-weil-residue-field`); the former is the residue
  field in the canonical fibre morphism's target.

All recorded proof-dependency modules are imported too, using plain imports when
not already public statement imports. In particular the global smooth-fibre criterion
is imported from `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`;
the ring-level converse from `Sheaf.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime`;
pointwise algebraic smoothness from `WeilConjectures.RingTheory.SingularIdeal`;
and the thickening and formal-smoothness interfaces from
`WeilConjectures.AlgebraicGeometry.Thickening` and
`WeilConjectures.AlgebraicGeometry.FormallySmooth`. The Mathlib matches for affine
squares, stalk localizations and residue fields, affine/open fibre products, principal
localization, smooth composition and the affine smoothness comparison are supplied
by `AffineScheme`, `ResidueField`, `Pullbacks`, `OpenImmersion`, `Morphisms.Smooth`
and `Morphisms.RingHomProperties`. No proof-dependency import is omitted for a cycle.
The docstring carries all five proof steps, including the local-flat affine reduction,
the correct residue-field tensor fibre, the kernel prime, the use of Algebra 00TF,
and the open-target thickening argument.

Edge cases checked mathematically before writing:

- Empty source: there is no `x`, so the pointwise assertion is vacuous, as required.
  Empty target likewise admits no such pointed morphism.
- Identity morphism: the stalk map is flat; the left side holds on the whole source
  and the fibre is `Spec κ(x)`, smooth over itself, so both sides hold.
- Over a field, stalk flatness is automatic. A nodal singular point has both sides
  false; smooth points have both sides true. Smoothness is not required away from
  the chosen point on either side.
- An inseparable algebraic field extension is flat and finitely presented but not
  smooth; its fibre over the sole base point is the same extension, and both sides
  are false. No perfect-field or characteristic hypothesis is introduced.
- The closed immersion `Spec k → Spec k[t]` at `(t)` has a smooth fibre but a nonflat
  stalk map. It is excluded exactly by `hflat`, showing why global-free deletion of
  flatness would be wrong.
- Arbitrary `Scheme.{u}` sizes are allowed with explicit `universe u`; no bound,
  finite type base, Noetherian, separation or geometric-point assumption is added.

Searches made before writing (through `msearch.py`, group NC, this item):

- LeanFinder: “A locally finitely presented morphism of schemes flat at x is smooth
  near x if and only if its fibre is smooth near the corresponding point”. Eight
  hits: global `isSmooth_iff`, relative-dimension definitions, standard-smooth
  charts, and local finite presentation of smooth morphisms. No pointwise-flat iff.
- Loogle: `AlgebraicGeometry.IsSmooth, AlgebraicGeometry.Scheme.Hom.fiber`.
  Zero hits; service reports unknown identifier `AlgebraicGeometry.IsSmooth`.
  The pinned local sources use the current name `Smooth` (the old name is deprecated).
- LeanSearch: “Smoothness on an open neighbourhood of a point of a flat locally
  finitely presented morphism of schemes is equivalent to smoothness of its fibre
  at that point”. Eight hits on global smoothness and `RingHom.smooth_def`;
  no exact statement.
- Mathlib grep: `smooth.*point|flat.*fibre|fiber.*smooth`, in `AlgebraicGeometry`.
  Two hits, in `Group/Smooth.lean` and `Morphisms/SmoothFiber.lean`, neither the node.
- Local `rg` of `lean/Sheaf`, upstream `WeilConjectures`, and Mathlib algebraic
  geometry for `SmoothAt|smoothAt|smooth_at|smooth.*[Nn]eighbo|[Nn]eighbo.*smooth`:
  existing algebraic smooth-at-prime predicates, smooth-neighbourhood consumers,
  Artinian lifting criteria and global-flat fibre criteria, no exact scheme iff.
- Local upstream node-ID search for `lem-trf-smooth-at-point-fibre-criterion`: no hit.
- Final exact-name/concept `rg` in `dag/lean_names_upstream.json`, project algebraic
  geometry and upstream algebraic geometry found no duplicate declaration.

The upstream pointwise lemma `Scheme.Hom.fiberι_mem_smoothLocus` assumes global
flatness, so it cannot replace this node's strictly local-flatness assertion.
`Algebra.IsSmoothAt` concerns formal smoothness of a localization and is not used
as a substitute for a scheme smooth neighbourhood.

Validation: `scompile.py NC lem-trf-smooth-at-point-fibre-criterion` compiled the
single delivered module successfully in both sandbox and library contexts, with
no error or warning. All variables and the universe are explicitly bound; all
Lean lines have at most 100 characters. No statement dispute or node fault found.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
