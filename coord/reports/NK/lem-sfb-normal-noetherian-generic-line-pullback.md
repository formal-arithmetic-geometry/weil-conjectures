## Worker report

The delivery states `AlgebraicGeometry.normal_noetherian_generic_line_pullback` in
`lean/Sheaf/AlgebraicGeometry/NormalNoetherianGenericLinePullback.lean`.
Its only proof is `by sorry`; it adds no definitions, helper theorems, or nodes.
Only the item's `lean` field changes. No statement correction or dispute is needed.

The source was read in `literature/stacks-project/divisors.tex`, lines 6967--7073:
Tag 0BD7, `lemma-in-image-pullback`. Its five assumptions and conclusion agree with
the node. The module's declaration docstring contains all eight natural-language
proof steps from the node, including the affine proof of source integrality,
local unit factorization, saturation, both alternatives for openness, and gluing.

Clause-by-clause translation:

- Schemes Y and T and their morphism: `{Y T : Scheme.{u}} (f : Y ⟶ T)`.
- Both schemes locally Noetherian: `[IsLocallyNoetherian Y]` and
  `[IsLocallyNoetherian T]`.
- Integral base: `[IsIntegral T]`. Mathlib's predicate includes nonemptiness.
- Normal base in the precise local-ring sense in the node:
  `hnormal : ∀ t : T, IsDomain (T.presheaf.stalk t) ∧
  IsIntegrallyClosed (T.presheaf.stalk t)`.
  This uses the recorded inline normal-domain convention, with no new predicate.
- Flatness: `[Flat f]`. `Flat.iff_flat_stalkMap` identifies it with the node's
  stalkwise flatness condition.
- Every residue-field fibre is integral and nonempty:
  `hfibres : ∀ t : T, IsIntegral (pullback f (T.fromSpecResidueField t))`.
  `T.fromSpecResidueField t : Spec (T.residueField t) ⟶ T` is the canonical map,
  not an arbitrary field-valued point. `IsIntegral.nonempty` supplies exactly
  the stated nonemptiness, without a redundant additional hypothesis.
- Either quasi-compact or locally of finite type:
  `hfinite : QuasiCompact f ∨ LocallyOfFiniteType f`. Both branches remain.
  Mathlib's quasi-compactness agrees with testing inverse images of affine opens.
- The generic point is `TopologicalSpace.genericPoint T`, available from the
  integral base's irreducibility. Its fibre is the same residue-field pullback
  as above at that point. For an integral scheme the generic stalk is a field,
  so its residue field is canonically that field; this is precisely the node's
  K = O_(T,eta), with the canonical structure morphism.
- The invertible O_Y-module is `(M : Y.Modules) [M.IsInvertible]`, using the
  dependency's existing Zariski-locally-rank-one predicate.
- Generic triviality is `hgeneric : Nonempty (...)`, where the isomorphism is
  between `(Scheme.Modules.tensorPullback (pullback.fst f
  (T.fromSpecResidueField (genericPoint T)))).obj M` and
  `SheafOfModules.unit (pullback f
  (T.fromSpecResidueField (genericPoint T))).ringCatSheaf`.
  The first projection is exactly the map from the generic fibre to Y, and
  `SheafOfModules.unit` is its structure sheaf as a module over itself.
- The conclusion `∃ N : T.Modules, N.IsInvertible ∧
  Nonempty ((Scheme.Modules.tensorPullback f).obj N ≅ M)` supplies both the
  invertible module downstairs and an isomorphism f*N ≅ M. It asserts existence
  of an isomorphism, without selecting a trivialization or adding uniqueness.
- Every module pullback in the hypothesis and conclusion is the dependency's
  explicit tensor pullback, not inverse image of abelian sheaves alone.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`, including
  its `nonempty` and `component_integral` fields and irreducibility instance.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  with standard `IsDomain`, this is the dependency's inline normal-domain form.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.fromSpecResidueField`; the latter is Spec of the residue map followed
  by the canonical morphism from Spec of the stalk.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (publicly available
  through `Mathlib.AlgebraicGeometry.Pullbacks`): `Limits.pullback` and
  `Limits.pullback.fst`, with the existing scheme pullback instance.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; its public quasi-compactness dependency
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` supplies `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded
  dependency interface, publicly importing
  `WeilConjectures.AlgebraicGeometry.TensorPullback` and its
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`. Its object is actual
  inverse image followed by extension of scalars and sheafification.

All stated proof dependencies are imported without `public` when they are used
only in the future proof: torsion-free flat modules, affine fibre products,
function-field fraction rings, faithfully flat local maps, localization base
change, `Algebra.local_generic_unit_factorization`, scheme fibres, the flat
quotient-map theorem, finite type versus finite presentation over a Noetherian
ring, and openness of flat locally finitely presented morphisms. Flatness,
properties, pullbacks, invertibility, and tensor pullback also serve the
statement and thus their modules are public imports. No import cycle is added.

Edge cases checked before writing:

- An empty base is excluded by `IsIntegral T`, just as in the node. An empty Y
  over a nonempty base fails `hfibres`; integral fibres are nonempty.
- The identity family is allowed, and the conclusion can take N = M. The result
  does not assert uniqueness or require the line itself to be globally trivial.
- Over a field the generic fibre is the whole family up to its canonical
  isomorphism, so generic triviality has exactly the expected strength.
- Non-quasi-compact, locally finite-type families remain covered by the right
  branch of `hfinite`; no finite-type conjunction replaces the disjunction.
- Integral fibres need not be geometrically integral. There is no properness,
  separatedness, smoothness, or extra surjectivity assumption.
- The zero sheaf on the nonempty source is not invertible. No accidental
  subsingleton or zero-object trivialization is used.
- The universe u is explicitly quantified and arbitrary. The standard scheme
  module category and canonical fibre products introduce no size equality or
  extra smallness hypotheses. `autoImplicit` and `relaxedAutoImplicit` are false.

Searches for an existing statement (2026-10-24):

1. `msearch.py ... leanfinder` with query "An invertible sheaf trivial on the
   generic fibre of a flat morphism with integral fibres over a normal locally
   Noetherian integral scheme is pulled back from the base": 8 normalization
   hits (`normalizationDiagram`, `normalizationDiagramMap`, etc.); none states
   line-bundle descent.
2. `msearch.py ... leansearch` with query "An invertible module trivial on the
   generic fibre of a flat morphism with integral fibres over a normal locally
   Noetherian base is a pullback": 8 hits, including faithfully flat detection
   of zero modules, localization of invertible algebra modules, pullback of
   free sheaves, and restriction of stalks; none is this theorem.
3. `msearch.py ... loogle` with query
   `AlgebraicGeometry.Scheme.Modules.IsInvertible, AlgebraicGeometry.Flat`:
   upstream `IsInvertible` is unknown to the Mathlib search index (0 hits).
   Repeated with the Mathlib-only query
   `AlgebraicGeometry.Flat, AlgebraicGeometry.IsIntegral`: 4 hits, namely flatness
   over a one-point integral base and integrality under geometrically integral,
   flat, universally open maps; none states the required result.
4. `msearch.py ... grep` with regex
   `generic.*(invertible|[Ll]ine)|[Ii]nvertible.*generic|in_image_pullback`
   in `AlgebraicGeometry`: 0 Mathlib hits.
5. Direct `rg -n` with that regex in both `lean/WeilConjectures` and `lean/Sheaf`,
   and narrower searches for `generic.*trivial|trivial.*generic|0BD7|in-image-pullback`
   in their algebraic geometry directories: related divisor, valuation, smooth
   family and normal-base locality statements occur. None has this statement;
   `NormalBaseFibrewiseLineLocality` cites this very node in its proof plan and
   was read to confirm that it is a consumer, not an implementation.
6. `grep -rn` for this node id in `lean/WeilConjectures`: no match. The chosen
   declaration name was also searched in both library roots and
   `dag/lean_names_upstream.json`: no existing declaration.

Validation: the first server compile found only one overlong signature line,
which was wrapped. The corrected file passed the prescribed
`scompile.py` with no warnings under both sandbox (2.2 s) and library (2.7 s)
module identities. `deliver2.py --no-push` then printed OK: its preflight and
per-file compiles passed (dry-run commit 87808983c8e). No local Lean
build, global build, direct git command, or shared-repository edit is used.

## Second reading by NK

The dispatcher explicitly forbids starting another worker. This section records
my second reading with the node, Stacks source, and module open; independent
review is left to the maintainer as the brief specifies.

Rechecked the five Stacks hypotheses against the Lean binders and both clauses
of the conclusion. The fibre pullbacks use residue fields, not algebraic closures;
nonemptiness is part of integrality. The generic map is the first pullback
projection over `genericPoint T`, and the structure sheaf belongs to that same
pullback scheme. Normality is required at every base stalk, and the finite-type
alternative is a disjunction. Both pullbacks are tensor pullbacks. No mathematical
mismatch was found and no node field except `lean` was changed. The sole compiler
warning, an overlong line, was repaired without changing the signature's meaning.
