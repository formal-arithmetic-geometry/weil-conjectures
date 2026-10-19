## Worker report

The delivery states `AlgebraicGeometry.normalization_field_extension_homeomorphism` in
`Sheaf.AlgebraicGeometry.NormalizationFieldExtensionHomeomorphism`, with proof `sorry`.
The item is unchanged except for its `lean` record. No new definitions, dependency repairs,
or statement corrections are needed.

Source read: `literature/stacks-project/varieties.tex`, lines 5026–5099, Tag 0C3N,
`lemma-normalization-and-change-of-fields`. It constructs the canonical comparison by
normalization functoriality and the fibre product, identifies its affine algebra map as
`A' ⊗ K → B'`, and proves it is a universal homeomorphism for arbitrary field extensions.
The node specializes this assertion to integral finite-type X. The Lean docstring includes
all eight steps of the node's proof, including nil kernel, finite coefficient descent,
separable-first reduction, Frobenius of the integral equation, and affine gluing. It also
explains the uniqueness characterization of the canonical map: on each reduced component,
a fraction a/s must map to the specified fraction because s remains a nonzerodivisor.

Hypothesis and clause correspondence:

- A field k: `{k : Type u} [Field k]`.
- An integral scheme X: `(X : Scheme.{u}) [IsIntegral X]`.
- X over k, of finite type: `(q : X ⟶ Spec (.of k))`, `[LocallyOfFiniteType q]`,
  `[QuasiCompact q]`. The explicit q is used throughout both base changes. The recorded
  finite-type node defines exactly these two properties, with no extra hypothesis.
- Any field extension K/k: `(K : Type u) [Field K] [Algebra k K]`; its map of spectra is
  `Spec.map (CommRingCat.ofHom (algebraMap k K))`. No finiteness, algebraicity, separability,
  perfectness, or characteristic condition is imposed.
- `X_K = X ×_k Spec K`: `pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))`.
- The function-field normalization and its map: `X.normalization`, `X.fromNormalization`.
- Y, the componentwise normalization of the reduction of X_K: `X_K.reducedNormalization`,
  and its map `X_K.fromReducedNormalization`. The dependency's real construction takes
  the reduced induced structure on every irreducible component, so it already ignores
  nilpotents and requires no additional reduction choice.
- Target `X^ν ×_k K`: `pullback (X.fromNormalization ≫ q)
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))`.
- Canonical comparison b: the unique morphism in the displayed `∃! b`. This is a theorem
  asserting existence and the characterization, not an arbitrary map supplied as data.
  It follows the same projection characterization used by the recorded separable
  normalization-field-change dependency. No new chosen normalization or comparison is
  introduced.
- Over X_K, induced by the normalization maps: the first equality says
  `b ≫ fst ≫ X.fromNormalization = X_K.fromReducedNormalization ≫ fst`;
  the second says `b ≫ snd = X_K.fromReducedNormalization ≫ snd`. Equality of these two
  projections is exactly equality of the induced maps to X_K by its pullback property.
  These equations determine the canonical b: on a chart fractions a/s have forced images,
  since s is a nonzerodivisor after field extension and reduction. Thus unique existence
  is the intrinsic characterization of the node's canonical comparison.
- Universal homeomorphism: `(topologically IsHomeomorph).universally b`. By the recorded
  definition, every scheme base change of b is a homeomorphism of underlying spaces.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`, nonempty and
  domain sections on every nonempty open.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap` for field extensions.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: read the current source with
  `scompile.py --source` because the older source checkout lacks it. Its module docstring
  explicitly specifies `pullback`, `pullback.fst`, and `pullback.snd` as the scheme base
  change and projections. These Mathlib constructions are used directly. The existing
  separable-comparison proof import already imports the older side module carrying the
  identical base-change conventions; importing the upstream duplicate as well is avoided.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `AlgebraicGeometry.Scheme.normalization`, `AlgebraicGeometry.Scheme.fromNormalization`;
  read their full definitions as relative normalization in `fromSpecFunctionField`.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`:
  `AlgebraicGeometry.Scheme.reducedNormalizationComponent`,
  `AlgebraicGeometry.Scheme.isIntegral_reducedNormalizationComponent`,
  `AlgebraicGeometry.Scheme.reducedNormalization`,
  `AlgebraicGeometry.Scheme.fromReducedNormalization`; read the full module.
- `Mathlib.CategoryTheory.MorphismProperty.Limits`:
  `CategoryTheory.MorphismProperty.universally`;
  `Mathlib.AlgebraicGeometry.Morphisms.Constructors`: `AlgebraicGeometry.topologically`;
  `Mathlib.Topology.Homeomorph.Defs`: `IsHomeomorph`. Read each full definition.

Already-stated proof dependencies are imported, including the componentwise affine-chart
comparison, reduced Noetherian total fractions, separable normalization-field-change,
power-generated-spectrum criterion, and separably-generated-implies-separable theorem.
The last is imported from its side module so that its separable-extension definition is
the same module already imported by the separable-normalization theorem, avoiding duplicate
upstream and side definitions. The full signature and proof docstring of each of these
interfaces was read. The current upstream field-theoretic sources were also inspected with
`scompile.py --source`. The proof dependency
`lem-per-reduced-total-fractions-field-extension` has no Lean record yet; no import is
invented for it. It is a proof prerequisite, not a missing notion in the present statement.

Edge cases checked before writing:

- X cannot be empty because the node assumes integral, and `IsIntegral` includes nonempty.
  No nonempty-open assumption appears in the final statement.
- K = k: the comparison identifies componentwise normalization with the base change of
  function-field normalization; unique existence allows the categorical pullback choices.
- Purely inseparable finite extension: X_K and the target can be nonreduced; neither has
  been assumed integral or reduced. For k = F_p(s), X = Spec(k[u]/(u^p-s)) and
  K = k(s^(1/p)), the comparison is the expected reduction map to a thickened point,
  a universal homeomorphism but generally not an isomorphism.
- Reducible base change: e.g. X = Spec C over R and K = C. The componentwise construction
  retains both components. There is no arbitrary choice of one component or function field.
- Transcendental extensions, arbitrary characteristic, and nonnormal X are included.
- The universe u is explicit and arbitrary and bounds all schemes and fields, as in the
  dependency normalizations and fibre products. No quantification over an independently
  smaller test universe occurs; universal homeomorphism tests every scheme in this universe.

Searches (2026-10-18 UTC; the wrapper logs the complete calls in `searches.jsonl`):

- `msearch.py ... leanfinder`, query: "Normalization of an integral finite type scheme
  after any field extension maps canonically to the base change of its normalization by a
  universal homeomorphism". Eight hits, headed by `Scheme.Hom.normalizationDesc` and
  relative-normalization properties; none states this field-extension theorem.
- `msearch.py ... loogle`, query:
  `AlgebraicGeometry.Scheme.normalization, AlgebraicGeometry.Scheme.Hom.normalizationDesc`.
  No hits; unknown identifier `AlgebraicGeometry.Scheme.normalization` in the Mathlib index.
- `msearch.py ... grep`, query:
  `normalization.*(baseChange|[Ff]ield|[Hh]omeomorph)|([Ll]ift|[Dd]esc).*ormalization`,
  Mathlib subdirectory `AlgebraicGeometry`. Five hits, all `normalizationDesc` and its
  equations in relative normalization. Read its full signature and docstring; it requires
  a pre-existing factorization through an integral target and is not this theorem.
- `msearch.py ... leansearch`, query: "normalization commutes with field extension up to
  universal homeomorphism". Eight hits on relative normalization and algebraic normal field
  extensions, none the required arbitrary-field-extension assertion.
- `rg` on `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for normalization with
  field/change/homeomorphism, lift/map/desc variants, and the item id: function-field
  normalization and finiteness are present, but this comparison is absent. The item id
  gives no hit.
- `rg` on `lean/Sheaf` for the same concepts finds `ReducedAlgebraicNormalizationFieldChange`
  (separable extensions only) and `NormalizationInseparableBaseChange` (geometric-normality
  hypotheses and a further purely inseparable base change), neither an exact match.
- `rg` on Mathlib, the source project, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `normalization_field_extension_homeomorphism` and
  `normalizationFieldExtensionHomeomorphism` finds no existing declaration.

Validation: `scompile.py Q74 lem-per-normalization-field-extension-homeomorphism
<module file>` passed both sandbox and library compilation locally and on the server,
with no errors or unexpected warnings. All variables are explicitly bound and
`set_option autoImplicit false` is set. Every source line is at most 100 characters.
No disputed statement or node fault was found.

## Second reading by Q74

Author's second pass under the dispatcher direct-delivery protocol; the maintainer supplies
an independent review. Reopened the unchanged node, Stacks 0C3N, the componentwise
normalization module and the final Lean file. Checked each binder against the node:
field k, integral X, structure map q, both finite-type conditions, arbitrary field K,
and the k-algebra structure are all present. Checked the domain as the disjoint union
of normalizations of the reduced components of X_K, and the target as the actual
base change of X's function-field normalization. Checked both projection equations:
together they say exactly that b lies over X_K and is induced by its normalization map.
Uniqueness expresses the canonical fraction map rather than requiring an externally
chosen comparison. Finally checked that `.universally` applies to b, rather than to
one projection or just its underlying original map, so all base changes are covered.
Rechecked the nonreduced purely inseparable example and the split reducible example.
No mismatch was found and no statement change was made.
