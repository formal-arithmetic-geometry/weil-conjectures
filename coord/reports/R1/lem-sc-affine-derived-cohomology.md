## Worker report

The module `Sheaf.AlgebraicGeometry.AffineDerivedCohomology` states
`AlgebraicGeometry.schemeHigherDirectImage_of_affine`, with one `sorry` proof and no
new definitions. The node is unchanged except for its `lean` record.

Hypotheses and conclusions, clause by clause:
- Schemes X and Y: `{X Y : Scheme.{u}}`.
- Morphism f from X to Y: `(f : X ⟶ Y)`.
- Affineness of f: `[IsAffineHom f]`; neither scheme is assumed affine.
- E belongs to D_QCoh(X): `(E : schemeDerivedCategory X)` and
  `(hE : schemeDerivedQCohProperty X E)`. This is the underlying-object/predicate
  presentation of the recorded full subcategory, with no boundedness condition.
- Every integer degree: `(i : ℤ)`, allowing negative degrees and degree zero.
- H^i(Rf_*E): `(schemeHigherDirectImage f i).obj E`.
- f_*H^i(E): `(RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj`
  applied to `(DerivedCategory.homologyFunctor
  (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E`.
- The isomorphism clause is `Nonempty (H^i(Rf_*E) ≅ f_*H^i(E))`, an isomorphism
  of O_Y-module sheaves, not an equality of groups or sections.
- The quasi-coherence clause is the conjunction with `.IsQuasicoherent` of that
  same ordinary direct image.
- The two explicit `HasDerivedCategory` binders supply the chosen localizations;
  their morphism universes `wX` and `wY` are independent. They express the existing
  definitions' setup, not additional geometric hypotheses.

Dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (the latter via categorical morphism notation).
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory` and
  `schemeDerivedQCohProperty`, including their full signatures and docstrings.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`: `schemeHigherDirectImage`,
  defined using `schemeDerivedDirectImage` and the homology functor.
- Its imported `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage` supplies
  `RingedSpace.moduleDirectImage`, the shared ordinary module direct image.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.

The docstring reproduces both proof steps: affine higher-image vanishing followed
by the quasi-coherently acyclic unbounded comparison, then preservation of
quasi-coherence by affine ordinary direct image. No proof is supplied in stage 2.

Source checked: https://stacks.math.columbia.edu/tag/0AVW, Lemma 36.5.4, proof,
the displayed cohomology comparison and its higher-direct-image vanishing input.
The local literature checkout has no `stacks-project/perfect.tex`, so the source
was read on the Stacks website. No correction or disputed statement was needed.

Edge cases checked mathematically before writing: zero E and the empty scheme
are included; i = 0 and negative i require no changes; arbitrary unbounded E is
included; f = identity gives the usual identity comparison; affine f over a
nonaffine Y is included; no Noetherian or separatedness condition is imposed on Y.
There is no restriction on characteristic. The same scheme universe follows the
recorded derived direct image, and no independent universe of test objects makes
a hypothesis vacuous.

Searches for an existing statement:
- `msearch.py leanfinder`, query “For an affine morphism of schemes derived
  pushforward commutes with cohomology sheaves of an unbounded complex with quasi
  coherent cohomology”: eight hits, all ordinary pushforward composition and
  naturality statements; none gives the derived cohomology comparison.
- `msearch.py loogle`, query
  `AlgebraicGeometry.Scheme.Modules.pushforward, DerivedCategory.homologyFunctor`:
  zero hits.
- `msearch.py grep`, query `derived.*pushforward|higherDirectImage|cohomology.*Rf`
  in Mathlib/AlgebraicGeometry: zero hits.
- `msearch.py leansearch`, query “affine morphism derived direct image cohomology
  quasi coherent”: service unavailable (Internal Server Error).
- `rg` in WeilConjectures for higherDirectImage, derived pushforward, and
  pushforward/cohomology: ordinary higher-direct-image results and degree-zero
  cohomology comparisons, no unbounded quasi-coherent comparison. Searching the
  exact node id gives no hit.
- `rg` in lean/Sheaf for affine/cohomology, schemeHigherDirectImage and
  moduleDirectImage: existing definitions, affine conservativity and concentration,
  but no theorem asserting this node's two clauses for every integer degree.
- Name collision searches in Mathlib/source/project and dag/lean_names_upstream.json
  for `schemeHigherDirectImage_of_affine` and `affineDerivedCohomology`: no hits.

Local compilation with `lcompile.py` passed with no errors or warnings.

## Second reading by R1

I independently read the node, its Stacks source (Tag 0AVW, Lemma 36.5.4),
the dependency declarations, and the Lean module. The introduced objects and
their Lean renderings match item by item:

- Schemes `X Y : Scheme.{u}` are introduced by `{X Y : Scheme.{u}}`.
- The morphism `f : X ⟶ Y` is the explicit Lean binder `(f : X ⟶ Y)`.
- Affineness is exactly the hypothesis `[IsAffineHom f]`.
- The object `E ∈ D_QCoh(X)` is rendered as
  `(E : schemeDerivedCategory X)` together with
  `(hE : schemeDerivedQCohProperty X E)`.
- The arbitrary degree `i ∈ ℤ` is the final binder `(i : ℤ)`.
- `H^i(Rf_*E)` is `(schemeHigherDirectImage f i).obj E`.
- `f_*H^i(E)` is the ordinary module direct image applied to the homology
  object, namely the displayed `RingedSpace.moduleDirectImage ...` term.
- The comparison is exactly `Nonempty (... ≅ ...)`, preserving the sheaf
  isomorphism rather than weakening it to an equality of sections.
- The second conjunct is `.IsQuasicoherent` on that same direct-image term.

The two `HasDerivedCategory` instance binders are the localization choices
required by the recorded definitions; they add no geometric hypothesis. The
quantifier order agrees with the node and the source. No mismatch was found,
so no Lean or node correction was required. The docstring records both source
proof steps and explains the unbounded-complex comparison citation.

I checked the zero object, empty schemes, identity and affine maps over a
non-affine target, degree zero, negative degrees, arbitrary unbounded objects,
and arbitrary characteristic. All are covered by the statement. Searches via
LeanFinder, Loogle, grep, `rg` over Mathlib, the project, and `lean_names_upstream`
found no existing declaration with this statement. `lcompile.py` succeeds.
