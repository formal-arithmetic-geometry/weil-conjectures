## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm` states
`AlgebraicGeometry.Scheme.Hom.exists_etale_to_affineSpace_of_exists_smooth_appLE`.
Its proof is `sorry`. No definitions or auxiliary theorems are introduced.

Hypothesis and conclusion correspondence:

- The morphism `g : X ⟶ Y` and point `x : X` are the node's `g : Y' → Y` and `y'`.
- “Smooth at y'” is expanded by `hx`: affine opens `U` in the target and `V` in the
  source, `x ∈ V`, `V ≤ g ⁻¹ᵁ U`, and `(g.appLE U V hVU).hom.Smooth`. This is precisely
  Stacks 01V5, definition-smooth (1), read in morphisms.tex. It requires no smoothness
  or local finite presentation away from that chart. It is an expansion of the
  pointwise hypothesis, not a new predicate or a change to the node.
- Replacing both schemes by affine neighbourhoods is expressed by existential opens
  `U`, `V`, their `IsAffineOpen` proofs, `g.base x ∈ U`, `x ∈ V`, and the image inclusion
  `hVU : V ≤ g ⁻¹ᵁ U`. These opens need not equal the input chart's opens.
- The integer `d ≥ 0` is `d : ℕ`, allowing zero.
- The map `e` has source `V.toScheme` and target
  `AffineSpace (ULift.{u} (Fin d)) U.toScheme`; `Etale e` is its stated property.
- The factorization is equality of actual morphisms:
  `e ≫ (AffineSpace (ULift.{u} (Fin d)) U.toScheme ↘ U.toScheme) = g.resLE U V hVU`.
  Thus it is the restricted original morphism, not an arbitrary map of the same schemes.

Dependency declarations read and used:

- `def-sbc-affine-space`: `AlgebraicGeometry.AffineSpace` in
  `Mathlib.AlgebraicGeometry.AffineSpace`, and its `AffineSpace.over` projection.
  The definition is the specified base change from the integral polynomial spectrum.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`. Its affine ring-map convention is
  expanded at the designated point in `hx`, using `RingHom.Smooth`, which reuses
  `Algebra.Smooth` through the ring map's algebra structure. This module is publicly
  imported; no new smoothness definition is made.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme` (publicly available through the imports).

The recorded proof dependencies are imported through `Mathlib.AlgebraicGeometry.ResidueField`
(and its affine-scheme imports), `Mathlib.RingTheory.Smooth.StandardSmoothOfFree`,
`WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive`, and
`WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree`, together with the public
statement imports. The docstring gives all six proof steps and their DAG inputs.

Edge cases: `d = 0` uses the empty coordinate type and the canonical zero-dimensional
projection. `u` is arbitrary and `ULift.{u} (Fin d)` lives in the scheme universe. An empty
source has no designated point, so the pointwise statement has no such instance. No
nonempty, reduced, Noetherian, separation or characteristic assumptions are imposed.
The zero ring is not excluded. The hypothesis permits an arbitrary nonsmooth component
away from the neighbourhood of `x`. There are no node faults or statement disputes.

Searches:

- `msearch.py ... leanfinder`: “A morphism smooth at a point factors on affine
  neighborhoods as an etale morphism to affine space followed by projection”. Eight
  hits: smooth/étale definitions and standard smooth chart results; no exact match.
- `msearch.py ... loogle`: `AlgebraicGeometry.Smooth, AlgebraicGeometry.AffineSpace`.
  One hit: the smoothness instance for affine space; no normal form statement.
- `msearch.py ... grep`: `exists_etale_to_affineSpace|etale.*affineSpace|affineSpace.*etale`.
  No Mathlib hits.
- Direct `rg` of the same expression and the node id in `WeilConjectures` and `lean/Sheaf`
  found upstream normal form declarations in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`, whose full signatures
  and docstrings were read. The relative-dimension theorem assumes global smoothness
  of fixed dimension. The pointwise smooth-locus theorem additionally assumes
  `[LocallyOfFinitePresentation g]` on the entire source. Neither matches this node;
  the input affine chart is sufficient here. No equivalent project statement was found.

Validation: the module compiled cleanly with the required `scompile.py` invocation.


## Second reading by NO

I independently read the node, the sandbox module, Stacks morphisms.tex
Definition 01V5 (definition-smooth) and Lemma 054L
(lemma-smooth-etale-over-affine-space), including the introductory conventions.
The node is the existential-neighbourhood version of 054L; the source's stronger
form permits a prescribed affine target neighbourhood. The node does not prescribe
one, so the existential target open in Lean is correct. No source-wide field,
Noetherian, separation, quasi-compactness, or global finite-presentation assumption
is present. No statement correction is needed.

Object/hypothesis/conclusion checklist, in the order of the node:

- Arbitrary schemes Y', Y: `{X Y : Scheme.{u}}`; the renamed source and target
  agree. Verdict: exact, with arbitrary universe u.
- Morphism g and designated source point y': `(g : X ⟶ Y) (x : X)`.
  Verdict: exact; the image point is `g.base x`.
- Smooth at y': `hx` existentially quantifies affine target U and affine source V,
  their `IsAffineOpen` proofs, `x ∈ V`, image inclusion `hVU`, and
  `(g.appLE U V hVU).hom.Smooth`. Verdict: exactly Definition 01V5(1).
  `hVU hxV` implies image-point membership, so its absence as a separate input
  conjunct drops no hypothesis. This does not assume smoothness away from the chart.
- Replace both schemes by affine neighbourhoods: output opens U, V, two
  `IsAffineOpen` proofs, `g.base x ∈ U`, `x ∈ V`, and `V ≤ g ⁻¹ᵁ U`.
  Verdict: exact; no unwanted containment in the input chart is required.
- Nonnegative dimension: output `d : ℕ`. Verdict: exact, including zero.
- Map to relative affine space: output
  `e : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) U.toScheme`.
  Verdict: exact; ULift relabels the d coordinates without changing their number.
- Etaleness: `Etale e`. Verdict: the recorded etale-morphism notion, with no
  additional surjectivity or finiteness constraint.
- Factorization of the original morphism: equality
  `e ≫ (AffineSpace (ULift.{u} (Fin d)) U.toScheme ↘ U.toScheme) =
  g.resLE U V hVU`. Verdict: exact equality with the restricted g; the projection
  is canonical, not a freely chosen morphism. All witnesses depend on g and x,
  and d and the opens are existential as required.

Dependency declarations were opened, not inferred from their names:
Mathlib AffineSpace.lean defines `AffineSpace` by pullback over the terminal
scheme and `AffineSpace.over` by its first projection. This is the
`def-sbc-affine-space` construction (the integral model uses ULift integers).
Mathlib Morphisms/Smooth.lean defines `Smooth` using smooth affine section maps;
RingHom/Smooth.lean defines `RingHom.Smooth` using `Algebra.Smooth` for precisely
the given ring map's algebra structure. The pointwise expansion uses these
existing notions and introduces no private smoothness predicate.
Mathlib Morphisms/Etale.lean defines `Etale` by etale affine section maps, as the
recorded `def-weil-etale-morphism` requires. Scheme.lean defines `Spec` and its
contravariant `Spec.map`; `appLE` is the original section map followed by
restriction. Restrict.lean defines `resLE` as the actual morphism restriction.
The upstream square-Jacobian definition and its etale characterization were
also opened: the proof-plan imports use the recorded declarations. The six
steps in the theorem docstring follow the node: affine point/prime, principal
localization, transport of the standard-smooth presentation, regrouping
variables, square-Jacobian etaleness, and equality of composites on coefficients.
There are no new definition nodes or dependency modules to audit.

Edge cases: for d = 0, `ULift (Fin 0)` is empty and the canonical projection
is the zero-dimensional affine-space isomorphism. No empty-coordinate case is
excluded. The empty source has no x, exactly as in the source; a morphism from
a nonempty source to an empty target cannot furnish these inputs. Zero rings
are allowed wherever their spectra occur. No characteristic restriction or
nonzero-ring instance appears. Universes are bound explicitly by `universe u`;
ULift places the coordinates in the scheme universe. This is the usual common
scheme-universe convention, not an independent smaller test-object universe.

Independent searches (2026-10-15): LeanFinder query "smooth at a point admits an
affine open neighborhood etale over polynomial affine space" returned eight
smooth/etale/chart results, none the exact statement. Loogle query
`AlgebraicGeometry.AffineSpace, AlgebraicGeometry.Etale` returned no matches.
An earlier two-quoted-string Loogle query was malformed and was replaced by
that valid query. LeanSearch query "A smooth morphism at a point factors on
affine neighbourhoods through an etale morphism to affine space" was unavailable
(Internal Server Error), so no mathematical verdict is based on it.
The grep service query `normal.form|smooth_appLE` was broad and mostly unrelated;
I supplemented it by direct rg searches for `normal.form`, `etale_to_affineSpace`,
`smooth_appLE`, and smooth/point and etale/affine combinations in Mathlib,
WeilConjectures and lean/Sheaf. I opened all three upstream normal-form
signatures in WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth:
the standard-smooth-chart result assumes a stronger presentation; the
fixed-relative-dimension result assumes global smoothness of that dimension;
the smooth-locus result assumes `[LocallyOfFinitePresentation g]` globally.
None gives this node's hypothesis exactly. No project duplicate was found.

No mismatch was found and no Lean or node change was made. The only addition
is this independent reading. There is one named theorem with proof `sorry`,
no definition data, no proved auxiliary result, no file-local notation or
instance, and no unbound variable. The recorded lean.statement was checked
verbatim against the file's signature. The required server scompile.py run
compiled the delivered module cleanly (no warnings or errors).
