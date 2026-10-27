## Worker report

The new module `Sheaf.AlgebraicGeometry.RationalDensityFieldExtension` states
`AlgebraicGeometry.Scheme.Hom.denseRange_baseChangeFieldPoint_of_dense` with a single
`sorry` proof. No definitions, dependency repairs, new nodes or statement corrections
are needed. Only the item's `lean` record changes.

Clause-by-clause correspondence:

- The field `k` is `{k : Type u} [Field k]`.
- An arbitrary scheme over `k` is `{X : Scheme.{u}}` together with
  `(f : X ⟶ Spec (CommRingCat.of k))`.
- The specified subset of rational points is `(D : Set (f.fieldPoints k))`.
  `f.fieldPoints k` is the existing subtype of maps `Spec k ⟶ X` with composite
  equal to `Spec.map (algebraMap k k)`, hence sections of `f`.
- Density of the images of these points is
  `hD : DenseRange (fun d : D ↦ d.1.1.base default)`.
  `d.1` is the rational point, its next `.1` the scheme map, and `default` is the
  unique point of `Spec k`. `DenseRange` means its range has closure all of `X`,
  equivalently every nonempty open contains one of these images.
- An arbitrary extension is `(L : Type u) [Field L] [Algebra k L]`. There is no
  algebraicity, finite generation, finite dimensionality or separability restriction.
- `X_L` is the existing pullback of `f` and
  `Spec.map (CommRingCat.ofHom (algebraMap k L))`, as in the return type of
  `f.baseChangeFieldPoint L`. Its structure map is `pullback.snd`.
- The induced point `d_L` is precisely the recorded canonical construction
  `f.baseChangeFieldPoint L d.1`. Its underlying image is
  `(f.baseChangeFieldPoint L d.1).1.base default`.
- The conclusion is `DenseRange` of that function on the SAME subtype `D`; it
  asserts density of the chosen base-changed points, not merely of all `L`-points.
- No finite type, reducedness, irreducibility, separatedness, smoothness or
  separability hypotheses occur. There is no `Nonempty` assumption on `X` or `D`.
  The universe `u` is explicit and arbitrary; the scheme and spectra belong to
  the same category `Scheme.{u}`, as required by the recorded base-change API.

Dependency declarations read and used:

- `Field` in `Mathlib.Algebra.Field.Defs` and `Algebra` in
  `Mathlib.Algebra.Algebra.Defs` render `def-weil-field` and
  `def-pc-field-extension` through their existing Mathlib matches.
- `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`, and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme` render the scheme and affine-spectrum nodes.
- `AlgebraicGeometry.Scheme.Hom.baseChangeFieldPoint` in
  `WeilConjectures.AlgebraicGeometry.DensePoints` is the recorded declaration of
  `def-pc-rational-point`. Its full definition uses the canonical pullback lift
  of `Spec.map (algebraMap k L) ≫ d` and the identity on `Spec L`; its second
  projection is the identity. Rational points are the existing `Hom.fieldPoints`
  in `Comparator.Weil.Definitions`, exposed through the recorded module.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` is the recorded
  `def-pc-base-change` module, publicly imported. Its documentation explicitly
  identifies scheme base change with `Limits.pullback` and its two projections;
  `baseChange_section_characterization` characterizes the induced section.
  Its recorded primary declaration `Scheme.Modules.moduleBaseChange` concerns
  modules; this item correctly uses its documented scheme/pullback interface,
  not a private replacement for base change.

All stated proof dependencies are imported privately: the affine chart theorem
`AlgebraicGeometry.exists_affineChart_baseChangeIso` from
`WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso`, the arbitrary-family
linear-kernel theorem `LinearMap.common_kernel_field_extension` from
`Sheaf.LinearAlgebra.CommonLinearKernelFieldExtension`, tensor multiplication
and evaluation from `Mathlib.RingTheory.TensorProduct.Maps` (and its Basic
import), the radical/zero-locus statements from
`Mathlib.RingTheory.Spectrum.Prime.Topology`, and basic-open/evaluation facts
from `Mathlib.AlgebraicGeometry.ResidueField`. The module docstring gives the
source and the theorem docstring supplies all five DAG proof steps, including
the nonreduced case and the finite-sum nilpotence exponent.

Edge cases checked before writing:

- `X = ∅`: both ranges live in empty spaces and density is vacuous.
- `D = ∅`: its density forces `X = ∅` by the open set `X`, and then `X_L = ∅`.
  The subtype formulation does not require an inhabitant of `D`.
- Nonreduced `Spec(k[ε]/ε²)`, with its one rational point: the evaluation kernel
  is `(ε)`, not zero. The proof uses the nilradical and preserves this case.
- Affine line over an infinite field with a dense chosen subset: the theorem
  keeps that subset rather than replacing it by all rational points.
- Finite base fields and inseparable or transcendental extensions: no typeclass
  excludes them. In the affine argument only finite tensor expansions, not
  finiteness of the extension or of the chosen family, are used.
- Arbitrary nonaffine, nonquasicompact and nonseparated schemes: the proof is
  assembled over all affine opens; none of these properties is assumed.

The source was read directly with `pdftotext` from
`literature/ega/EGA-IV-3_PMIHES-28-1966.pdf`, PDF pp. 170–171 (printed pp. 171–172).
Corollary 11.10.7 applies to the family `Spec k → X` because `Spec k` is
geometrically reduced. Density identifies the reduced closure with `X_red`;
after extension its underlying support is all of `X_L`. This confirms the
unrestricted statement, including nonreduced `X`. No statement fault was found.

Searches made (full remote search outputs are retained in `searches.jsonl`):

- `msearch.py leanfinder`: “A specified dense set of k rational points of an
  arbitrary scheme remains Zariski dense after any field extension”. Eight hits
  concern dominance and rational maps; no matching statement.
- `msearch.py loogle`: `"DenseRange", "baseChange"`. No hits.
- `msearch.py leansearch`: “A dense subset of rational points stays dense under
  extension of the base field for any scheme”. Eight hits concern general
  density, dominance and extensions of functions; no matching statement.
- `msearch.py grep`, subdirectory `AlgebraicGeometry`, pattern
  `rational.*dens|dens.*rational|denseRange.*[bB]aseChange|schematicallyDominant`.
  Nine hits concern dense open subsets and birational maps; no match.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for this node id, rational-point density, and the new declaration name.
  The node id and new declaration have no existing match. The closest theorem,
  `Hom.denseRange_baseChangeFieldPoint`, assumes `[IsSepClosed k] [Smooth f]`
  and uses all rational points, so does not state this node. The existing
  `DenseRationalClosedSubschemeDescent` theorem concerns reduced closed models
  and has finite type assumptions; it is also different.

Validation: the prescribed server-side `scompile.py` succeeded for both its
sandbox probe and the actual module `Sheaf.AlgebraicGeometry.RationalDensityFieldExtension`.
The actual-module compile took 2.2 s and emitted no errors or unexpected warnings.
The dry run and final delivery use `deliver2.py`.

## Second reading by Q116

Independent clause-by-clause reading done by the maintainer's review (cc reviewer, 2026-10-24).
It replaces the delivered self-check section ("No second worker reading was performed").

Node clauses and their Lean rendering:

1. Field `k` [def-weil-field]: `{k : Type u} [Field k]`. Correct.
2. A scheme over `k` [def-pc-scheme]: `{X : Scheme.{u}}` with `f : X ⟶ Spec (CommRingCat.of k)`. Correct.
   It is arbitrary: there is no finite type, reduced, irreducible, separated or quasi-compact instance.
3. `D ⊆ X(k)` [def-pc-rational-point]: `D : Set (f.fieldPoints k)`. `Hom.fieldPoints`
   (Comparator/Weil/Definitions.lean:85) is the subtype of `g : Spec k ⟶ X` with
   `g ≫ f = Spec.map (algebraMap k k)`, which is `𝟙`. So these are the sections of `f`. Correct.
4. Density hypothesis: `DenseRange (fun d : D ↦ d.1.1.base default)`. Its range is the set of images
   of the points of `D`, and `DenseRange` means that every nonempty open set meets it. This is
   exactly the node's "every nonempty open contains the image of some d". Correct.
5. Field extension `L/k` [def-pc-field-extension]: `(L : Type u) [Field L] [Algebra k L]`.
   There is no algebraic, finite or separable restriction. Correct.
6. `X_L = X ×_{Spec k} Spec L` [def-pc-base-change, def-weil-affine-spectrum] is
   `pullback f (Spec.map (algebraMap k L))`, through the return type of `baseChangeFieldPoint`. Correct.
7. Induced point `d_L` is the recorded `Hom.baseChangeFieldPoint L d.1`
   (DensePoints.lean:227) = `pullback.lift (Spec.map (algebraMap k L) ≫ d) (𝟙 _)`,
   which is the induced section `σ_T` of def-pc-rational-point for `T = Spec L`. It is canonical,
   not a chosen point. Correct.
8. Conclusion: `DenseRange` of `d ↦ (f.baseChangeFieldPoint L d.1).1.base default`. It is
   indexed by the same `D`, so it is neither weaker (all `L`-points) nor stronger. Correct.

Edge cases: `X = ∅` makes both ranges empty and the density vacuous. `D = ∅` is allowed:
the hypothesis then forces `X = ∅`, and nothing requires `Nonempty D`. The nonreduced case,
for example `Spec k[ε]/ε²`, is not excluded. Finite `k` and inseparable or transcendental
`L/k` are not excluded.

Universes: `k`, `L` and `X` share `u`, as the recorded `fieldPoints`/`baseChangeFieldPoint`
API requires. This is the project convention, and the same holds for the landed
`Hom.denseRange_baseChangeFieldPoint`.

Searches and duplicates: the closest existing result, `Hom.denseRange_baseChangeFieldPoint`,
needs `[IsSepClosed k] [Smooth f]` and uses all rational points, so it does not state this node.
I found no Mathlib match.

Other checks:
- `lean.statement` is a verbatim substring of the file.
- The proof is only `sorry`.
- The module and theorem docstrings give the source place and `(blueprint: …)`, and the
  theorem docstring carries all five proof steps.
- The private imports (AffineChartBaseChangeIso, CommonLinearKernelFieldExtension) exist live.
- The delivery changes nothing besides the item.
