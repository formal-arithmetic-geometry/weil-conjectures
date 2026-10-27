## Worker report

The module `Sheaf.AlgebraicGeometry.GenericSmoothModelSmoothening` states
`AlgebraicGeometry.Scheme.exists_smoothening_of_smooth_generic_fiber`, with its only
proof `sorry`. It defines no new notion. The item statement and accepted proof are
unchanged. The statement-dependency list gains the already landed
`def-weil-pbc-strict-henselization-structural-map`, needed to specify morphisms over
Spec R using the canonical structural map, rather than an arbitrary map.

Source read: Bosch--Lütkebohmert--Raynaud, Néron Models, §3.1 Theorem 3 and
Corollary 4, printed pp.61–62 (PDF pages 67–68), at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
Theorem 3 supplies special-fibre blowups; the smooth open gives Corollary 4.
Separatedness is preserved by blowups and open restriction when the original
model is separated. The theorem docstring records all eight accepted proof steps,
including the preliminary removal of vertical torsion, both inductions and their
support invariant, and the final quasi-compactness argument for finite type.

Clause-by-clause statement correspondence:

- A discrete valuation ring R: `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. The Mathlib class extends local and principal ideal
  ring structures and requires a nonzero maximal ideal.
- Its fraction field E: `(E : Type u) [Field E] [Algebra R E]
  [IsFractionRing R E]`. No separability or characteristic condition is imposed.
- T is Spec R: the base of the over-category is literally `Spec (.of R)`.
- A geometric closed point: `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` and
  `s : Spec (.of Ω) ⟶ Spec (.of R)`. The hypothesis `hs` says that every point
  maps to `IsLocalRing.maximalIdeal R`; Spec Ω has one point, so this is exactly
  lying over the closed point, with no residue-field closure restriction.
- The corresponding strict henselization: the domain of the section Hom is
  `Over.mk (strictHenselizationStructuralMap s)`. Its underlying scheme is the
  existing `strictHenselizationScheme s = Spec (strictHenselizationRing s)`.
  The ring is the published affine pointed-étale-neighbourhood colimit.
- A scheme Y over T: `(Y : Over (Spec (.of R)))`, with structure map `Y.hom`.
  Separatedness is `[IsSeparated Y.hom]`, whose defining field is precisely
  `IsClosedImmersion (pullback.diagonal Y.hom)`.
- Finite type: `[LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]`, exactly the
  two clauses of the recorded finite-type definition.
- Smooth generic fibre: the `Smooth` instance is on `pullback.snd Y.hom
  (Spec.map (CommRingCat.ofHom (algebraMap R E)))`. This is the projection of
  Y ×_T Spec E to Spec E, rather than the projection to Y.
- Existence of a smooth separated finite-type T-scheme: `∃ Ysm : Over
  (Spec (.of R)), ...`, with the four conclusions `Smooth Ysm.hom`,
  `IsSeparated Ysm.hom`, `LocallyOfFiniteType Ysm.hom`, `QuasiCompact Ysm.hom`.
- A T-morphism q: the existential `q : Ysm ⟶ Y` is a morphism in the over-category;
  its triangle commutes by the definition of that Hom, not an extra conclusion.
- q_E is an isomorphism: `IsIso (((Over.pullback ...).map q).left)` on the
  scheme morphism induced by pulling q back along Spec E → Spec R.
- The specified section bijection: `Function.Bijective (fun a : Over.mk
  (strictHenselizationStructuralMap s) ⟶ Ysm ↦ a ≫ q)`. These are exactly
  Hom_T(Spec R^sh, Ysm) and Hom_T(Spec R^sh, Y). This states bijectivity of
  composition with q itself, not merely existence of an unrelated equivalence.
- No boundedness, properness, excellence, group structure or initial flatness
  is assumed. Those hypotheses do not appear in the signature.

Dependency declarations read and reused:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are
  written inline as recorded. `Scheme.SpecToEquivOfField` was also read in
  `Mathlib.AlgebraicGeometry.ResidueField`; it is not needed to encode this Hom.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, `Scheme.strictHenselizationScheme`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap` and its characterization by
  `exists_strictHenselizationStructuralMap`. This is a canonical construction.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded bundle
  delegates scheme base change to `Over.pullback`, whose object and map were
  read in `Mathlib.CategoryTheory.Comma.Over.Pullback`. This API is used directly;
  module pullback from that bundle is not confused with scheme base change.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.RingTheory.Localization.FractionRing`: `IsFractionRing` gives the
  standard fraction-field algebra structure.

Stated proof dependencies are imported without `public`: affine strict-local-ring
comparison, strict-henselization DVR, strict-henselization local maximal ideal,
Noetherian schemes and morphisms, and PID torsion-free flatness. Smooth restriction
is already in the public smoothness import. Unstated proof dependencies receive
no fabricated interface. They are named by their content in the proof docstring.

Edge cases checked before writing: Y may be empty; its generic fibre may be
empty; the strict-henselian section sets may be empty; Y may already be smooth
(the identity is the expected choice); and Y may have vertical torsion or extra
special-fibre components. None is excluded by a binder. In particular no flatness
hypothesis was added. Both equal and mixed characteristic DVRs are allowed.
The universe `u` is explicitly bound and can be enlarged to contain R, E, Ω and Y;
there is no quantified family of tests in an independently smaller universe.
No new definitions, hollow data, or auxiliary postponed theorems occur. No
statement fault or unresolved statement dispute was found.

Searches actually run:

- `msearch.py`, `leanfinder`: “A separated finite type scheme over a discrete
  valuation ring with smooth generic fibre admits a smoothening preserving
  generic fibre and strict henselian integral points”. Eight hits concerned
  local smooth presentations, relative dimension and smooth loci; none stated
  this existence theorem.
- `msearch.py`, `loogle`: `"Smooth", "Valuation"`. Zero hits.
- `msearch.py`, `grep`: `smoothening|smoothen|Neron`, restricted to
  `AlgebraicGeometry`. Zero Mathlib hits.
- `msearch.py`, `leansearch`: “A generically smooth separated finite type scheme
  over a discrete valuation ring has a smooth separated model inducing an
  isomorphism of generic fibres and a bijection on strict henselian sections”.
  Eight hits: smoothness constructors, schemes and the separated valuative
  criterion; none was this theorem.
- `rg -n 'smoothening|smoothen|Neron|lem-sfb-generic-smooth-model-smoothening'`
  in `lean/WeilConjectures` and `lean/Sheaf`: no hits.
- `grep -rn 'lem-sfb-generic-smooth-model-smoothening'` in
  `lean/WeilConjectures`: no hits.
- `rg -n 'exists_smoothening_of_smooth_generic_fiber'` across Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`: no hits.
- `rg -n 'smoothening|smoothen'` in `literature/blueprint/latest`: no hits.
- Searched existing strict-henselization declarations in the DAG and source;
  found the existing structural-map node and reused it, with no new node.

Validation: `scompile.py Q15 lem-sfb-generic-smooth-model-smoothening` compiled
both the sandbox and library module views cleanly (1.8 s and 2.4 s), without
warnings or errors. All theorem variables and the universe are explicitly bound;
no diagnostic commands or file-local notation are left in the delivered module.

## Second reading by Q15

The worker delivered directly, with no separate worker reading, because the dispatcher
allows no second agent. The maintainer's reviewer wrote this reading in its place. It
compares the node, the source place (BLR 3.1 Thm 3 / Cor 4) and the dependency records
with the delivered signature of
`AlgebraicGeometry.Scheme.exists_smoothening_of_smooth_generic_fiber`.

| Node clause | Lean | Verdict |
|---|---|---|
| R a DVR (def-sc-discrete-valuation-ring) | `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]` (recorded leaf) | exact |
| E the fraction field | `[Field E] [Algebra R E] [IsFractionRing R E]` | exact; E in universe u is harmless (fraction fields are unique up to iso) |
| T = Spec R | base `Spec (.of R)` of the over-category | exact |
| geometric closed point | `Ω` alg. closed, `s : Spec (.of Ω) ⟶ Spec (.of R)`, `hs`: the unique point maps to `maximalIdeal R` | exact (inline form of def-weil-geometric-point record) |
| R^sh, Spec R^sh as T-scheme | `Over.mk (strictHenselizationStructuralMap s)`: recorded canonical structural map of def-weil-pbc-strict-henselization-structural-map (landed, existing:true), over `strictHenselizationScheme s` | exact; adding this landed node to stmt_deps is allowed (brief-stage2 §"STMT_DEPS MAY GAIN LANDED NODES") |
| Y → T separated, diagonal closed immersion | `Y : Over (Spec (.of R))`, `[IsSeparated Y.hom]` | exact |
| finite type | `[LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]`, i.e. the conjunction in the def-weil-finite-type-morphism record | exact |
| Y_E smooth over E | `Smooth (pullback.snd Y.hom (Spec.map (algebraMap R E)))`, i.e. pr_T of def-pc-base-change | exact |
| ∃ smooth separated finite-type Ysm over T, T-morphism q | `∃ Ysm q`, with `q` an Over-hom, `Smooth`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` of `Ysm.hom` | exact |
| q_E an isomorphism | `IsIso ((Over.pullback (Spec.map …)).map q).left` | exact |
| composition with q bijective on R^sh-points, Y(B)=Hom_T(Spec B,Y) | `Function.Bijective (fun a ↦ a ≫ q)` on Over-homs from `Over.mk (strictHenselizationStructuralMap s)` | exact; the map is composition with q itself |
| no boundedness, properness, excellence, group, flatness | absent from binders | exact |

Edge cases: Y empty, Y_E empty, empty point sets, Y already smooth (q = 𝟙), vertical torsion
in Y, and equal or mixed characteristic are all allowed by the binders. One universe u covers
R, E, Ω and the schemes, as the strict-henselization records require.

Searches (reviewer): grep for `smoothening`, `exists_smoothening_of_smooth_generic_fiber` and
`GenericSmoothModelSmoothening` in live lean/Sheaf and lean/WeilConjectures, and grep of the
DAG for citers. There is no duplicate declaration. The item is referenced only by the
weak-Néron parent and the three sibling nodes created with it.

Gates: no definitions; the only proof is `sorry`; the module and theorem docstrings carry the
source and `(blueprint: …)`; the theorem docstring gives proof steps 1–8; the `lean.statement`
record is verbatim from the file. Mismatches: none in the Lean. This section replaces the
empty dispatcher-wording section.
