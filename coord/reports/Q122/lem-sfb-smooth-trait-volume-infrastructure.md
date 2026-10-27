## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothTraitVolumeInfrastructure` states
`AlgebraicGeometry.smooth_trait_volume_infrastructure`, with one whole-proof `sorry` and no
new definitions or auxiliary theorems. The natural-language proof docstring contains all eight
reviewed proof steps and their dependency IDs. The node's mathematical statement is unchanged.
Its statement dependencies gain the already-landed `def-weil-pure-dimension` because the final
hypothesis explicitly uses its exact recorded predicate.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| DVR R | `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]` |
| Uniformizer π | `(π : R) (_hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})` |
| Fraction field E | The canonical `FractionRing R`, with its `algebraMap`; no additional choice or hypothesis. Every fraction field is canonically R-isomorphic to this one. |
| Residue field k | The residue field at `IsLocalRing.closedPoint R` in the canonical scheme fibre. The canonical identification of the spectrum stalk's residue field with `R/𝔪` gives exactly the residue-field base change. |
| T = Spec R and smooth finite-type f:Z→T | `{Z : Scheme.{u}} (f : Z ⟶ Spec (.of R)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]`. Finite type is exactly locally finite type plus quasi-compactness, as the dependency record requires. |
| Generic fibre Z_E and its inclusion j | `pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))` and its actual `pullback.fst`. |
| Special fibre Z_k | `f.fiber (IsLocalRing.closedPoint R)`, with actual inclusion `f.fiberι (IsLocalRing.closedPoint R)`. |
| Z Noetherian and regular | `IsNoetherian Z ∧ IsRegularScheme Z`; the latter includes local Noetherianity and stalkwise regularity, exactly as recorded. |
| Every local ring an integrally closed domain | `∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧ IsIntegrallyClosed (Z.presheaf.stalk z)`. No global integrality of disconnected Z is asserted. |
| Z_E is an open subscheme | `IsOpenImmersion (pullback.fst ...)`. |
| Z_E is quasi-compact | `CompactSpace ↥(pullback ...)`. Mathlib's compactness here requires no Hausdorff hypothesis. |
| O_Z → j_*O_Z_E injective | `∀ U : Z.Opens, Function.Injective (j.app U)`. `Scheme.Hom.app` is the actual ring map on U to sections on its inverse image. Sectionwise injectivity is exactly injectivity of this map of sheaves. |
| Special fibre reduced | `IsReduced (f.fiber (IsLocalRing.closedPoint R))`. |
| Finitely many irreducible components | `(irreducibleComponents (f.fiber ...)).Finite`. |
| Components open and closed | Every `C ∈ irreducibleComponents ...` satisfies `IsClopen C`. |
| Components pairwise disjoint | For components C,D, `C ≠ D → Disjoint C D`. |
| Generic point ζ of each nonempty special component | Quantify over actual `ζ : f.fiber ...`, component membership, and `IsGenericPoint ζ C`. Irreducible components are nonempty by their definition and schemes are sober, so this covers every component generic point without adding a hypothesis. |
| Ambient O_Z,ζ is a DVR | `∃ hdom : IsDomain (Z.presheaf.stalk (f.fiberι ... ζ)), @IsDiscreteValuationRing ... _ hdom ∧ ...`. The proof argument hdom is existential in the conclusion, not an additional assumption. |
| Its uniformizer is the image of π | Its maximal ideal equals the singleton span of the image of π under `(Scheme.ΓSpecIso (.of R)).inv`, then `f.appTop`, then the germ of Z at the actual ambient point. These are canonical maps; no arbitrary ring map or stalk identification is assumed. |
| If Z_E nonempty and pure of dimension d≥0 | `∀ d : ℕ, Nonempty ↥(pullback ...) → (pullback ...).IsPureDimension d → ...`. The existing predicate quantifies over all irreducible components and their subspace Krull dimensions. |
| Ω¹_Z/R locally free of constant rank d | `SheafOfModules.IsFiniteLocallyFreeOfRank f.relativeDifferentials d`. |
| Ω^d_Z/R = exterior^d Ω¹_Z/R invertible | `(Scheme.Modules.exteriorSheaf f.relativeDifferentials d).IsInvertible`. The equality is the definition of the notation Ω^d, so the conclusion directly uses that object. |

Dependency declarations used (source signatures and docstrings read):

- `def-sc-discrete-valuation-ring`: `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean` — `IsDiscreteValuationRing`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme` — `AlgebraicGeometry.Spec`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme` — `AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth` — `AlgebraicGeometry.Smooth`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` — `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` — `AlgebraicGeometry.Scheme.Modules.moduleBaseChange`.
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme` — `AlgebraicGeometry.IsRegularScheme`.
- `def-sc-relative-differential-sheaf`: `WeilConjectures.AlgebraicGeometry.Modules.Differentials` — `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`.
- `def-sc-sheaf-exterior-power`: `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf` — `AlgebraicGeometry.Scheme.Modules.exteriorSheaf`.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible` — `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian` — `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` — `IsIntegrallyClosed`.
- `def-amb-finite-locally-free-module`: `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree` — `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension` — `AlgebraicGeometry.Scheme.IsPureDimension`.

The statement imports are public. Every recorded, stated proof dependency's module is also
imported; those imports are non-public where the statement does not use their declarations.
The proof itself remains postponed. No dependency interface repair is needed.

Edge cases checked before writing: empty Z gives vacuous stalk/component conditions and no
nonempty-generic-fibre hypothesis; Spec E→Spec R has empty special fibre; Spec R→Spec R has
rank zero and degree-zero exterior sheaf O_R; affine n-space has rank n; disconnected generic
fibres are allowed, with purity requiring each component to have dimension d; no separatedness,
properness, surjectivity, perfection of k, or excellence is assumed. If the generic fibre is
empty, schematic density forces empty Z and the rank conclusion still retains its explicit
nonemptiness antecedent. No universe is auto-bound; R and schemes share arbitrary universe u,
and both canonical fields live there. An isomorphic presentation of a fraction or residue field
changes no assertion.

Sources read: current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
clause (3), and the item's reviewed agent assembly of Stacks facts. Locally read
`morphisms.tex` Tag 02G1, `schemes.tex` Tag 0HA1, and `properties.tex` Tag 033M.
The [primary BLR scan](https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf)
was opened at PDF p.110, printed p.104 (the general smooth-model stalk/π order construction),
and PDF pp.42–43, printed pp.36–37 (§2.2 Proposition 5, differential rank). No source-based
correction is needed. The full supporting statement is the DAG's extracted lemma, not a verbatim
BLR proposition. No STATEMENT-DISPUTED finding.

Searches for an existing full statement:

- `msearch.py leanfinder`: “A smooth finite type scheme over a discrete valuation ring is regular,
  has schematically dense generic fibre, special fibre generic stalks are DVRs, and differentials
  have constant generic rank”. Eight hits: smooth-chart APIs, smooth relative dimension and
  Weierstrass good reduction; none states the complete assertion.
- `msearch.py loogle`: `"Smooth", "IsDiscreteValuationRing"`; zero hits.
- `msearch.py grep`: `IsDiscreteValuationRing|schematicallyDense|smooth_trait` in Mathlib's
  AlgebraicGeometry directory; seven hits, in OrderOfVanishing and elliptic-curve reduction,
  none states this lemma.
- `rg -n` on `lean/WeilConjectures` for the item's ID returned no match.
- `rg -n` on both `lean/WeilConjectures` and `lean/Sheaf` for `smooth.*trait|smooth_trait`
  found SmoothTraitCurveLocalProperties, SmoothTraitAffineGenericOpen and other local charts.
  The first concerns pure relative curves and dimension bounds, the second affine charts;
  neither gives this statement. Both source modules were read.
- Project searches for schematic density, pure dimension, irreducible-component dimension,
  and stalk ring maps found the existing notions reused here. In particular PureDimension's
  definition was read in full and its landed node added, rather than copied.

Validation: all single-file compilation uses the prescribed `scompile.py` against the live
published server library. Initial elaboration errors were explicit `CommRingCat.ofHom` naming
and the need for explicit scheme-to-type coercion `↥` inside CompactSpace and Nonempty. Both
were repaired without changing the mathematics. The docstring linter's final-newline warning
was repaired, and compilation and the required delivery dry run are recorded below.

Final validation results: `scompile.py Q122 lem-sfb-smooth-trait-volume-infrastructure` compiled
the delivered file both as the sandbox probe and under its actual library module name, with
exit code 0, no errors and no warnings (2.5 s and 2.7 s). The first required
`deliver2.py ... --no-push` returned `OK (dry run)` with server preflight and compile passing.
The only changed node fields are `lean` and the addition of the landed pure-dimension dependency
to `stmt_deps`; the recorded signature is byte-for-byte the file signature. Maximum Lean line
width is 98. There is exactly one postponed theorem and no data definition.

## Second reading by Q122

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
