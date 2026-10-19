## Worker report

This delivery states `AlgebraicGeometry.exists_refined_quasiFinite_polynomial_pureTranscendental`
in `Sheaf.AlgebraicGeometry.RefinedQuasiFinitePolynomialPureTranscendental`.
Its single theorem has proof `sorry`; no definition or proof is introduced.
The module docstring and theorem docstring cite Stacks 0520 and the first proof
paragraph of 052E. The theorem docstring follows all eight recorded proof steps,
including the special-fibre tensor comparison, the iterated localization, and
the computation of the final image prime.

Sources read: `literature/stacks-project/algebra.tex`,
`lemma-refined-quasi-finite-over-polynomial-algebra` (0520), and
`literature/stacks-project/more-morphisms.tex`,
`lemma-local-structure-finite-type` (052E), first paragraph of its proof.
The former provides the coordinate-prime normalization after shrinking both
source and base; the latter translates it into a quasi-finite affine-space chart
with purely transcendental image residue field.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Schemes `Z`, `S` and a morphism `p : Z → S` | `{Z S : Scheme.{u}}`, `(p : Z ⟶ S)` |
| Both schemes affine | `[IsAffine Z] [IsAffine S]` |
| `p` is of finite type | `[LocallyOfFiniteType p] [QuasiCompact p]`, the recorded finite-type convention |
| A marked point `z`, with `s = p(z)` | `(z : Z)` and `p z` throughout |
| `n` is the dimension at the marked point of the fibre over `s` | `∃ n : ℕ, topologicalKrullDimAt (p.asFiber z) = (n : WithBot ℕ∞) ∧ ...` |
| Dimension is topological local dimension, not local-ring dimension | `topologicalKrullDimAt` is the infimum of the topological Krull dimensions of open neighbourhoods; it is applied to the point in the scheme fibre |
| An affine open neighbourhood `S₀` of `s` | `(U : S.Opens)`, `IsAffineOpen U`, `p z ∈ U`; its scheme is `U.toScheme` |
| An affine open neighbourhood `Z₀` of `z` | `(V : Z.Opens)`, `IsAffineOpen V`, `(z₀ : V.toScheme)`, and `V.ι z₀ = z` |
| `Z₀` lies over `S₀` | The commutative equality `q ≫ (AffineSpace ... U.toScheme ↘ U.toScheme) ≫ U.ι = V.ι ≫ p` gives a factorization of `p` on all of `V` through `U`; hence `V ⊆ p⁻¹(U)` |
| An `S₀`-morphism `q : Z₀ → Aⁿ_(S₀)` | The stated type of `q` and the same commutative equality; `q ≫` the affine-space projection is the restricted structure morphism |
| `q` is quasi-finite, i.e. finite type with finite discrete fibres | `q.IsQuasiFinite`, the recorded Stacks predicate: finite type and every point isolated in its scheme fibre. Finite type makes these discrete fibres finite (the recorded finite-fibre equivalence). Thus this is exactly the node's quasi-finiteness, including the finite-type condition absent from Mathlib's bare `LocallyQuasiFinite` |
| The image point `t = q(z)` | `q z₀`; no independent image point is chosen |
| Some `0 ≤ r ≤ n` | `∃ r : ℕ, r ≤ n ∧ ...`; nonnegativity is inherent in `ℕ`, with no redundant conjunct |
| `κ(t)` is isomorphic over `κ(s)` to `κ(s)(u₁,...,uᵣ)` | The ring equivalence `e` to `FractionRing (MvPolynomial (Fin r) (...))` and the equation for every base-field element `a` |
| The extension is the one induced by the given structure morphism | The equation uses `Scheme.Hom.residueFieldMap` of the canonical affine-space projection at `q z₀`; its right side is the canonical `algebraMap` into the fraction field |

The residue field on the right is written at the image in `U.toScheme`.
Its image under `U.ι` equals `p z` by the displayed commutative equality and
`V.ι z₀ = z`. Since `U.ι` is the canonical open immersion, its induced residue
field map is the canonical isomorphism from `κ(p z)` to this field. Consequently
the displayed commuting ring equivalence is exactly an isomorphism over the
node's base residue field. In particular, it is not merely an abstract field
isomorphism, and it never replaces the image residue field by `κ(z)`.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and its morphisms; `IsAffine`/`IsAffineOpen` express affine schemes and opens.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`; the affine-scheme interfaces implement
  this notion without choosing new presentations by rings.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `AlgebraicGeometry.QuasiCompact`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`;
  `Mathlib.AlgebraicGeometry.Fiber` uses this chosen pullback for `p.fiber`
  and supplies `p.asFiber z`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and `Scheme.Hom.residueFieldMap`.
- `def-kun-dimension`: `WeilConjectures.Mathlib.Topology.KrullDimension`,
  `topologicalKrullDimAt`; its full definition was read and reused.
- `def-sbc-affine-space`: the Mathlib match is
  `Mathlib.AlgebraicGeometry.AffineSpace`, `AlgebraicGeometry.AffineSpace`,
  with coordinate type `ULift.{u} (Fin n)` and its canonical first projection.
- `pqf-def-quasifinite`: `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`,
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite`. Its existing node is added to
  `stmt_deps`, as permitted for an already landed notion used in the statement.
  No duplicate quasi-finite definition is introduced.

Existing stated proof dependencies are imported privately, including the
quasi-finite polynomial chart, fibre-prime and localization comparisons,
finite-ring-map quasi-finiteness, openness of the quasi-finite locus, principal
localization, and scheme quasi-finite/fibre comparisons. Mathlib proof leaves
are provided by the affine-space, pullback, quasi-separated, open-immersion,
localization, polynomial tensor-product, and algebraic-independence modules.
The source of `WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`
was read through `scompile.py --source` because it is not present in the older
local source checkout. The two newly split proof nodes
`lem-trf-quasi-finite-composition` and
`lem-trf-refined-noether-normalization-prime` have no Lean records yet, so they
have no imports to add. No downstream theorem is imported.
The upstream `WeilConjectures.RingTheory.QuasiFiniteAtPrime` interface is not
imported alongside its older side-library duplicate: the imported recorded
proof modules and quasi-finite scheme predicate already use the existing
side-library interface transitively.

Edge cases checked:

- `n = 0` is allowed: `ULift (Fin 0)` is empty and its affine space is canonically
  the base. The bound forces `r = 0`; the fraction field of the polynomial ring
  in zero variables gives the trivial field extension, not an excluded case.
- The marked point prevents an empty source (and hence an empty base); there is
  no artificial nonempty hypothesis on either scheme.
- Points are arbitrary, including nonclosed points. `p.asFiber z` is the point
  in the fibre over `p z`, so the dimension is not the dimension of a local ring.
- Arbitrary characteristic and non-Noetherian affine bases are included.
- Finite type includes quasi-compactness on both the input morphism and the
  quasi-finite chart. Purely transcendental means the image field, not a finite
  extension of the source field or a choice of an arbitrary algebra structure.
- Universe `u` is explicit; the finite coordinate type is lifted to that universe.
  All objects, variables, and universes are bound; `autoImplicit` is disabled.

Searches made (before writing the declaration):

- `msearch.py ... leanfinder`: “An affine finite type scheme morphism admits a
  quasi finite map to affine space with purely transcendental image residue
  field”. Eight hits on affine-space finite presentation, finite morphisms,
  and `LocallyQuasiFinite`; none supplies this refined chart.
- `msearch.py ... leansearch`: “quasi finite affine space chart with purely
  transcendental image residue field”. Eight hits on ring-map quasi-finiteness
  and its residue-field/fibre consequences; none states the chart theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.AffineSpace,
  AlgebraicGeometry.LocallyQuasiFinite`. Zero hits.
- `msearch.py ... grep`: `refined.quasi.finite|purely.transcendental|0520`
  in Mathlib's `AlgebraicGeometry`. Zero hits.
- `rg` in the upstream `WeilConjectures` and project `lean/Sheaf` for
  `refined-quasi-finite|purely transcend|0520|052E`: found the existing downstream
  local-structure and smooth-component modules and the general purely
  transcendental definition, but no refined-chart declaration.
- `rg` for the exact item id and proposed declaration name in upstream Lean,
  project Lean and `dag/lean_names_upstream.json`: no declaration.
- The node's existing Mathlib searches were also read: the ring quasi-finite
  and Noether-normalization hits do not contain the prescribed image field
  over an arbitrary base.

The item statement, source, proof, proof dependencies, and stage-1 review are
unchanged. Only its Lean record and the added existing notion in `stmt_deps`
are delivered. There are no new nodes, dependency repairs, statement disputes,
or statement corrections. The prior Q69 merge is a stage-1 split and contains
no Lean record or statement module; this delivery supplies stage 2.

Validation: compiled with the prescribed `scompile.py` wrapper. An initial
line-break parsing error in the residue-field map was repaired, then the only
remaining line-length warning was repaired. The final file is checked again
by the dry-run and delivery wrapper before push.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
