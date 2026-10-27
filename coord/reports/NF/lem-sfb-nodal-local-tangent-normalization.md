## Worker report

The delivery states `AlgebraicGeometry.NodalLocal.tangent_normalization` in
`Sheaf.AlgebraicGeometry.NodalLocalTangentNormalization`. Its only postponed theorem is
this theorem, with the complete ten-step reviewed proof in its docstring. All definitions
have actual data. No proof is supplied. No statement correction or re-splitting is made.
Q02's reviewed stage-1 split is retained verbatim, including its two intermediate nodes.
The live item had no Lean record: its reviewed split is not a stage-2 declaration.

Source read: `literature/stacks-project/curves.tex`, remark-quadratic-extension (0CBT),
remark-trivial-quadratic-extension (0CBU), and lemma-split-node (0CBW). In particular, 0CBT
explicitly identifies constructions (2) and (3) and their scheme-normalization fibre;
its omitted comparison is exactly the calculation retained in the DAG proof.

The helper definitions assemble the recorded notions. `Normalization A` is literally
`integralClosure (A / nilradical A) (FractionRing (A / nilradical A))`. Its A-action factors
through the actual reduction. `normalizationIdeal A` is the extension of m, and
`ResidueAlgebra A` is its actual quotient. The scalar action is Mathlib's quotient-algebra
construction with `Ideal.le_comap_map`, not a chosen coefficient field. `tangentGrading A n`
is the range of the degree-n inclusion into the dependency's existing associated graded
ring, and `initialForm` is that inclusion applied to the quotient class. Thus neither the
associated graded ring nor its multiplication is duplicated. The theorem supplies the
unique grading structure on these fixed subgroups, as part of the mathematical assertion;
no definition chooses a grading or an isomorphism from an unproved existence theorem.

The following matches every hypothesis:

| Node hypothesis | Lean rendering |
| --- | --- |
| k is a field | `{k : Type u} [Field k]` |
| C is a scheme over k | `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))` |
| Locally finite type | `[LocallyOfFiniteType f]` |
| Equidimensional of dimension one | `hpure : C.IsPureDimension 1` |
| x is a closed point | `(x : C) (hx : x ∈ closedPoints C)` |
| Its structural residue extension is finite | `hfinite : (f.residueFieldAlgebraMap x).Finite` |
| The same extension is separable | `hsep : @Algebra.IsSeparable ... (f.residueFieldAlgebraMap x).toAlgebra` |
| An algebraic closure of k | `Ω`, `[Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]` |
| A geometric point over x | `xbar` in the actual pullback and `hxbar : pullback.fst ... xbar = x` |
| Its completed local ring is Ω[[u,v]]/(uv) | `hnode : Nonempty (CompletedLocalRing ... xbar ≃+* (MvPowerSeries (Fin 2) Ω / Ideal.span {X 0 * X 1}))` |

`A` is always the actual `C.presheaf.stalk x`; m is `IsLocalRing.maximalIdeal A`;
κ is the actual `C.residueField x`, definitionally the local residue field. No rationality
assumption κ=k, separability beyond the stated extension, characteristic restriction,
properness, separatedness, connectedness or global quasi-compactness is imposed.

The following matches every conclusion and its canonical character:

| Node clause | Lean rendering |
| --- | --- |
| The canonical κ-scheme isomorphism from tangent Proj to Spec(Aν/mAν) | `Comparison.iso`, `zeroIso`, `zeroIso_apply`, and `over_residue` |
| Proj is that of the actual m-adic associated graded ring | `tangentGrading` is the range grading on `Ideal.associatedGraded m`, and the existential `graded` is a `GradedRing` structure on precisely that family |
| The comparison is intrinsic, without a coordinate choice | `Comparison.normalized` specifies `in_n(a)/in_1(f)^n ↦ [b]` whenever `a = f^n b` in the actual normalization, on every admissible standard chart; `Comparison.unique` says that this specification determines the isomorphism |
| The chart specification is an equality of scheme morphisms | The last equation of `IsNormalized` compares the chart inclusion followed by the isomorphism with Mathlib's `Proj.basicOpenIsoSpec` followed by `Spec.map θ.symm` |
| The residue algebra is split quadratic or a separable quadratic field | `Comparison.quadratic`: either a κ-algebra equivalence with κ×κ, or `IsField E ∧ Algebra.IsSeparable κ E ∧ Module.finrank κ E = 2` |
| Spec(E) is canonically the reduced-normalization fibre | `Comparison.fiberIso`, `fiberIso_fst`, and `fiberIso_snd` give an isomorphism with `pullback C.fromReducedNormalization (C.fromSpecResidueField x)` over Spec κ |
| Its normalization map is the actual one | `normalizationLift_over` makes the lift of Spec(Aν) lie over the actual local-scheme map `C.fromSpecStalk x`; `fiberIso_fst` agrees with the quotient map to this lift |
| Natural under every pointed-local-ring isomorphism | `D.IsNatural` quantifies over every local-ring isomorphism to any local ring A', constructs the induced graded and normalization/residue maps, specifies them on representatives, and gives the commutative square with Mathlib's `Proj.map` |
| Two points after algebraic closure | `D.GeometricBranches` provides an isomorphism from `Spec (CompletedBranchAlgebra ... xbar)` to the scalar extension of the actual tangent Proj, and asserts `Nat.card` of that branch spectrum is 2 |
| These points correspond to the two branches of the normalized completed node | `CompletedBranchAlgebra` is the actual normalization of the completed geometric stalk, modulo the extended original geometric maximal ideal; this is the closed-fibre algebra of the normalized completed node |
| This is the same branch correspondence as the intrinsic local isomorphism | The two projection equations in `GeometricBranches` force the isomorphism to be induced by the specified normalization map and structural Ω-map, not by an arbitrary permutation |

The residue-field map used for scalar extension is also fixed: the existential `ω` is
inverse to the structural Ω-map to the geometric residue field; `ρ` is specified on the
residues of all elements of A by the actual geometric stalk map. In particular Ω is an
algebraic closure of κ through ρ, because κ/k is finite algebraic and Ω/k is algebraic
and algebraically closed. The completed branch ideal uses the extension of the maximal
ideal of the geometric stalk; it equals the maximal ideal of the completed local ring.
This spelling does not require an artificial local-ring instance as an additional
hypothesis on the completion. The normalization map ν extends the actual map from A to
the completed geometric stalk; regular denominators determine its value on the integral
closure. The residue map r is fixed on every quotient representative.

For naturality the graded map is specified on every `initialForm`, ν on the image of A,
and r on every normalization-residue class. These determine the induced maps uniquely:
initial forms span the graded ring, and every normalization element is a fraction of
original local-ring elements with a regular denominator. The target ring A' is arbitrary,
not an extra scheme or coefficient-field presentation. Its normalized comparison is
universally quantified; no existence of compatible maps is assumed, since all the
transported maps and the irrelevant-ideal condition are existential conclusions.

The two additions to `stmt_deps` are existing, already recorded definition nodes:
`def-weil-pure-dimension` for the exact equidimensional predicate and
`def-weil-pbc-integral-closure` for the literal local normalization construction.
There are no new nodes and no dependency replacements.

Dependency declarations read and used:

- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, as used by the recorded pure-dimension predicate.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`,
  `AlgebraicGeometry.Scheme.IsPureDimension` (every irreducible component has dimension 1).
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, `residue`, `fromSpecResidueField`.
  The structural base-field map is the existing `Scheme.Hom.residueFieldAlgebraMap` in
  `WeilConjectures.ZetaSeries`, read with its docstring and formula.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable`; its statement applies to the structural residue-field algebra.
- `def-weil-algebraic-closure`: the Mathlib match is `AlgebraicClosure` and
  `IsAlgClosure`, from `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` and `Basic`.
  The latter class is the one used, permitting any supplied algebraic closure.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`, with its ring/algebra structure from `AdicCompletion.Algebra`.
- `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic`,
  `MvPowerSeries`, applied to `Fin 2`.
- `def-weil-pbc-reduced-normalization`: `Sheaf.AlgebraicGeometry.ReducedNormalization`,
  `Scheme.reducedNormalization` and `Scheme.fromReducedNormalization`. The entire
  componentwise construction and its structural map were read.
- `def-weil-pbc-associated-graded-ring`:
  `WeilConjectures.RingTheory.AssociatedGradedRing`, `Ideal.associatedGradedPiece`,
  `Ideal.associatedGraded`, `Ideal.associatedGradedRingHom`, with the existing ring structure.
- `def-nagata-affine-proj`: `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`,
  `AlgebraicGeometry.Proj`; its structural map and standard charts in
  `ProjectiveSpectrum.Basic`, and its functorial map in `ProjectiveSpectrum.Functor`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `Spec.map`.
- `def-weil-pbc-integral-closure`: `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
  `integralClosure`, used with Mathlib's `FractionRing` of the actual reduced ring.

The already stated proof dependencies are imported as ordinary imports, including the
normalization/completion theorem, separable formal presentation, faithful-flat injection,
affine spectrum pullbacks, integral-closure localization, completion, total fractions,
relative normalization, and locally-Noetherian inheritance. The two new intermediate
stage-1 nodes, `lem-sfb-separable-node-quadratic-completion` and
`lem-sfb-quadratic-series-integral-closure`, have no Lean modules yet and are not restated
or re-split. Their use is retained in the proof docstring. All statement dependencies are
already available.

Edge cases checked before writing:

- Split crossing `uv=0`: E=κ×κ, both branches remain distinct; the statement does not
  require the original local ring to be a domain or its curve to be irreducible.
- A self-node on an irreducible curve: the semilocal normalization and its two residue
  points are covered by integral closure in total fractions, not by choosing one branch.
- A nonsplit real node with completed equation `u²+v²`: E is the quadratic field C over R;
  it has two points only after algebraic closure, as the statement requires.
- Characteristic two: `u²+uv+v²` over F₂ has nonsplit residue algebra F₄; `u(u+v)` has
  split residue algebra F₂×F₂. No division by 2 or nonzero characteristic hypothesis occurs.
- A double line is excluded by the given geometric ordinary-double-point hypothesis,
  not accepted as a separable quadratic residue algebra.
- A nonrational closed point with finite separable κ/k retains κ as the scalar field;
  the completed branch comparison specifies the embedding into Ω instead of setting κ=k.
- The empty scheme has pure dimension one vacuously but supplies no point x, so the theorem
  adds no assertion there. No hidden nonemptiness or connectedness hypothesis is needed.
- The denominator quantifier only admits regular generators of mAν; a degree-one form
  supported on just one split branch is correctly excluded. This preserves Q02's reviewed
  repair concerning admissible chart denominators.

Searches for an existing declaration:

- `msearch.py NF ... leanfinder`, query "The projectivized tangent cone of a nodal local
  ring is canonically its normalization fibre": 8 hits, all general relative-normalization
  declarations (`Scheme.Hom.normalization`, `normalizationDesc`, etc.), no nodal tangent
  comparison. The search succeeded.
- `msearch.py NF ... loogle`, query `"AlgebraicGeometry", "normalization"`: 12 hits,
  general relative normalization and its structural maps, no comparison with tangent Proj.
- `msearch.py NF ... grep`, query
  `nodal|[Tt]angent.*[Nn]ormali|[Nn]ormali.*[Tt]angent`, Mathlib subdirectory
  `AlgebraicGeometry`: 0 hits, successful search.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `nodal_local_tangent_normalization`, `nodalTangent`, and `localTangent`: only the
  citation in `NodalBranchDoubleCover.lean`'s proof plan, no declaration of the item.
  The requested `grep -rn` of the item id in `lean/WeilConjectures` also had no hits.
- Read the nearby `RationalNodeQuadraticCompletion`, `NodalPointLocalCriterion`,
  `NodalBranchScheme`, `NodalBranchDoubleCover`, and `NodalNormalizationQuotient` modules.
  They supply different notions or use this item; none states its conclusion.

No `STATEMENT-DISPUTED` flag or source fault was found. The only incomplete proof is the
requested statement theorem. The module compiled through the prescribed `scompile.py`;
final dry-run and delivery results are recorded by the delivery wrapper.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
