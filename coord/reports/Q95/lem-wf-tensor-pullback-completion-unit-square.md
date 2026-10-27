## Worker report

This delivery states `WeilConjectures.wfTensorPullbackCompletionUnitSquare`, with a
single postponed proof. It keeps the integral bounded constructible complete category,
ordinary tensor, intrinsic Koszul completion and geometric Frobenius of the recorded
dependencies. The helper definitions only name the maps and equations in this node;
they introduce no alternative coefficient category, tensor, completion or unit.

The source read is the current blueprint at
`literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md`,
penultimate sentence, together with the full specified model in `def-wf-tensor-product`
and all four proof steps of this node.

Hypotheses and clauses:

- `D : FiniteFieldDatum` contains primes p, q=p^a with a>=1, the finite field and its
  algebraic closure. `c : D.CoefficientDatum` contains the distinct coefficient prime
  and its fixed algebraic closure; `E : Padic.FiniteCoefficientFields c.l c.Qbar`
  is a finite intermediate extension. These are the same finite-stage data already
  used by `WeilD`, rather than an arbitrary coefficient ring in the main theorem.
- `X₀ : Over (Spec (.of D.k₀))`, `IsSeparated`, `LocallyOfFiniteType` and
  `QuasiCompact` express separated finite type. `D.geometricFiber X₀` is W and
  `D.geometricFrobenius X₀` is id times the inverse q-power automorphism.
- `pbcStageDatum` and `pbcStageUniformizer` are the established valuation-ring datum
  and chosen uniformizer, transported by the existing Shrink equivalence. The
  coefficient sheaf is `pbcAdicCompletion`; it is never identified with constant R.
- `M N : PbcBoundedConstructibleComplete ...` are precisely integral inputs in I_E.
  `wfOrdinaryDerivedTensor` defines T and, after `pbcIsoAmbientPullback`, T'.
- `DerivedSquare` states H(eta_T);b = a;eta_T', using Lean's left-to-right `≫`.
  `ordinary` is `proEtaleCanonicalTensorComparison` on `wfTensorModel`.
  `completed` is the exact ambient composite underlying `wfIntegralTensorPullback`:
  `wfPullbackCompletion` followed by completion applied to `ordinary`.
  Both units are `wfCompletionUnit`, i.e. the specified intrinsic unit with its
  genuine localization representative and realization.
- `StrictSquare` quantifies over every flat-term K-flat U,V and their realizations
  of M,N in the equivalent completed quotient-ring presentation. This presentation
  is reused from `IntrinsicCompletionCompleted`; its canonical comparison to
  `pbcAdicCompletion` is `pbcCompletedComparison`, induced by finite quotient maps.
- `coefficientIso` conjugates `completedCoefficientMap` by that canonical comparison.
  `NormalizedConstants` fixes its module comparison on every constant generator,
  via the canonical module adjunction's unit; the comparison is not an arbitrary iso.
- `koszul` is the existing rank-one positive-power Koszul complex: index m means
  exponent m+1, covering all positive powers. The already constructed transition is
  the uniformizer in degree -1 and identity in degree 0. Naturality of the constant
  comparison with that module map retains these transitions.
- `alpha` is the inverse of `proEtaleTensorPullbackTotalIso`. `beta` tensors this
  exact comparison with the induced constant-Koszul comparison. `NormalizedFiber`
  fixes delta on every product projection by beta H(pr_m), and fixes b on BOTH
  fiber coordinates using the original mapping-cocone projections.
- `unit` is exactly `completedKoszulUnitComplex`, whose data is the original
  `mappingCocone.lift` of the product augmentation and zero cochain. The strict
  conjunct asserts b H(unit)=unit' alpha as equality of actual chain maps. The last
  equation applies `DerivedCategory.Q` to those same maps and their composites.

Dependency declarations read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public import:
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, finite rings.
- `Sheaf.Paper.PbcWeilCategory`: `WeilD`, `weilFrobeniusPullback`, and the public
  finite-field/geometric-Frobenius and exact coefficient-transport interfaces.
- `Sheaf.Paper.WeilTensorProduct`: `wfTensorModel`, `wfOrdinaryDerivedTensor`,
  `wfPullbackCompletion`, `wfIntegralTensorPullback`, `wfUniformizer_generates`.
- `Sheaf.Paper.IntrinsicCompletionCompleted`: `completedKoszulPowerSheaf`,
  `completedKoszulTensor`, `completedKoszulProduct`, `completedKoszulOneSubShift`,
  `completedKoszulFiber`, `completedKoszulUnitComplex`.
- `Sheaf.Paper.IntegralUniformCoefficient` and its public imports:
  `PbcBoundedConstructibleComplete`, its unchanged three-clause predicate, the
  finite-extension coefficient specialization and the actual valuation ring.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage_equivalence`, its independent coefficient universes,
  and the retained canonical constant coefficient and exact module transport APIs.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, publicly retaining
  `Sheaf.Paper.ProEtaleCanonicalTensorPullback`: the representative-normalized
  `proEtaleCanonicalTensorComparison` and `proEtaleTensorPullbackTotalIso`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the localization functor `DerivedCategory.Q`.

Edge cases checked: zero M or N, empty W₀, exponent a=1, level m=0 (power one),
ramified finite E, and arbitrary unbounded flat K-flat representatives of bounded
constructible derived inputs. No nonzero section, tensor generator, or nonempty site
is assumed. The fiber's zero second unit coordinate is retained. The site remains
object universe u+1 and morphism universe u; coefficient and module size is u+1.

Searches (all through the prescribed wrapper unless stated):

- LeanFinder: "inverse image tensor comparison preserves actual Koszul completion
  unit on mapping fiber chain complexes". Eight hits: homological-complex unitors,
  tensor-unit instances and a Dold--Kan comparison; no normalized completion square.
- Loogle: "CategoryTheory.NatTrans.naturality, CochainComplex.mappingCone".
  Zero hits. General naturality would not specify this chain-level fiber map.
- LeanSearch: "exact inverse image preserves the actual Koszul mapping fiber
  completion unit under canonical tensor comparison". Eight hits, including
  image-preservation maps, ordinary adic completion and right unitors; no match.
- Mathlib grep: `Koszul.*pullback|pullback.*Koszul|completion.*unit`.
  Ten hits in ordinary adic completion/valued-field files; none has this sheaf square.
- rg in `lean/WeilConjectures` for the node id: no match. Concept search for
  intrinsic completion/Koszul comparisons gives other affine and algebraic results.
- rg in `lean/Sheaf`: the ordinary derived unit-normalized comparison exists in
  `WeilTensorProduct`, but it does not state the strict normalized tensor/fiber
  equation for all specified representatives. `AutomorphismCompletionUnitComparison`
  supplies only the derived universal-property comparison, and
  `ExactCompletedKoszulPullback` uses another completion interface. Neither states
  this node, as also recorded by the stage-1 review.

No node statement correction, new DAG node, or dependency repair is required.

Validation: the final delivered module compiled separately both as the sandbox
module and under its library module name with `scompile.py`, with no errors or
warnings. The two total-tensor helper definitions locally disable broad imported
smallness instances during elaboration; their mathematical definitions and site
universes are unchanged.

## Second reading by Q95

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
