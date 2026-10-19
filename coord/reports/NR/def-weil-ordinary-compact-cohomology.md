## Worker report

Repaired the returned packet rather than re-pushing its compiling marker structure.
The owning module is `Sheaf.Paper.OrdinaryCompactCohomology`, and the primary
declaration is now `WeilConjectures.ordinaryCompactCohomology`. Its value is the
tuple of the actual section/cohomology operations at all four coefficient levels,
the point equivalences, and the constant/twisted specializations. There is no
`OrdinaryCompactCohomologyData` marker structure. All 48 owning declarations are
listed in `lean.declarations`; definitions contain actual constructions and this
module introduces no theorem, axiom, or sorry.

Source reread: current blueprint main-20261015,
`sec-six-functors-basics/sk-def-sf-admissible/def-weil-ordinary-compact-cohomology.md`.
The node statement is unchanged. Its statement dependencies gain the three
already published nodes used explicitly: `lem-sf-integral-direct-image-constructible`,
`def-weil-derived-pullback-tensor-hom`, and `lem-weil-point-fibre-equivalence`.
The saved node and current shared node agreed outside `lean` before these additions.
The prescribed delivery wrapper builds the repair on the current server base;
no direct Git command or edit was made in a read-only checkout.

Hypothesis-by-hypothesis correspondence:

| Source | Lean rendering |
| --- | --- |
| Global p,a,q,k₀,k, with q=p^a and k the fixed algebraic closure | `D : FiniteFieldDatum.{u}`; its fields include primality, positive a, cardinality and algebraic closure |
| Prime ℓ≠p | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` |
| Chosen Q̄ℓ | `(Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]` |
| Finite E/ℚℓ inside Ω | `(E₀ : Padic.FiniteCoefficientFields l Ω)` in the primary bundle; the canonical equivalent small field is `Coefficient.{u} l Ω E₀` |
| O_E, uniformizer, A_(E,n) | Existing `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionRing` on that field |
| Positive level n, including n=1 | `(n : ℕ) (hn : 1 ≤ n)`; reindex published j+1 constants/twists with `j=n-1` and `Nat.sub_add_cancel hn` |
| Arbitrary separated finite-type k-scheme Y | `(Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]` and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` instances on its structure morphism |
| a_Y:Y→Spec k | `Y ↘ Spec (.of D.k)`; Spec k is given its identity structure when invoking the base-relative APIs |
| Compact-support construction | `c : Compactification (Y ↘ Spec (.of D.k))`, the representative prescribed by the dependency; no properness or nonemptiness assumption on Y |
| Every cohomological degree and twist | `(i : ℤ)` and `(m : ℤ)` without sign restrictions |
| A Weil complex, when used | A finite-type `Y₀ : Over (Spec (.of D.k₀))`, its geometric fibre with the same scheme hypotheses, and the recorded `sfWeilComplex`/`sfCommonStageWeilComplex` |

Clause-by-clause correspondence:

| Source clause | Concrete implementation |
| --- | --- |
| Displayed Fib_s equivalences and the Q̄ℓ stagewise target | `cohomologyPointEquivalences` packages `pointFiniteFibre`, `pointIntegralFibre`, `pointRationalFibre`, `pointQbarFibre` using `point_fibre_equivalence`; its inverse data come from equivalence of these specified functors |
| Finite RΓ=Fib_s(Ra_*K), RΓ_c=Fib_s(Ra_!K) for K∈D^b_c | `finiteConstructibleImages` uses `directImages_constructible` for these exact two objects; `finiteConstructibleSections` applies `pointFiniteFibre`, landing in `pointFiniteCohomology.FullSubcategory` |
| Finite H^i and H_c^i | `finiteConstructibleCohomology` applies `coefficientFiniteCohomology` to those two point complexes |
| Ambient finite versions used for coefficient abbreviations | Retained `finiteOrdinarySections`, `finiteCompactSections` evaluate the identical finite direct images by `pointFiniteSections.mapDerivedCategory`; their cohomology functions apply `homologyFunctor` |
| Integral Ra_* | `integralImage` selects the recorded `SfIntegralDirectImage` Roos presentation using `sfIntegralDirectImage_constructible`; the limit property determines its object up to isomorphism, and that theorem supplies membership in `sfIntegralConstructibleCategory` |
| Integral RΓ and RΓ_c | `integralOrdinarySections` applies `pointIntegralFibre` to `integralImage`; `integralCompactSections` applies the same fibre to `sfIntegralCompactSupportValue` |
| Integral H^i and H_c^i | `integralOrdinaryCohomology`, `integralCompactCohomology` apply `coefficientFgCohomology` to the corresponding point complexes |
| Rational Ra_* and Ra_! | `rationalImage` rationalizes `integralImage` on `K.obj`; the compact construction uses `sfRationalCompactSupportValue` on the same integral representative |
| Rational RΓ, RΓ_c, H^i, H_c^i | `rationalOrdinarySections`/`rationalCompactSections` use `pointRationalFibre`; their cohomology functions use `coefficientFdCohomology E i` |
| Q̄ℓ Ra_* at every stage | `qbarImage K = (K.stage, rationalImage ... K.obj)`, in `generalAlgebraicallyClosedConstructibleCategory`; the finite field of definition is retained |
| Q̄ℓ Ra_! | `qbarCompactSections` uses the published `sfQbarCompactSupportValue` at `K.stage` with its actual integral representative |
| Q̄ℓ RΓ, RΓ_c, H^i, H_c^i | `qbarOrdinarySections`/`qbarCompactSections` apply `pointQbarFibre`; `qbarOrdinaryCohomology`/`qbarCompactCohomology` apply `coefficientQbarCohomology`, hence Ω⊗_E H^i of the recorded finite-stage complex |
| (A_(E,n))_Y | `finiteCohomologyCoefficient` is the recorded `finiteConstantCoefficientObject` at exponent n, reindexed from j+1 |
| Completed integral Λ_Y | `integralCohomologyCoefficient` uses `constantWeilIntegralObject`, whose underlying data are the recorded `integralConstantCoefficientObject` |
| Rational Λ_Y | `rationalCohomologyCoefficient` uses `constantWeilRationalObject`, the actual raw rationalization of that completed constant object |
| Algebraically closed Λ_Y | `qbarCohomologyCoefficient E₀` uses the underlying complex of the recorded `AlgebraicallyClosedCoefficients.constantCoefficientPair`; only the constructibility proof and intrinsic rational wrapper are changed |
| H^i(Y,Λ), H_c^i(Y,Λ), all four Λ | `finiteConstantCohomology`, `integralConstantCohomology`, `rationalConstantCohomology`, `qbarConstantCohomology` are pairs of the corresponding ordinary/compact functions evaluated on exactly those coefficient objects |
| Λ_Y(m)=Λ_Y⊗^LΛ(m)_Y, finite level | `finiteTwistedCoefficient n hn m` applies the recorded `finiteComplexTwist` to `finiteConstantCoefficientObject`, with the same positive-level reindexing |
| Λ_Y(m), integral level | `integralTwistedCoefficient` is `constructibleIntegralTensor` of the constant coefficient object and `intrinsicIntegralCoefficientTwist ... m` |
| Λ_Y(m), rational level | `rationalTwistedCoefficient` rationalizes that very integral derived tensor |
| Λ_Y(m), Q̄ℓ level | `qbarTwistedCoefficient` applies `intrinsicQbarComplexTwistFunctor` to `qbarCohomologyCoefficient`, using the recorded common-stage derived tensor |
| H^i(Y,Λ(m)), H_c^i(Y,Λ(m)), every m∈ℤ, all four Λ | `finiteTwistedCohomology`, `integralTwistedCohomology`, `rationalTwistedCohomology`, `qbarTwistedCohomology` evaluate both cohomology constructions on these actual twisted objects |
| In particular ℚℓ(m) | Specialize the rational helpers to `E = ℚ_[l]`; the bundle also permits `E₀ = Padic.finiteCoefficientBase l Ω`, the equivalent small ℚℓ model |
| Canonical E_Y Weil structure | `constantWeilCohomology` retains `constantWeilRationalSheaf` itself, and applies `weilCohomology` to its underlying Weil complex |
| Canonical (Q̄ℓ)_Y Weil structure | `qbarConstantWeilCohomology` retains `constantWeilAlgebraicallyClosedSheaf`, and applies `qbarWeilSheafCohomology` |
| Four symbols for Weil complexes mean application after For | `weilSections`, `weilCohomology` use `sfWeilForget`; `qbarWeilSections`, `qbarWeilCohomology` use `sfCommonStageWeilForget`; the sheaf specialization accepts the recorded `sfCommonStageWeilSheaf` |
| Finite-dimensional dimension, trace, determinant | `cohomologyLinearAlgebra F V hV` returns precisely `Module.finrank F V`, `LinearMap.trace F V`, and `LinearMap.det` |

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`: `intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `generalAlgebraicallyClosedConstructibleCategory` and its literal stage/object pair.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`, with its finite-image tower and Roos triangle.
- `Sheaf.Paper.SfIntegralDirectImageConstructible`: `sfIntegralDirectImage_constructible`.
- `Sheaf.Paper.DirectImagesConstructible`: `finiteFieldDatumPrimeUnit`, `directImages_constructible`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFiniteSections`, `pointFiniteFibre`, `pointIntegralFibre`, `pointRationalFibre`, `pointQbarFibre`.
- `Sheaf.Paper.PointFibreEquivalence`: `point_fibre_equivalence`.
- `Sheaf.Paper.CoefficientCohomologyModules`: `coefficientFiniteCohomology`, `coefficientFgCohomology`, `coefficientFdCohomology`, `coefficientQbarCohomology`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `sfIntrinsicCompactSupport` (the preserved intrinsic presentation of the recorded proper/open formula).
- `Sheaf.Paper.QcqsCompactSupportRealization` reexports `IntegralRationalQbarCompactSupport`: `sfIntegralCompactSupportValue`, `sfRationalCompactSupportValue`, `sfQbarCompactSupportValue`.
- `Sheaf.Paper.ConstantCoefficientObjectsConstructible`: `finiteConstantCoefficientObject`, `integralConstantCoefficientObject`, `integralConstantCoefficient_constructible`, `rationalConstantCoefficientObject`, `constantCoefficientPair`.
- `Sheaf.Paper.ConstantWeilStructure`: `constantWeilIntegralObject`, `constantWeilRationalObject`, `constantWeilRationalSheaf`, `constantWeilAlgebraicallyClosedSheaf`.
- `Sheaf.Paper.SfWeilSheafComplex`: the rational/common-stage Weil complexes, Weil sheaves and forgetful functors.
- `Sheaf.Paper.PbcCoefficientTwists` reexports `IntrinsicCoefficientTwists` and `CoefficientTwistsDetailed`: `finiteComplexTwist`, `intrinsicIntegralCoefficientTwist`, `intrinsicQbarComplexTwistFunctor`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralTensor`, and the common-stage tensor used by the recorded twist.
- `Sheaf.Paper.SmoothPurityQbar`: `smoothQbarResidueInvertible`; invertibility is constructed from the base field and not assumed of Y.
- Mathlib: `Scheme.ProEt`/`ProEt.topology`, the structure-morphism properties, `DerivedCategory.homologyFunctor`, `Module.finrank`, `LinearMap.trace`, `LinearMap.det`, `FiniteDimensional`.

Edge cases checked by reading the constructions: n=1 reindexes to j=0, hence
exponent 1; n=0 is excluded by exactly hn, rather than silently becoming exponent
1. The signed twist branches include m=0, positive powers and negative dual
powers through the recorded APIs. All degrees i, including negative degrees,
remain integers. Empty schemes, zero complexes, and zero-dimensional coefficient
spaces add no nonemptiness condition. The arbitrary k-scheme clauses use no
Y₀ or descent assumption; Y₀ appears only where a Weil complex/structure requires
it. The ℚℓ specialization and least finite coefficient field are included.
Q̄ℓ inputs retain their own finite stage, independent of the chosen E₀ used for
the other three coefficients. Small pro-etale objects remain in universe u+1
and arrows in u; no equality of those universes is imposed.

Searches repeated during repair: `msearch.py ... leanfinder "ordinary and
compactly supported cohomology with Tate twists and algebraically closed l-adic
coefficients"` returned eight generic group/continuous-cohomology hits, none
with these scheme/coefficient constructions. `msearch.py ... loogle
"ordinaryCompactCohomology, compactCohomology, coefficientQbarCohomology"`
returned zero hits (ordinaryCompactCohomology unknown). `msearch.py ... grep
"compact.*[Cc]ohomology|ordinary.*[Cc]ohomology" AlgebraicGeometry` returned
zero hits. `rg` for the item id, primary and retained helper names through
`WeilConjectures/` and project `lean/Sheaf` found only the direct-image and
coefficient-cohomology dependencies referring to the node, no implementation of
this combined notion. Existing component constructions were reused throughout.

No new node, dependency repair, statement correction or disputed statement.

## Second reading by NR

The dispatcher prohibits starting other agents, so this is an explicit in-thread
second reading of the complete node, source paragraph, module and declaration
record. It is not represented as an independent agent's approval.

The initial dry run passed for the saved packet, but opening its actual main
structure exposed that every numbered return remained unresolved. The marker
field supplied none of the definitions claimed by the report. That declaration
has been removed and replaced by the concrete tuple, with every helper recorded.
The four coefficient levels were then checked separately against both displayed
section formulas and both cohomology formulas. This caught the missing Q̄ℓ
branch and the distinction between an ambient finite complex and the displayed
D^b_fin target; the repaired packet includes `finiteConstructibleImages`,
`finiteConstructibleSections` and `finiteConstructibleCohomology` for that exact
domain/codomain, using the existing preservation theorem. Integral ordinary image
now uses the prescribed Roos tower rather than merely naming an ambient
completed-sheaf pushforward.

For the coefficient paragraph, each Λ_Y was followed into the arguments of its
ordinary and compact cohomology, and then each Λ_Y(m) was followed into both
cohomology functions, for all four Λ. The previous finite sheaf-only twist was
not such an argument; the repaired finite helper is a derived object and is
actually passed to both cohomologies. The published finite API's exponent j+1
was checked against the node's n, giving the explicit n-1 transport. Integral,
rational and Q̄ℓ signed twists use the recorded derived-tensor constructions.
The canonical rational and algebraically closed constant Weil sheaves are
retained as actual data; both forgetful branches cover complexes, and the Q̄ℓ
sheaf helper uses `sfCommonStageWeilSheaf` as requested. The final linear-algebra
clause uses Mathlib's three definitions.

H8 was checked mechanically against every definition: all have source/blueprint
docstrings and the module has its own source docstring. H9/H2 were checked against
the JSON and source: no duplicate `include`, unused prime-invertibility wrapper,
marker field or missing helper record remains; all variables and universes are
explicit, lines are at most 100 characters, and the recorded signature is copied
verbatim. The source statement and the dependency nodes were not rewritten.
Validation: `scompile.py NR def-weil-ordinary-compact-cohomology` compiled the
complete module in the sandbox (25.6 s) and as the library file (25.2 s), with
no warnings. The final `deliver2.py ... --no-push` printed
`OK (dry run): commit 47d0c94d24 passes the preflight and compiles; nothing pushed`.
The report is updated only to record these completed checks before the push.
