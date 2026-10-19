## Worker report

The delivery states `WeilConjectures.PointCompletedEvaluation.point_completed_evaluation`
in `Sheaf.Paper.PointCompletedEvaluation`. It changes only this node's `lean` record.
No natural-language statement, dependency, proof plan, or existing module is changed.
The three postponed theorems are `extension_existsUnique`, `towerBalancing_existsUnique`,
and `point_completed_evaluation`. Their docstrings give the construction/proof plans;
all are helpers or the conclusion of this same node and carry its blueprint tag.
All definitions contain real data. In particular the extension functor and balancing
isomorphism are chosen from uniqueness statements that fix their objects and maps,
never from a bare existence of an unspecified functor or isomorphism.

Clause-by-clause rendering:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Fixed finite-field datum and algebraic closure k | `D : FiniteFieldDatum.{u}`, with `D.k`; the point is always `Spec (.of D.k)` |
| Prime ell distinct from characteristic | `(l : ℕ) [Fact l.Prime]`, and main theorem binder `(hl : l ≠ D.p)` |
| Finite extension E/Q_ell, R its valuation ring and chosen uniformizer | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`; `R l E` abbreviates the dependency's valuation ring with its standard `ULift`; all quotient towers use the dependency's uniformizer and positive levels n+1 |
| Small pro-etale site and completed ring B | `B D l E` is `completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))`; object universe u+1, morphism universe u, coefficient/module universe u+1 |
| Bounded finite-projective complex P | `P : CochainComplex (ModuleCat.{u+1} (R l E)) ℤ`, bounds `a b : ℤ`, `P.IsStrictlyGE a`, `P.IsStrictlyLE b`, and `∀ i, Module.Projective (R l E) (P.X i) ∧ Module.Finite (R l E) (P.X i)` |
| P-dual = total Hom(P,R[0]) | `dual l E P := CochainComplex.moduleHomComplex P (ringComplex l E)`; the recorded Hom differential is retained |
| C = B tensor constant P and J = B tensor constant P-dual | `model D l E P` and `model D l E (dual l E P)`; `extension_existsUnique` fixes every object to `PointDerivedHom.extensionObject` and every map to `extensionMorphism`; `generator` is exactly the recorded sheafification image of b tensor x |
| Canonical J -> ambient derived internal Hom(C,B) is invertible | In `Result`, `homIso`, `_hom_normalized`, and `_derivedHom_isIso`; the derived arrow is `(sheafQ D l E).map homIso.hom ≫ IntegralHom.homModelMap ...`. The normalization is b tensor f acting on b' tensor x as bb'f(x), so the arrow is the canonical one |
| J, C, and ordinary derived C tensor J are derived-complete bounded constructible | `ctf_J`, `ctf_C`, and `_constructible_tensor`; `finiteTorConstructibleIntegral` has `sfIntegralConstructible` as its first conjunct. `good_C` and `good_J` say the displayed flat-term K-flat models compute the ordinary derived tensor `total`; they are conclusions, not added assumptions |
| The specified chi_Q uses actual quotient maps and zero shifted-product coordinate | `_coefficientCompletion_normalized` fixes `coefficientCompletion.hom` to the localization of `completedScalarIdentityUnit`; `_tensorCompletion_isIso` uses that identical unit on the ordinary tensor model. `completedScalarIdentityUnit_existsUnique` supplies exactly those two coordinates |
| Completed evaluation is the recorded completed tensor evaluation | `completedEvaluation` first uses `integralCompletedTensorComparison`, then the functorial Roos image of `towerBalancing`, then the identity scalar-completion functor applied to ordinary `evaluation`, then `coefficientCompletion.inv`. This is precisely Rlim of reduced evaluation followed by chi_B inverse. `towerBalancing_existsUnique` fixes the underlying strict tower map on every local tensor generator; `roosBalancing` maps this isomorphism through `integralOperationsRoosFunctor`, so its shifted component is fixed too |
| q_P(h)(x) = h(1 tensor x) | `q` and `_q_normalized`; the scalar inclusion is written explicitly with `pointIntegralSectionMap` to compare R-values and B-sections, and `homIso` identifies J with the ordinary Hom model |
| Canonical P = Gamma(C) | `unit` and `_unit_normalized`, degreewise x mapped to the actual `generator ... 1 x` |
| Canonical Gamma(B) = R for the evaluation target | `coefficientUnit` and `_coefficientUnit_normalized`, normalized to the actual constant-value map `pointIntegralSectionMap` |
| The canonical point tensor comparison tau | `tau` uses `pointIntegralTensorComparison ... S`, then the fixed exact-sections factorization and `unit.inv` in its first tensor factor. The theorem supplies S together with `PointIntegralTensorCanonical`; thus every quotient coordinate, zero shifted coordinate and inverse tensorator normalization is the one from the dependency |
| Gamma(completed evaluation) = ev_(P,R) (1 tensor q_P) tau in D(R) | The last equality of `Result`. Its left side takes actual derived sections and the coefficient target identification; its right side is `tau`, the tensor functor's map of identity and the derived q, `Functor.LaxMonoidal.μ (moduleQ l E) P (dual l E P)`, and the localized `ringEvaluation`. This is ordinary equality of morphisms, not HEq or just existence of an isomorphism |
| Factor order and signs | `_evaluation_normalized` and `_ringEvaluation_normalized` use argument first, dual second, and `(p*j).negOnePow`, exactly as the node's proof |

`Result` uses existentially bound normalized canonical maps and proof witnesses. These
are conclusions supplied for every bounded projective P, not input assumptions about
P or freely chosen replacements for canonical maps. S is supplied simultaneously for
all P and is required to satisfy the dependency's complete canonical normalization.
The extra finite-Tor and good-representative witnesses express properties of the fixed
perfect models needed to type the recorded tensorator and representative comparison.

Dependency declarations used (the recorded modules are imported publicly):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its public coefficient
  extension module): `Padic.finite_coefficientExtensionRing`,
  `Padic.coefficientExtensionIntegers`, uniformizer/ideal/quotient conventions.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses`, reexported completion.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, its topology.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex` (its bounded finite-projective model condition
  is written directly because the input is already a complex).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`:
  `SheafOfModules.siteSheafTensorRightMap` and its public general-universe tensor API;
  reused through the recorded point Hom/extension interface.
- `Sheaf.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`, through `sheafHom`.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `completedScalarIdentityUnit`, `completedScalarIdentityUnit_existsUnique`,
  `finiteFreeCompletedScalarComparison` and the exact identity scalar tower.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the integral operation is the ambient
  `integralCompletedTensor`/internal Hom, with no rational or finite specialization.
- `Sheaf.Paper.PointDerivedHomEvaluation`: `extensionObject`, `extensionMorphism`,
  `extensionElement`, `coefficientMap`, `scalar`, `homValue`, `sheafHom`, `total`,
  `totalElement`, and `point_derived_hom_evaluation` as the ordinary proof input.
- `Sheaf.Paper.PointFibreDerivedTensor`: `PointIntegralTensorData`,
  `PointIntegralTensorCanonical`, `pointIntegralTensorComparison`,
  `pointIntegralDerivedFactors`, and `pointFibreDerivedTensor`.

Every recorded proof-dependency module is imported without `public` unless already a
statement dependency. `lem-pod-connected-constant-h0` has no recorded Lean module and
is consequently not imported. Its mathematical use remains step 2 of the proof docstring.
There is no import cycle and no dependency-interface repair in this delivery.

Searches before construction:

- msearch `leanfinder`: “Evaluation of a perfect complex and its dual commutes with
  completed scalar extension to the pro-etale coefficient sheaf on an algebraically
  closed point”. Eight hits, including BDeRham and ordinary adic evaluation/formal
  etale results; none states this comparison.
- msearch `loogle`: `CochainComplex.moduleHomComplex, AdicCompletion`. No hit;
  `CochainComplex.moduleHomComplex` is a project name, unknown to the Mathlib service.
- msearch `grep`: `completed.*evaluation|evaluation.*completed|proetale.*perfect`.
  Zero Mathlib hits.
- msearch `leansearch`: “Derived evaluation of a perfect complex and its dual is
  compatible with completed tensor and sections at a pro-etale geometric point”.
  Eight ordinary perfect-pairing/module-dual hits, none about the strict quotient tower.
- `rg` in slopmaster2 `WeilConjectures`, shared `lean/Sheaf`, and the upstream-name
  index for the item id, `point_completed_evaluation`, `PointCompletedEvaluation`,
  and completed/evaluation combinations. No existing complete statement. The point
  Hom and point tensor modules are the correct separate inputs. The slice evaluation
  module concerns restriction of the dual-evaluation natural transformation, rather
  than this pointwise P tensor P-dual pairing, and is not a matching declaration.

Edge cases checked: the zero complex; degree-zero finite projective modules;
non-free projective summands; arbitrary negative degrees; bounds with a>b, which
force the zero model; positive quotient exponent 1 and every n+1; and vanishing
Hom components off p+j=0. Normalizations are stated in degree p+j=0 because the
coefficient complex vanishes in every other degree. Thus this restriction drops no
component. The Koszul sign is retained even for shifted complexes. The zero shifted
Roos coordinate is inherited from the actual completion unit, not omitted. The
common universe for k and E may be enlarged to contain both; the site still has
object size u+1 and morphism size u, and no object/morphism universe equality is imposed.

Elaboration: `sheafQ` explicitly uses the recorded standard localization; `moduleQ`
uses the same small-Hom localization as the recorded point fibre. The two broad
`PointDerivedHom.derivedSheaves`/`derivedModules` instances are disabled while this
file elaborates and restored at its end, so the file exports no instance removal.
Replacing a large dependent witness structure by an existential proposition avoided
expensive projection generation. No timeout or resource limit was raised.
No STATEMENT-DISPUTED flag or natural-language node fault was found.

## Second reading by N4

I re-read the source paragraph, node, all normalized maps and final equality after the
first draft. Per the dispatcher's explicit instruction I did not start another agent;
this is a second pass by the delivering worker, with independent review to be carried
out by the maintainer, not a claim of an independent worker review.

The pass checked the following correspondences against the actual file:
finite-field/ell/E binders; actual B and constant extension objects; both strict bounds
and finite/projective terms; the recorded Hom differential; canonical J-to-RHom map;
all three completeness/constructibility assertions; the prescribed coefficient and
tensor completion units; q on 1 tensor x; the unit P-to-sections; argument/dual order;
Koszul sign; the recorded point tensorator and both of its cone-coordinate constraints;
and equality with matching derived endpoints. The final equation has source sections
of the actual completed tensor and target R[0]. In particular it does not substitute
an arbitrary isomorphism for tau or assume the desired evaluation square.

The first formulation's localization inference mixed standard sheaf-localization
instances with the smaller ordinary-module localization. This was repaired with
explicit `sheafQ` and `moduleQ`, retaining the same mathematical categories and maps.
The proof-witness proposition carries every normalization explicitly, and unused
proof-binder names have leading underscores without suppressing warnings. No source
statement, statement dependency or coefficient notion needed correction.
