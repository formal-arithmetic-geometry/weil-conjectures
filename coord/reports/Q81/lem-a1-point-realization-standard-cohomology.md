## Worker report

The module `Sheaf.Paper.PointRealizationStandardCohomology` states
`WeilConjectures.pointRealizationStandardCohomology`. Its conclusion is the existence of
a complete normalized comparison system, packaged as
`PointRealizationStandardCohomologyData`. No structure is selected from that existence
theorem. The only selected auxiliary data come from unique-existence theorems that
specify all map fields. All four theorem proofs are `sorry`.

The target categories are the existing ones, not new models. At a finite stage we compose
`pointRationalFibre` with its full-subcategory inclusion. At the common stage we compose
`pointQbarFibre` with `DerivedCategory.pointFdQbarRealization`. This is fully faithful and
its distinguished predicate is defined by finite-stage distinguished triangles. Ordinary
cohomology and standard halves can therefore be expressed in the ambient module derived
categories without changing the categories or their morphisms. The common-stage descent
equations additionally specify the finite-stage representatives of the cohomology maps;
no arbitrary functor to D(Ω) replaces the recorded point functor.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Fixed p,a,q,k₀,k with k the fixed algebraic closure | `D : FiniteFieldDatum.{u}`; source scheme literally `Spec (.of D.k)` |
| Prime ℓ distinct from p | `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p` |
| Fixed algebraic closure Ω of Q_l | `Ω : Type u`, `[Field Ω]`, `[Algebra (Padic l) Ω]`, `[IsAlgClosure (Padic l) Ω]` |
| Finite E and its valuation ring/uniformizer | Finite fields in `finite`, `scalar`, `integral`, `localization` use the recorded finite-dimensional Padic-algebras; all categories reuse `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer` through the recorded sf definitions |
| Derived-complete integral category | `sfIntegralConstructibleCategory`, with actual completed coefficient sheaves and uniform bounds on every derived reduction |
| Rationalization and common-stage category | `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`, `generalAlgebraicallyClosedConstructibleCategory` |
| Standard source t-structures | `pointRealizationSourceT` and `pointRealizationCommonT` abbreviate the recorded unique sf standard t-structures; `pointRealizationIntegralT` is the induced ambient standard structure using the published truncation-closure theorem |
| The specified Fib_E and Fib_Ω, including Γ(-) tensor E | `pointRealizationAmbient`, `pointRealizationCommonAmbient`; `pointRealizationIntegralNormalization` has exactly the components of the recorded `pointRationalNormalization`, retaining its actual size-lift counit and coefficient comparison |
| Ordinary target t-structure | `DerivedCategory.TStructure.t` on the actual ambient D(ModuleCat E) or D(ModuleCat Ω) |
| Exact and t-exact | `PointRealizationComparison.commShift`, `.exact` (the existing `Functor.IsTriangulated`), `.tExact` (the existing `Functor.IsTExact`) in the `finite` and `common` fields |
| Every integer j and every object C, natural δ | `PointRealizationComparison.delta j` is a natural isomorphism, hence includes natural inverses and naturality for every object and morphism |
| δ induced by canonical truncation maps | `.upper_counit` and `.lower_unit` fix the upper/lower natural isomorphisms; `.delta` is their literal composite with the shift comparison; its source and target use the recorded `constructibleTruncationCohomology` |
| Integral normalization at C=Q C₀ | `integral_normalization`: the Q comparison followed by the finite δ and size lift equals the integral inclusion comparison followed by the canonical exact sections/tensor comparison, conjugated by the recorded `pointRationalNormalization` |
| Both sides identify with Γ(s,H^j C₀) tensor E | The right path of `integral_normalization` is exactly good integral cohomology through the full inclusion, followed by exact completed sections and fraction-field tensor. `pointExactDerivedComparison` fixes its shifts and good-truncation comparisons to the upstream exact-functor API, so its cohomology comparison is the cycle/kernel/quotient comparison, not a freely chosen isomorphism |
| Heart sent to degree zero | `heart` and `common_heart` quantify over every j≠0 and assert `IsZero` of the actual ordinary homology module |
| The specified φ for E⊆L | `pointRealizationScalarIso` is `pointRationalFibreScalarIso` through the full target embedding; that dependency fixes it by the sections-tensor/completion normalization on all integral representatives |
| Scalar/cohomology square | `scalar_square`, expanded in `PointRealizationCohomologySquare`: the source scalar/cohomology comparison, δ_L, H^j(φ), φ at H^j C, tensor(δ_E), and target scalar/cohomology comparison appear in order with matching endpoints |
| Canonical source scalar shifts | `scalar_shift` fixes the rational shift-by-one comparison to the localized, ordinary-tensor-normalized integral shift from the existing general coefficient interface; coherent integer shifts determine the remaining shifts |
| Identity normalization at L=E | First conjunct of `PointRealizationScalarCoherence`, using the actual `sfRationalScalarUnit` and `DerivedCategory.fieldScalarUnit` |
| E⊆L⊆M, tensor associators | Second conjunct of `PointRealizationScalarCoherence`, using `sfRationalScalarComp` and `DerivedCategory.fieldScalarTower`, with the actual point φ on both paths |
| Composition of squares | All `scalar_square` equations hold for every extension; the explicit φ tower equality identifies the outer boundary of pasted squares. Functoriality of cohomology applies the same tower equality to the other boundary. No extra associator can be selected |
| Common-stage cohomology at a common finite stage, compatible with every extension | `stage_transport` uses the specified Shrink equivalence; `inclusion_shift` fixes the recorded stage inclusion shift; `common_square` identifies the common δ with the finite δ after actual scalar extension to Ω. It quantifies over the comparison whose every component is the identity on the realized finite-stage object; the separately stated unique-existence normalization supplies precisely this comparison, so the clause is not conditional on extra data. The finite scalar squares and tower equality give agreement under every further extension, including repeated stages |

Finite fields are quantified using the existing abstract finite-dimensional Padic-algebra
interface. In particular every finite subfield of Ω is included. This is equivalent to
using its embedding in the fixed algebraic closure: all maps used are Padic-algebra
homomorphisms, and every finite extension embeds in Ω. For actual common-stage indices,
the module uses `AlgebraicallyClosedCoefficients.Coefficient.{u}` and the already recorded
`Shrink.algEquiv` transport to the actual subfield, without imposing any new size equality.
The shared universe u is the universe of the existing point-fibre interface; generic
comparison helpers bind all object and morphism universes independently.

Dependencies read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` (full fields and instance declarations read).
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public `CoefficientExtension` import: `Padic.finite_coefficientExtensionRing`, `coefficientExtensionIntegers`, `coefficientExtensionUniformizer` and the complete coefficient construction signatures/docstrings.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `generalAlgebraicallyClosedConstructibleCategory`, `Stage`, `inclusion`, `integralScalarCommShift_existsUnique`, and the normalized stage shifts/transitions.
- `Sheaf.Paper.SfConstructibleHeart`: `sfIntegralStandardClass`, `sfRationalStandardClass`, `sfCommonStageStandardClass`, `sfRationalStandardTStructure`, `sfCommonStageStandardTStructure` (source, defining unique-existence statements and docstrings read).
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`, `pointQbarFibre`, `pointRationalFibreScalarIso`, `pointRationalNormalization`, `pointStageFibre`; read the exact functor types, tensor-Hom specification, component formulas, scalar normalization, size transport and common-stage representative formulas.
- Proof-plan imports are the recorded modules for integral stratified-perfect characterization, integral/localized t-structures, point exact sections, point scalar sections, completed-scalar shift, sections-tensor shift, generic t-exact truncation comparison, constructible truncations, rationalization and the point common-stage target. The coefficient-complex-rationalization node has no recorded module, so no invented import is added for it.
- The Mathlib dependency `CategoryTheory.Functor.preservesHomologyOfExact` was read at `Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean:60`; it requires preservation of finite limits and finite colimits and gives the existing homology-preservation class. The exact-derived-functor truncation, homology and shift interfaces in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` were also read.

Edge cases checked before and during writing: zero objects and acyclic integral
representatives (including torsion killed by rationalization); all integer j, with no
nonnegative-degree restriction; all standard bounds in `IsTExact`; heart and shifted
heart objects; identity E=E and repeated fields in a tower; arbitrary non-strict coefficient
inclusions; the base finite coefficient field; actual Shrink coefficient transport at
common stages. The specified base is Spec of a field and is nonempty, so an empty-scheme
hypothesis is neither added nor removed. ℓ≠p and primality are retained; no residue-characteristic
case covered by the node is dropped. No finite-level truncation/inverse-limit interchange
is assumed. Definitions contain real data, with named proof obligations where needed.

Searches actually run through the prescribed logged wrapper:

- LeanFinder: `Point realization of rational constructible pro etale complexes commutes with standard cohomology and scalar extension`. Eight hits, on standard etale pairs, Kaehler differentials and the etale locus; none states this theorem.
- Loogle: `Functor.mapDerivedCategory, TStructure`. Zero hits, unknown identifier `Functor.mapDerivedCategory` reported by the service; recorded as an unsuccessful query, not as evidence of absence of the exact-functor API.
- LeanSearch: `An exact t-exact functor commutes with cohomology naturally and with scalar extension`. Eight hits, on exact-functor Ext maps, homology preservation and module scalar extension. Useful generic infrastructure, no point-realization/coefficient-coherence theorem.
- Mathlib grep: `pointRationalFibre|pointQbarFibre|homologyFunctorIso`. Fifteen hits, all generic homology functor isomorphisms; none of the specified point/coefficient statement.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for point-realization/cohomology names, and the exact node id in `lean/WeilConjectures` and `dag/lean_names_upstream.json`: no existing exact statement. The relevant upstream field-coefficient cohomology file was opened; it defines cohomology for a different nonlocalized field-sheaf interface, so it is not this theorem. The new declaration names were also searched in both project roots and Mathlib; no collision.

Source checked directly: the local Bhatt--Scholze PDF, Proposition 6.8.11(3)
(boundedness and constructible cohomology) and Proposition 6.8.14 (finite-stage and
rationalization equivalences), using `pdftotext -layout`; the eight-step exact-sections
coherence argument is the node's own explicitly identified agent argument. There is
no statement correction, no disputed statement, no new DAG node and no dependency repair.

## Second reading by Q81

Second pass by the same dispatcher worker (the task explicitly prohibits starting other
agents); the maintainer's independent review remains separate. Reopened the node and the
finished Lean signatures and checked every row above against the actual fields and maps.
The initial square had the inverse source comparison, whose endpoints did not match;
this was corrected to the forward `PT.delta` before delivery. Explicit module and Shrink
universes were added where inference selected a larger target, preserving the recorded
categories. The scalar shift is now explicitly normalized by the published integral
shift, and the common-stage inclusion shift is fixed to its existing instance. Checked
that the integral normalization uses the actual size-lift and exact sections/tensor
comparisons; that δ is constructed from the characterized truncation isomorphisms;
that identity and repeated-field towers are included; and that no theorem is proved.
All definition data are explicit constructions or uniquely specified maps. No item
field outside `lean` is changed.

Validation: prescribed scompile.py server confirmation passed cleanly in 55.1 seconds
(nice 19, two threads, unchanged 60-second limit). The common-stage scalar term uses
`pointStageTargetComparison` to expose its exact source and target, keeping the
canonical comparison constructed from the same upstream exact-functor data.
No compiler settings or tool scripts were changed.
