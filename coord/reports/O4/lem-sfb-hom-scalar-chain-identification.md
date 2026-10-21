## Worker report

Item: `lem-sfb-hom-scalar-chain-identification`, group O4, stage 2.
Module: `Sheaf.Algebra.Homology.StrictScalarHomChain`.
Main declaration: `SheafOfModules.StrictScalarHom.exists_scalarHomChainIdentification`.

The sole postponed theorem asserts simultaneous existence of the normalized ordinary
extension, chain isomorphisms nu and theta, alpha and the uniquely normalized sigma,
with the strict square and all input/coefficient compatibility equations. Its proof
is `sorry`; its docstring records all eleven steps of the node's proof, including
sheafification descent, signs, uniqueness, and coefficient compatibility. No proof
is supplied in this stage. All helper definitions have actual data. No object is
chosen from a merely existential postponed assertion.

The namespace's `Complex` is a transparent abbreviation of `CochainComplex` of the
recorded `ringedSiteModules`. The structures `Extension`, `Data`,
`CoefficientSquare` and `CoefficientCompatibility` package exactly the maps and
laws in this node; they introduce no replacement tensor, Hom, localization or
resolution. Their existence is the one assertion of this node, not an assumption
on the inputs. The package makes the many interdependent source/target types
readable and leaves each equality available to downstream proofs.

Hypotheses and clauses, individually:

| Node text | Lean rendering |
| --- | --- |
| A site small in the module universe | `{C : Type c} [Category.{v} C] {J : GrothendieckTopology C}`, with rings/modules at `max c v u`; site objects and arrows fit in that universe. `c`, `v`, `u` are independent. |
| Sheaves of commutative rings and their morphism phi | `R S : Sheaf J CommRingCat.{max c v u}`, `φ : R ⟶ S`; the theorem quantifies over all such rings and morphisms. |
| Ordinary sheafified extension E | `Extension.functor`, `obj_eq` and `map_eq` fix it to `changeOfRingsOfUniverses` and `changeOfRingsHomOfUniverses`. The tensor places S first. This is the existing sheafification of the sectionwise ordinary scalar tensor. |
| Restriction U | `restriction φ` is exactly Mathlib `restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)` applied termwise. |
| Extension to unbounded complexes | `Extension.complex` and `restriction` use `mapHomologicalComplex (.up ℤ)`. The index is all integers; no support restriction. |
| R-linear S tensor A | `scalarModule φ` restricts the unit S-module to R; `tensor φ` applies the existing `tensorLeft (scalarModule φ)` termwise. |
| Actual product Hom complex | Every Hom is `CategoryTheory.homComplex (R := ...)`; no abstract closed substitute or arbitrary Hom object occurs. |
| Local representative evaluation | `evaluate` uses `homComplexπ P N n i k h`, then evaluates the resulting slice-module map at `op (Over.mk (𝟙 V.unop))`. This is precisely the projection/identity-of-slice convention of `coefficientHomComponent` and `coefficientHomSectionEvaluation`, without invoking their K-injective resolution. |
| Natural chain iso nu | `Data.nu : tensor φ ≅ extension.complex ⋙ restriction φ`; a functor isomorphism includes input naturality. |
| nu(s tensor x) = s tensor x | `Data.nu_pure`, with `tensorSection` and `Extension.section`; these are the actual sheafification-unit images in the two presentations. |
| Chain iso theta | `Data.theta P N` has source `U homComplex_S (EP) N` and target `homComplex_R P (UN)`. Its inverse is part of the isomorphism. |
| theta(g)(x) = g(1 tensor x) on every slice/component | `Data.theta_evaluate` quantifies over `n i k`, `h : i + n = k`, every object `V`, every actual Hom section `g` and every local section `x`. Evaluation uses the chosen product projection. Since all objects and restrictions occur, the same rule applies over objects of every slice. |
| Every P,J,N and chain map q : EJ to N | `Data.sigma` takes `P A : Complex R`, `N : Complex S`, and `_q : extension.complex.obj A ⟶ N`; `A` denotes the node's complex J, avoiding collision with the topology J. |
| S-linear chain map sigma_q with the stated source and target | `Data.sigma` is a morphism in `Complex S` from `E homComplex_R P A` to `homComplex_S (EP) N`. |
| sigma_q(s tensor f)(t tensor p) = st q(1 tensor f(p)) | `SigmaFormula` and `Data.sigma_formula`, quantified in every degree and over every object, using actual pure sections and product evaluation on both sides. |
| Unique such S-linear chain map | `Data.sigma_unique` quantifies over every competing chain map satisfying `SigmaFormula`, and equates it to the supplied sigma. |
| alpha_S(s tensor f)(p) = s tensor f(p) | `Data.alpha` has source `tensor φ (homComplex_R P A)` and target `homComplex_R P (tensor φ A)`; `alpha_evaluate` specifies exactly this local formula. |
| Strict normalized square | `Data.square`: `nu_H.hom ≫ U.map sigma ≫ theta.hom = alpha ≫ homMap id nu_A.hom ≫ homMap id (U.map q)`. Composition `≫` is in diagrammatic order, the reverse of the source's juxtaposition order. This is equality in the category of cochain complexes. |
| All maps commute with input chain maps | `nu` is a natural isomorphism; `theta_natural`, `alpha_natural`, `sigma_natural` explicitly give the three other equations. `a : P' ⟶ P` is contravariant. Sigma's condition is `E.map b ≫ q' = q ≫ w`, so its naturality includes compatible changes of q. |
| Compatible changes of coefficient rings | The theorem quantifies every `a : R ⟶ R'`, `b : S ⟶ S'`, `φ' : R' ⟶ S'` with `φ ≫ b = a ≫ φ'`. It produces a `CoefficientSquare` and `CoefficientCompatibility`. |
| Canonical maps for those coefficient changes | `extensionIso_pure` pins the iterated extension iso by `t tensor (s tensor x) ↦ t*b(s) tensor (1 tensor x)`. `restrictionMate_pure` pins the mate by `r' tensor z ↦ φ'(r') tensor z`. `Data.homComparison` is sigma with q the identity, so the Hom comparisons are normalized, not arbitrary maps or asserted isomorphisms. |
| Coefficient compatibility of nu | `CoefficientSquare.tensorComparison` transports the canonical mate through nu. `tensor_pure` states its expected scalar formula, and `CoefficientCompatibility.nu` is the resulting actual coefficient square. |
| Coefficient compatibility of theta | `CoefficientCompatibility.theta` compares extension of theta followed by the canonical Hom comparison/mate with the mate, S-Hom comparison, precomposition by `extensionIso.inv`, and theta over R'. |
| Coefficient compatibility of alpha | `CoefficientCompatibility.alpha` compares extension of alpha with alpha after the canonical tensor and Hom coefficient maps. |
| Coefficient compatibility of sigma and q | `CoefficientCompatibility.sigma` gives the chain equation for arbitrary S'-complex `N'`, `w : Eb(N) ⟶ N'`, and compatible `q'`. It includes the canonical extended target `N'=Eb(N)` and every compatible semilinear target map through the tensor adjunction. |
| Identity changes and coefficient towers | All coefficient squares are quantified, with their generator normalizations; direct squares, identity squares, and successive squares are all included. The equations can be applied successively without choosing a new comparison. Normalization uniquely fixes the iterated extension isomorphisms and mates. |
| No flatness, boundedness, K-injectivity | None of these predicates occurs among the binders or in any data-package hypothesis. The explicit sheaf-composition, weak abelian-sheafification and locally-bijective assumptions are the canonical API infrastructure for a site in the indicated universe, not mathematical restrictions on rings or complexes. |

The coefficient sigma equation uses the canonical square identification in its
contravariant first input. Both sides start at `Eb Ephi Hom_R(P,A)` and end at
`Hom_S'(Ephi' Ea P,N')`. In particular no invalid tensor/product exchange, no
invertibility of a Hom coefficient comparison, and no arbitrary comparison map
are hidden by the structure packaging.

Dependency declarations read and used:

- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`,
  `Sheaf.CategoryTheory.RingedSiteModules`; transparently Mathlib `SheafOfModules`.
- `def-pur-sheaf-tensor-product`: `SheafOfModules.cochainModulesMonoidal` and
  `cochainModulesPreadditive`,
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`; underlying
  `monoidalCategory`, `tensorObjIsoSheafification`, and the independent-universe
  `changeOfRingsOfUniverses` / `changeOfRingsHomOfUniverses` retained by its imports.
  The ordinary extension's object and map equalities explicitly fix these.
- `def-pc-sheaf-restrict-scalars`: `SheafOfModules.restrictScalars`,
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`; retains sections and
  restricts their action, with its additive instance.
- `def-pur-hom-complex`: `CategoryTheory.homComplex`, `homComplexFunctor`,
  `WeilConjectures.Algebra.Homology.HomComplex`; actual component projections
  `homComplexπ` from `WeilConjectures.Algebra.Homology.HomComplexComponents`.
- `def-coef-hom-representative-evaluation`:
  `WeilConjectures.coefficientHomComponent` / `coefficientHomSectionEvaluation`,
  `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`; exact product projection
  and slice-identity evaluation convention, directly expanded in `evaluate`.
  The resolution-specific portion is intentionally not used for these ordinary
  chain complexes; no replacement is introduced.
- Proof imports: `SheafOfModules.exists_localizedSiteTensorRestriction`,
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`;
  `SheafOfModules.overFunctor`, `overMap`, `overFunctorMap`,
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`;
  `PresheafOfModules.sheafification` / `sheafificationAdjunction`,
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`;
  `LinearMap.liftBaseChangeEquiv`, `Mathlib.RingTheory.TensorProduct.Basic`;
  `SheafOfModules.homObj`,
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`;
  `TensorProduct`, `Mathlib.LinearAlgebra.TensorProduct.Defs`.
- Existing pure-section helper `SheafOfModules.scalarExtensionSection`,
  `Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions`, is used to express
  local extension generators. Its data are the existing sheafification unit.

Edge cases checked mathematically before and against the draft:

- Empty site and zero complexes: all local formulas are vacuous or zero,
  and the categorical equations are still meaningful. No nonemptiness assumed.
- Zero rings, including S=0: no Nontrivial assumption; the isomorphisms and zero
  maps have the claimed types. Restriction retains the original underlying sheaf.
- Nonflat Z to Z/2 on the point site: for P=Z/2, A=Z, the source Hom and sigma
  are zero; no false Hom-base-change isomorphism is asserted. Theta is the
  extension/restriction adjunction, not a base-change isomorphism for arbitrary Hom.
- Complexes unbounded in both directions: the native Hom is the product over
  every integer; formulas use a single coordinate, never a finite-support family
  or an interchange of tensor and infinite product. Negative and zero degrees use
  the native signed differential, already part of the dependency.
- Identity and arbitrary commuting coefficient squares: the mate need not be
  invertible, whereas the iterated extension comparison is an isomorphism.
  Every coefficient q' compatible with an arbitrary target map w is retained.
- Independent object and morphism universes: all helper uses have explicit
  universe parameters `.{c, v, u}`. No equation c=v or c=u is imposed.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`, query: "Extension and restriction of scalars for
  sheaves gives a natural isomorphism of product Hom cochain complexes and a
  normalized tensor evaluation square". Eight hits: ordinary sheaf free-object
  lemmas, sheaf global-section adjunction lemmas and a light-condensed closed
  structure. None states this normalized product-Hom chain assertion.
- `msearch.py ... leansearch`, query: "The internal Hom complex of sheaves after
  extension of scalars is naturally isomorphic by adjunction to the internal Hom
  complex into the restricted target". Eight hits, all ordinary module scalar
  adjunction/coextension declarations. Their exact formulas support the proof,
  but do not give the ring-sheaf product-Hom complex and strict square.
- `msearch.py ... loogle`, query:
  `SheafOfModules.restrictScalars, CategoryTheory.homComplex`: zero hits,
  unknown identifier `CategoryTheory.homComplex` (project-specific declaration).
- `msearch.py ... grep`, regex:
  `homComplex.*changeOfRings|changeOfRings.*homComplex|extendRestrictScalarsAdj`,
  Mathlib subdirectory `Algebra/Category/ModuleCat`: 11 hits, ordinary module
  scalar adjunction and monoidal adjunction uses, not the stated sheaf chain maps.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, regexes
  `scalar.*[Hh]om|[Hh]om.*[Ss]calar|changeOfRingsFunctor|changeOfRings.*[Ff]unctor`:
  inspected `ScalarInternalHomData`, `ScalarHomOrdinaryTensorComparison`,
  scalar-extension binary coherence, ordinary change of rings and native Hom
  components. Derived scalar-Hom infrastructure is not this ordinary strict
  product-Hom theorem; its ordinary normalized tensor infrastructure is reused.
- Item-id search in `lean/WeilConjectures`: no declaration; searches for
  `StrictScalarHom|scalarHomChainIdentification` in both source roots and Mathlib:
  no existing declaration. No exact existing binding was found.

No statement correction, dependency repair, new independent node, or
STATEMENT-DISPUTED issue was needed. The item node changes only in `lean`.

Validation: every compile used the prescribed `scompile.py`; the final source
compiled as both a sandbox module (14.1 s) and the delivered module (13.4 s),
without warnings or errors. All variables/universes are explicitly bound,
all lines have at most 100 characters, and the sole theorem proof is `sorry`.

## Second reading by O4

This is a separate clause-by-clause self-reading by the single dispatcher worker;
no other agent was started, as instructed. The maintainer's independent review
remains the independent reading of this delivery.

I reopened the node and complete module. I checked the source/target of nu
(R-linear tensor versus restricted S-extension), theta (restriction of S-Hom,
not S-extension of R-Hom), and sigma (an S-linear map), and reversed the source's
functional composition to Lean's diagrammatic `≫` in the strict square. The
homogeneous formula uses `i+n=k`, matching the actual product projection and q's
component k. The identity object of each slice is explicitly present.

I checked input naturality contravariantly in P, and the q-square condition in
`sigma_natural`. For coefficient compatibility I checked that the iterated
extension iso points from Eb Ephi to Ephi' Ea; its inverse therefore occurs in
precomposition with Hom. In the coefficient sigma equation, the arbitrary target
N', target map w and compatibility with q' are all retained. The mate and Hom
comparisons are maps, with no claim that they are invertible. The alpha comparison
uses both canonical tensor and Hom comparison maps. I checked the coefficient
nu equation together with `tensor_pure`, which pins the tensor coefficient map
independently on generators.

The first compile exposed universe inference ambiguity in the max-universe
aliases and a line-break syntax error in termwise restriction. I supplied all
helper universe applications explicitly and fixed the application syntax.
The next compile accepted the entire mathematical signature; I then shortened
eight long lines and renamed sigma's formally unused q binder `_q` without
changing its type or any formula. The final compile was clean. I found no omitted
hypothesis or source clause in this reading. The type packages introduce no
extra input assumption: their simultaneous existence is the theorem's conclusion.
