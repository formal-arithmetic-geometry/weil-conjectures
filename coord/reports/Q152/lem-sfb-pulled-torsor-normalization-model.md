## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.PulledTorsorNormalizationModel` states
`AlgebraicGeometry.Scheme.pulled_torsor_normalization_model`, with proof `sorry`.
There are no definitions, auxiliary theorems, dependency repairs, new nodes, or statement changes.
Only the item's `lean` field changes. The existing stage-1 split/review is preserved.
The earlier worker's stage-1 live-wins obstruction does not apply to this stage-2 statement.
No released repair note for this item is present in the read clone.

The statement uses arbitrary compatible presentations of the two principal localizations
and fraction fields. These are existing notions, not new assumptions on the domains:
localization's universal property and injectivity of R to B give the indicated maps uniquely.
The scalar towers require that the presentations use those induced maps. All rings and schemes
use a common ambient universe `u`; the finite group has its own independent universe `v`.
An arbitrary pair of ring sizes fits a common universe by the usual universe lift convention.
No equation between the group and scheme universes is imposed. `set_option autoImplicit false`
checks every binder; the two universe parameters are explicit.

The theorem produces an affine presentation S of the input torsor, rather than assuming
one as an additional hypothesis. Its tensor algebras are actual coordinate presentations
of the pullbacks, as witnessed by both projection equations. In the following mapping,
T means `A' ⊗[A] S`, D means `E ⊗[A'] T`, and C means
`∀ a, integralClosure B (F a)`; these are explanatory names only, not Lean definitions.
Commutativity identifies the usual S-tensor-A' and T-tensor-E with these scalar-first
orders. The default E-algebra on every displayed E-tensor is multiplication in the E
factor, exactly the specified right-hand E-structure in the node's usual tensor order.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| R and B commutative Noetherian normal domains | `[CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]`, and the identical four classes on B |
| Injective map R to B | `[Algebra R B]` and `hRB : Function.Injective (algebraMap R B)` |
| Nonzero f in R | `(f : R) (hf : f ≠ 0)` |
| A = R[1/f] | `[Algebra R A] [IsLocalization.Away f A]` |
| A' = B[1/f] and the induced map A to A' | `[IsLocalization.Away (algebraMap R B f) A']`, the R/B/A' and R/A/A' scalar towers |
| K = Frac R and E = Frac B | `[Field K] [IsFractionRing R K]`, `[Field E] [IsFractionRing B E]` |
| Induced inclusion K to E and generic/open maps | K/E, A/K, A'/E, A/E algebra structures, with the R/K/E, R/B/E, R/A/K, B/A'/E, A/A'/E, and A/K/E towers |
| Finite group G | `(G : Type v) [Group G] [Finite G]` |
| Given finite etale surjective G-torsor P over Spec A | `P : GaloisCoverAction G (Spec (CommRingCat.of A))`; its fields are finite, etale, surjective, action over the base, action laws, simply transitive geometric fibres, and quotient universal property |
| Its coordinate ring and specified structural map | Existential S, CommRing and A-algebra, `e : Spec S ≅ P.Z` and `e.hom ≫ P.π = Spec.map (algebraMap A S)` |
| Actual pulled torsor P_B over Spec A' | W and `ι : W.Z ≅ pullback P.π (Spec.map (algebraMap A A'))`, the equation over A', and the equation intertwining every action with P's action through `pullback.fst` |
| Actual coordinate algebra T of P_B | `eT : Spec T ≅ pullback ...`, with equations for both `pullback.snd` (the A'-structure) and `pullback.fst` (the original S-coordinate map) |
| Actual generic torsor P_K and its coordinate ring | `eK : Spec (K ⊗[A] S) ≅ pullback ...`, again with both projection equations |
| Both index sets finite and nonempty | `Fin n`, `Fin m`, `0 < n`, `0 < m` |
| Generic decomposition over K | `dK : K ⊗[A] S ≃ₐ[K] (∀ j, L j)`; by eK this is the algebra of the actual P_K |
| L_j/K finite Galois with degree dividing group order | `FiniteDimensional K (L j) ∧ IsGalois K (L j) ∧ Module.finrank K (L j) ∣ Nat.card G` |
| F_a/E finite Galois | `FiniteDimensional E (F a) ∧ IsGalois E (F a)` |
| D compatible with the base extension of the K-decomposition | `base : D ≃ₐ[E] E ⊗[K] (∀ j, L j)`, with `base (z ⊗ (a' ⊗ s)) = (z * algebraMap A' E a') ⊗ dK (1 ⊗ s)` |
| Tensor distributes over the finite product | `prod : E ⊗[K] (∀ j, L j) ≃ₐ[E] (∀ j, E ⊗[K] L j)`, with its coordinate pure-tensor formula |
| Generic product of fields | `fields : (∀ j, E ⊗[K] L j) ≃ₐ[E] (∀ a, F a)`; composition with base and prod decomposes D |
| Each F_a is a maximal field quotient of one tensor factor with its actual E-structure | For every a there exist j and `q : E ⊗[K] L j →ₐ[E] F a`, surjective with maximal kernel, and `fields x a = q (x j)` for every x |
| T to D injective | `Function.Injective (Algebra.TensorProduct.includeRight : T →ₐ[A'] D)` |
| D is the total ring of fractions | `@IsLocalization T _ (nonZeroDivisors T) D _ Algebra.TensorProduct.rightAlgebra`; the last argument is the real algebra structure of precisely the preceding inclusion |
| T normal | For every prime p of T, `IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)` |
| T integrally closed in D | `@IsIntegrallyClosedIn T D _ _ Algebra.TensorProduct.rightAlgebra`, with the same inclusion as the total-fractions clause |
| C_a integral closure of B in F_a, using the actual E-structure | `integralClosure B (F a)` and the B/E/F_a scalar tower |
| Each C_a and C finite over B | `∀ a, Module.Finite B (integralClosure B (F a))` and `Module.Finite B C` |
| Literal equality C[1/f] = T as subalgebras of D | For every x in the generic product, existence of t with `fields (prod (base (1 ⊗ t))) = x` iff there exist c in C and k with `∀ a, x a * (algebraMap B (F a) (algebraMap R B f))^k = (c a : F a)` |
| The normalization restriction is the actual P_B, respecting structural maps | `model : pullback (Spec.map (algebraMap B C)) (Spec.map (algebraMap B A')) ≅ Spec T`, and the equation over Spec A'. Compose model with eT for the displayed isomorphism to the actual P_B |
| No excellence assumption | No excellence class or additional finiteness property of B occurs |

The subalgebra equality is elementwise, not a mere abstract ring isomorphism. The
composite `fields ∘ prod ∘ base` embeds T in the same product of fields that contains
C by its coordinate inclusions. The right side of the equivalence is exactly the image
of C[1/f]: f is nonzero in B and therefore invertible in every F_a. A single exponent
works for all coordinates because the index set is finite. Equality of the underlying
sets of these subalgebras is equality of subalgebras. The separate injectivity and
localization clauses retain the actual maps before the generic product decomposition.

`GaloisCoverAction` is the recorded dependency notion with independent group universe.
Its quotient field expresses the scheme quotient of a finite etale surjective torsor;
that quotient property follows by faithfully flat descent from the simple-transitivity
condition, so it is not an additional geometric restriction. It avoids restricting
G to the universe used by the older `GaloisCover` proof interfaces. Proof imports of
those older interfaces remain available as proof ingredients; the statement does not
force their universe convention onto the item.

Dependency declarations used (read with signatures and docstrings):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  `IsIntegrallyClosedIn`; prime-local normality is the recorded inline conjunction.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `algebraMap`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.GroupTheory.MonoidLocalization.Away` and
  `Mathlib.RingTheory.Localization.Away.Basic`: `Localization.Away`, `IsLocalization.Away`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`, used by GaloisCoverAction.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, used by GaloisCoverAction.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`, used by GaloisCoverAction.
- `WeilConjectures.AlgebraicGeometry.NormalScheme`: `Scheme.GaloisCoverAction`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; existence for schemes comes from
  `Mathlib.AlgebraicGeometry.Limits`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`.

The modules of recorded proof inputs are imported privately:
`WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverBaseChange`,
`WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange`,
`WeilConjectures.AlgebraicGeometry.Morphisms.FieldTorsorGaloisComponents`,
`WeilConjectures.RingTheory.EtaleNormalRing`,
`WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal`,
`Mathlib.RingTheory.Smooth.Flat`, `Mathlib.RingTheory.Flat.TorsionFree`,
`Mathlib.RingTheory.DedekindDomain.IntegralClosure`,
`Mathlib.RingTheory.Localization.Integral`.
The remaining Mathlib proof leaves are exposed by public statement imports
(`sigmaSpec`, the localization/normality lemmas, and finite-implies-integral).

Edge cases checked mathematically before stating:

- Trivial group: the torsor is the base, with one K-field and one E-field; C = B.
- Split disconnected torsor: T and D have multiple factors. No domain assumption
  is imposed on T or D; total fractions localize at all nonzerodivisors.
- Further splitting over E: m may exceed n; the selected quotient index j may repeat.
- f a unit, including f = 1: the localizations are the original rings, and the same
  equality identifies C with T. No nonunit assumption is present.
- Empty generic index sets are correctly excluded by nonempty geometric fibres over
  the nonzero fraction fields. Empty torsors over these nonempty bases are excluded
  by the input surjectivity. Zero base rings and f = 0 are excluded in the node itself.
- Arbitrary characteristic, including characteristic dividing the group order: no
  invertibility of the group order, tameness, connectedness, or excellence is used.
- Finite separable field extensions give finite integral closures by 032L for any
  Noetherian normal domain. No Nagata/excellence hypothesis is hidden in step 5.

Searches made on 2026-10-22, using the prescribed msearch.py wrapper:

1. LeanFinder: "Finite normalization of the actual base change of a finite etale group
   torsor on a principal open, integral closures of generic Galois components recover
   its coordinate algebra". Eight hits, including `IsGaloisGroup.to_isFractionRing`,
   `Ideal.exists_comap_galRestrict_eq`, `galRestrict`, and
   `IsGaloisGroup.of_isFractionRing`. These are separate Galois/integral-closure
   ingredients, not this actual-cover normalization comparison.
2. Loogle: `"IsIntegralClosure", "Etale"`. Zero hits.
3. Mathlib grep:
   `(normalization|integralClosure|IsIntegralClosure).*(torsor|GaloisCover)|(torsor|GaloisCover).*(normalization|integralClosure|IsIntegralClosure)`.
   Zero hits.
4. LeanSearch: "Finite etale torsor pulled back to a normal domain is the localization
   of the finite integral closure in its generic product of Galois fields". Eight
   hits, including `Ring.instIsGaloisFractionRingNormalClosure`,
   `IsGaloisGroup.of_isFractionRing`, `IsGalois.to_normal`, and `Ring.NormalClosure`.
   None states the actual pulled-torsor comparison and its compatible decompositions.
5. Project rg in both `lean/WeilConjectures` and `lean/Sheaf`:
   `pulled.torsor|pulledTorsor|normalization.*[Tt]orsor|[Tt]orsor.*[Nn]ormalization`.
   The related Cartier/stalk generic models impose DVR/divisor/local hypotheses,
   and field-monodromy normalization treats different input data. They do not state
   this result for arbitrary injective maps of Noetherian normal domains.
6. Required grep of the item id in `lean/WeilConjectures`: no matches.

Sources opened: the complete node and every statement dependency record, all of
those declarations and their docstrings; the recorded upstream torsor/field-component
proof modules; ILO PDF pp.139-140 (printed pp.133-134), and Stacks algebra.tex labels
lemma-integral-closure-localize, lemma-normal-ring-integrally-closed, and
lemma-Noetherian-normal-domain-finite-separable-extension.

Validation: scompile.py compiled the statement in sandbox mode (8.0 seconds) and
library module mode (6.1 seconds), without errors or warnings. The final imports
and delivery are checked again by the required dry run. A preliminary compile
identified an incorrect standalone Surjective module name; it was removed and the
actual recorded UnderlyingMap import is used. No node fault or statement dispute.

## Second reading by Q152

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
