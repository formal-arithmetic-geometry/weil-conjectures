## Worker report

Module: `Sheaf.Paper.CommonStageWeilIterate`. The statement is represented by
`WeilConjectures.commonStageWeilFiniteRealization` and
`WeilConjectures.commonStageWeilIterate`, with five explicit canonical-comparison helpers.
Both theorems have only `sorry` proofs. All helper data is constructed explicitly.
There is no new node, dependency repair, or statement correction.

Source read: current `literature/blueprint/latest` (main-20261024),
`blueprint/sec-purity-real-sheaves/sk-lem-wrp-l2-growth/lem-wf-l2-upper.proof.md`,
opening punctual eigenvalue bound. The item's source path records its historical location;
its eight-step extracted proof supplies the finite-stage categorical argument.

Hypotheses and clauses:

- The distinct primes, positive exponent, q=p^a, finite field and fixed algebraic closure
  are `D : FiniteFieldDatum`, `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p`.
  The arbitrary coefficient closure is `Ω : Type v` with field, Padic algebra and
  IsAlgClosure instances. The scheme and coefficient closure universes are independent.
- `Y₀ : Over (Spec (.of D.k₀))`, LocallyOfFiniteType, QuasiCompact, and IsSeparated
  are precisely a separated finite-type k₀-scheme. `D.geometricFiber Y₀` is Y, and
  `D.geometricFrobenius Y₀` is the recorded geometric Frobenius.
- The finite coefficients use `Index l Ω` and their already published `Coefficient.{u}`
  small models. `Stage`, `transition`, `unitor`, `associator`, `inclusion`, and
  `stageSystem` are from GeneralAlgebraicallyClosedCoefficients. No category is copied.
- A finite collection of objects and specified arrows is the finite quiver V and
  `F : V ⥤q sfCommonStageWeilComplex ...`; finite vertices and finite arrow sets permit
  arbitrary finite directed graphs, including loops and repeated objects. A finite R
  and pairs `p r`, `q r` of paths encode exactly finitely many equations between
  composites. `heq` says these equations hold in the original Weil category.
- Finite realization returns E containing all fields of `S : Finset (Index l Ω)`;
  h bounds every original object's stage. F₀ consists of actual E-Weil pairs and
  Weil arrows. Its carriers are literally `(F.obj i).carrier.toStage (h i)`.
  The inverse of σ has the specified canonical `stageSystem.isoToStage` underlying
  map (HEq only identifies endpoints along the asserted carrier equality). Thus σ
  gives the original structure map and its inverse, rather than an arbitrary model.
  The arrow equation gives every prescribed arrow's class. Weil pairs contain actual
  structure isomorphisms with both inverse equations, and their arrows contain actual
  Weil squares. The last conjunct states every path equation over E itself.
- `IsoAlgebra.strIterate` supplies the existing isomorphisms on functor powers. Its
  one-step equality and additive cocycle (`strIterate_one`, `strIterate_add_hom` with
  m=1) give exactly theta^[1]=theta and theta^[r+1]=theta^[r] T^r(theta), after the
  published functor-power equality. We do not introduce a second iterate definition.
- `wfPowerPullbackComparison` recursively uses `localPullbackComposition` and the
  existing `localPositivePower`. The first iterate conjunct identifies the functor
  iterate through this comparison with `localWeilIterate`; thus the scheme-power
  pullback and its specified integral-rationalized comparisons are retained.
- `wfScalarComparison` is the published `rationalPullbackScalarComparison` specialized
  to Frobenius and the conjugated field inclusion. `wfScalarWeil` uses the existing
  `IsoAlgebra.mapOfNatIso` on its inverse: theta_M is d_1 inverse followed by scalar
  theta, exactly as in the node. `wfIteratedScalarComparison` assembles d_r recursively
  from that comparison and the pullback functor. The second conjunct states
  d_r followed by theta_M^[r] equals the scalar extension of theta_E^[r].
- The third conjunct is the identity-field equation with `unitor`. The fourth is
  the tower equation with `associator`, including equal intermediate fields. These
  express the node's specified scalar identifications, not strict equalities of
  differently associated tensor objects.
- `wfStageIteratedComparison` uses the existing
  `sfWeilStagePullbackIdentification` at every step. The fifth conjunct says the
  actual common-stage iterate of `sfWeilStageObject` is the included finite iterate
  through these canonical boundaries. This expresses descent from every model.
  Inverse witnesses are absent from the iterate data, and equality of representatives
  is equality in the existing quotient category. Hence neither inverse witnesses nor
  equation witnesses can affect the common-stage iterate. Two isomorphic models agree
  by the final naturality clause, applied to their comparison isomorphism.
- The last conjunct says theta_K^[r] followed by u equals T^r(u) followed by
  theta_L^[r], with r=n+1. `uKL : K ⟶ L` is an arbitrary Weil morphism; it is never
  assumed invertible. This includes zero and other noninvertible arrows.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: FiniteFieldDatum, CoefficientDatum, geometricFiber.
- `Sheaf.Paper.SfWeilSheafComplex`: sfWeilFrobeniusPullback, sfWeilComplex,
  sfCommonStageWeilFrobeniusPullback, sfCommonStageWeilComplex,
  sfWeilStagePullbackIdentification, sfWeilStageObject. These are actual IsoAlgebra
  pairs, not the unrelated upstream derived category of Weil sheaves.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: Stage, transition, stageSystem,
  inclusion, unitor, associator, representatives. Its existing literal pair category
  and actual Hom quotient supply eventual equality without Hom-map injectivity.
- `Sheaf.Paper.LocalFrobeniusTrace`: localPositivePower, localPullbackComposition,
  localWeilIterate. Their signatures and recursive construction were read.
- `Sheaf.Paper.DerivedPullbackTensorHom` (publicly reached from LocalFrobeniusTrace):
  rationalPullbackScalarComparison, commonStageDerivedPullback. The former is uniquely
  normalized by the rationalized canonical integral component.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`: integralPullbackComparisonRealization,
  IntegralComparisonSystem, IntegralComparisonRealizationCoherence, including
  rationalScalarComposition, scalarIdentity, scalarSchemeUnit, scalarTower and
  the specified comparison naturality. Imported for the proof and normalization.
- Upstream `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`:
  IsoAlgebra.strIterate, mapOfNatIso; Mathlib `CategoryTheory.PathCategory.Basic`:
  Paths.lift and Quiver.Path.

Edge cases checked before stating: empty V, empty arrow sets, empty R, empty prescribed
field list (a finite coefficient field still exists); isolated/repeated vertices and
loop arrows; length-zero paths (identities); zero Weil objects and noninvertible or zero
arrows; r=1 via n=0; arbitrary positive exponents; identity scalar inclusions and towers
with repeated fields; empty schemes; distinct coefficient/site universes. No hypothesis
of injective scalar transition maps occurs. The r=0 helper comparisons are actual identity
data used in recursion, while every theorem clause concerns the requested r≥1.

Searches performed before writing:

- msearch leanfinder, "Finite common coefficient stage realization of Weil complexes and
  morphisms and scalar compatible natural iterated Weil structures": 8 results concerning
  Witt vectors, Dold--Kan and affine limits; none is the requested statement.
- msearch loogle, "IsoAlgebra, localWeilIterate, commonStageDerivedPullback": no hit
  (IsoAlgebra is an upstream name, not a Mathlib identifier in that index).
- msearch grep, "WeilIterate|commonStageDerivedPullback|IsoAlgebra", CategoryTheory:
  no Mathlib hits for these project-specific notions.
- msearch leansearch, "Finite stage realization of a finite diagram of Weil complexes
  together with equations": 8 results about finite limits of complexes; no match.
- rg in Mathlib CategoryTheory found Paths.lift and Quiver.Path for the existing finite
  diagram syntax. rg in lean/WeilConjectures found the reusable IsoAlgebra.strIterate
  and mapOfNatIso APIs; its TraceFormula.Frobenius.iterateStr concerns a different
  category. grep for the item id in lean/WeilConjectures found no existing statement.
- rg in lean/Sheaf found localWeilIterate and localQbarWeilIterate (definitions),
  LocalFrobeniusWeilMorphismNaturality (finite-stage naturality), and
  CommonStageFiniteHomLifting (a different restriction/fullness statement). None
  states the item's simultaneous Weil-diagram realization and full scalar/iterate laws.

No STATEMENT-DISPUTED issue was found. Every supplied definition uses real data.

## Second reading by Q70

The delivered section was a single-worker self-check ("not represented as an independent
second worker's review"). This reading, by the maintainer's second reader
(NT-cc review of 274ea67a), replaces it. Lean file and records are unchanged.

Node clauses, the Lean rendering, and the verdict:

1. p, l distinct primes, a >= 1, q = p^a, k0 = F_q, k, Omega: `D : FiniteFieldDatum.{u}`,
   `l`, `[Fact l.Prime]`, `hl : l ≠ D.p`, `Ω : Type v` with `IsAlgClosure (Padic l) Ω`.
   Same objects. OK.
2. Y0 separated of finite type, Y, g_Y: `Y₀ : Over (Spec D.k₀)`, LocallyOfFiniteType,
   QuasiCompact, `[IsSeparated Y₀.hom]` on both theorems; `D.geometricFiber Y₀`,
   `D.geometricFrobenius Y₀`. No extra hypothesis. OK.
3. E-stages, T_E = Lg*: `Stage`/`Coefficient.{u}` and `sfWeilFrobeniusPullback`, which is
   `rationalDerivedPullback` along g (def-weil-weil-sheaf-complex). C_Y and T:
   `Pair` and `sfCommonStageWeilFrobeniusPullback` (`commonStageDerivedPullback`). OK.
4. Weil pairs and morphisms: `sfWeilComplex` and `sfCommonStageWeilComplex` (IsoAlgebra).
   OK.
5. Finite realization (`commonStageWeilFiniteRealization`): finite quiver V with finite
   hom sets and a prefunctor F into common-stage Weil pairs gives every finite family of
   pairs and Weil morphisms, including loops and repeats. Finite R with path pairs p, q
   and `heq` gives finitely many equations between composites. Conclusion: an E above
   every field of S (prescribed fields) and every object stage; a prefunctor F₀ of
   E-Weil pairs (actual inverse at E, actual Weil squares at E). The carriers are
   literally `toStage`, i.e. K_i ⊗ E. `σ i` is a Weil isomorphism whose underlying inverse
   is HEq to the canonical `isoToStage`, so it is pinned. Hence θ_i is represented by
   θ of F₀ i. Each F.map e is σ⁻¹ ≫ incl(F₀ e) ≫ σ. The path equations hold for F₀
   at E. This is exactly the node's clause, and it is neither weaker (no arbitrary model)
   nor stronger. OK.
6. θ^[1] = θ, θ^[r+1] = θ^[r] T^r(θ): reuses upstream `IsoAlgebra.strIterate`
   (recursion T(θ^[n]) ≫ θ). `strIterate_add_hom` with m = 1 gives the node's form. No
   duplicate iterate. OK.
7. Identification of T_E^r with L(g^r)*: `wfPowerPullbackComparison` is built from
   `localPullbackComposition` (lem-pod comparisons used by def-weil-local-frobenius-trace)
   and eqToIso for `iterate_succ_left`. Conjunct 1 says comparison ≫ `localWeilIterate`
   = strIterate (n+1). I checked by induction: n = 0 is θ = θ. The successor case reduces,
   by naturality of the composition comparison, to strIterate_add_hom. True as stated. OK.
8. d_{r,K} and θ_M = (θ_E ⊗ M) d_1⁻¹: `wfScalarComparison` = the pinned
   `rationalPullbackScalarComparison` (∃! normalized by the rationalized integral
   component, i.e. lem-trf's a_{f,K}). `wfScalarWeil` = `mapOfNatIso` of its inverse, so
   str = d⁻¹ ≫ S θ. `wfIteratedScalarComparison` d_{r+1} = d_1(T^r K) ≫ T_M(d_r). By
   naturality this equals the node's T_M^r(d_1) d_{r,TK}. OK.
9. θ_M^[r] d_r = θ_E^[r] ⊗ M: conjunct 2, d_{n+1} ≫ θ_M^[n+1] = S(θ_E^[n+1]). I
   recomputed the induction with the Lean recursion and naturality of d_1. True. OK.
10. Identity and tower scalar identifications: conjuncts 3 and 4 state the coherence of
    d_r with `unitor` and `associator`, for r ≥ 1. With conjunct 2, they give the node's
    statement for the iterates (step 6 of the node's proof derives the iterate version from
    exactly these). They are not strict equalities of differently associated objects. OK.
11. θ^[r] in C_Y, independent of representatives: the common-stage iterate is
    `strIterate` of the common-stage Weil pair, which is representative-free by
    construction. Conjunct 5 says that for `sfWeilStageObject` it is the included finite
    iterate through `sfWeilStagePullbackIdentification`. I checked this against
    `sfWeilStageObject`'s str = identification ≫ incl(θ). OK.
12. Naturality for every Weil morphism u, noninvertible included: conjunct 6,
    θ_K^[n+1] ≫ u = T^{n+1}(u) ≫ θ_L^[n+1], with u arbitrary. OK.

Edge cases: empty V/R/S (E exists, Index is directed and nonempty); loops and repeated
vertices; length-0 paths; zero objects and zero or noninvertible u; r = 1 (n = 0);
E = M (conjunct 3) and repeated fields in towers; the empty scheme. Universes: u for schemes
and coefficient models, v for Ω, w/t/z for the quiver and relations, all independent.

Searches: rg in lean/Sheaf for `IsoAlgebra.mapOfNatIso`, `WeilScalar`, `strIterate`.
`weilScalarExtension` (PbcWeilCategory) is on the PBC stages, not the sf stages of C_Y.
`localWeilModelScalar` is an object-level copy in a theorem-node module, not a def-node
owner. So there is no H4 duplication. Mathlib has only `Endofunctor.Algebra` one-step
notions.

Advisories, no change: `rationalPullbackScalarComparison`/`rationalDerivedPullback` are
owned by def-weil-derived-pullback-tensor-hom. That is a direct stmt_dep of the cited
def-weil-weil-sheaf-complex and def-weil-local-frobenius-trace, not of the item. The
import of Sheaf.Paper.IntegralPullbackComparisonRealization (the cited lem-trf module) is
not used by the statement. Both theorems are `sorry`. Every helper def has real data.
Docstrings carry source and blueprint tags.
