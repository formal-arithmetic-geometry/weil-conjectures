## Worker report

The delivery states `WeilConjectures.CoefProjectionEvaluation.systemPairingDinaturality`
in `Sheaf.SixFunctors.CoefPairingSystemDinaturality`. Its only theorem has proof
`sorry`. Five helper definitions are actual composites of the dependency's canonical
functors and maps: `systemHomSections`, `integralHomSections`,
`Model.integralSupport`, `Model.leftEvaluation`, and
`ScalarSpecialization.reductionFunctor`. They expose actions on arrows needed to
write the identities; they introduce no independent mathematical notion or chosen
map. No new nodes, dependency repair, statement correction or disputed statement.
Only the item's `lean` field changes.

The source read is `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-lem-sp-tower/prop-coef-integral-dualizing.proof.md`, paragraph 2. This specifies
the natural derived mapping-complex comparisons before limits. The node is the
seven-step extracted naturality argument, rather than a verbatim blueprint theorem.
I also read `literature/stacks-project/sites-cohomology.tex`, labels
`lemma-internal-hom` (08J9), `lemma-adjoint` (07A6), and
`equation-projection-formula-map` (0B56). These give the functorial closed adjunction,
derived adjunction and counit-defined projection map used by the node.

### Every hypothesis and object

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)`
  with `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. These explicit
  section parameters are inherited by the theorem and helpers.
- `k : Type u` and `[Field k]` give the base field; `_hl : IsUnit (l : k)` is
  precisely invertibility of the coefficient prime in k.
- `X Y : Scheme.{u}`, their `Over (Spec (.of k))` instances and the two pairs of
  `LocallyOfFiniteType` and `QuasiCompact` instances say that they are finite-type
  k-schemes. `a : X ⟶ Y`, its `IsOver` instance, `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` give the separated finite-type k-map.
- `c : Compactification a` supplies Z, the open immersion c.i, proper c.g and
  c.comm. There is no new compactification or compactification-independence claim.
- `m : Model l E c` names the normalized canonical tensor/adjunction presentation
  already supplied by `projectionEvaluation`. It includes signed total-tensor
  models, sections, proper and restriction adjunctions, and the actual open tensor
  comparison. It contains no naturality hypothesis for beta. Universally naming
  these witnesses makes the assertion apply to the specified word, without
  choosing data from a bare existence theorem. Their existence is the dependency's
  conclusion for exactly the displayed geometric inputs.
- `coefficientSequenceDerived.{u,u} l E X` is the ordinary unbounded derived
  category over the actual vertical sequence ring sheaf Q_X. Its module sheaves
  and quotient transitions are those of `coefficientSequenceCommRingSheaf`, not
  arbitrary towers. Completed coefficients and constant systems are unchanged.
  The index n in the imported implementation means exponent n+1, so all positive
  coefficient levels, including exponent one, occur.
- `systemHomSections l E X` is the composite of the recorded derived internal Hom
  and `coefHomQuotientDerivedSections`: it is h(U,N) and its two-variable maps.
  `integralHomSections` composes it with the exact
  `coefHomPointDerivedRestriction`, so it is rho_0* h and its maps.
- `m.integralSupport` is `m.support` then quotient point sections then exact
  scalar restriction. Thus its object and map are exactly B_U and B(u), with
  `m.support = CoefSupportOpenTensor.operation l E c = Rp_* j_!`.
- `m.beta` is the imported specified word: scalar balance, signed point symmetry,
  sections projection mate, proper projection mate, actual open comparison, and
  closed evaluation after source-sections counit. It is not an arbitrary pairing.
- All constructions use a common explicitly quantified ambient universe u,
  matching the recorded `Model`. The pro-etale site retains objects in u+1 and
  morphisms in u; module values are in u+1 and the standard localization in u+2.
  The common ambient bound for schemes, field and coefficients is the node's size
  convention, not an equality of site object and morphism universes. Larger input
  sets can be included in one larger ambient universe. `autoImplicit` and
  `relaxedAutoImplicit` are both false.

### Every conclusion clause

1. The first conjunct quantifies arbitrary U,U',N and `u : U ⟶ U'`. Its left
   side is `rTensor.map (rho h(u,N), id B_U) ≫ m.beta U N`; its right side is
   `rTensor.map (id rho h(U',N), B(u)) ≫ m.beta U' N`. Lean composition is
   written in traversal order. The common source is exactly
   `rho h(U',N) tensor_R B_U`, not the tensor with B_U'.
2. The second conjunct quantifies arbitrary U,N,N' and `v : N ⟶ N'`. It says
   `m.beta U N ≫ B(v) = rTensor.map (rho h(U,v), id B_U) ≫ m.beta U N'`.
   Both first two conjuncts are equalities in
   `DerivedCategory (coefHomPointModules.{u,u} l E)`, which is the ordinary derived
   category of strict R-module towers. The ULift of the fixed integer ring only
   implements the existing size convention.
3. The third conjunct is exactly the closed dinaturality normalization on
   `U tensor RHom(U',N)`. `Model.leftEvaluation` is the prescribed graded braiding
   followed by the recorded right-tensor closed counit. The two tensor maps are
   `(id U, RHom(u,N))` and `(u, id RHom(U',N))`.
4. The fourth conjunct is the corresponding equality for `Model.v`, whose common
   source is `U tensor La* Lg_Y* h(U',N)`. It uses the actual varying-ring pullback,
   m.gy.left and the whole-system Hom-sections map. `Model.v` already composes
   pullback composition, the g_X counit and signed evaluation. The proper/open,
   g_Y and rho_0 natural projection maps transporting this equality are the
   actual maps in `Model.beta`; the first two conjuncts assert the transported
   identities. No projection map is assumed invertible.
5. The fifth conjunct quantifies every normalized `ScalarSpecialization l E m`,
   K,K' in the ambient completed-coefficient derived category, arbitrary quotient
   system N and `f : K ⟶ K'`. The Hom arrow is exactly
   `(coefHomTower l E X).map (f.op,id N)`, the H_N(f) of the recorded Hom model.
   `ScalarSpecialization.reductionFunctor` is const followed by the recorded
   derived scalar extension, so its map is M(f). The support arrow is exactly
   `m.integralSupport.map (M(f))`. `ScalarSpecialization.transported` already is
   tensor of the normalized full-system Hom comparison with identity, followed
   by m.beta at M(K). The displayed equality is therefore
   beta_K(H_N(f) tensor id) = beta_K'(id tensor B(f)), with the comparison's
   direction and normalization unchanged. The specialization's reductionModel
   retains finite evaluations and actual quotient transitions.

The seven proof steps in the docstring follow all seven steps of the DAG:
closed adjunction; source counit; proper/open naturality; quotient point-sections
naturality; scalar balance and symmetry naturality; whole-system pasting;
full-system Hom transport. There is no trace, inverse limit, finite evaluation
criterion, boundedness, Tor-amplitude or constructibility hypothesis.

### Dependency declarations read and used

All non-convention statement dependencies are publicly imported through their
recorded modules; the two additional proof modules are imported without `public`.

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its reexported
  `coefficientExtensionIntegers`, `coefficientExtensionRing` and quotient maps.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`.
- `def-weil-size-convention`: metatheoretic convention record, implemented by the
  explicit universes described above; there is no module to import.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses` and the completion
  and quotient coefficient sheaves it reexports.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently the Mathlib category `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` and the standard localization.
- `Sheaf.Paper.CoefficientRingedSequenceSite`:
  `coefficientSequenceCommRingSheaf`, `coefficientSequenceDerived`,
  `coefficientSequenceInternalHom`, restriction and evaluation functors.
- `Sheaf.Algebra.Homology.DerivedInternalHomMixedUniverses`:
  `CategoryTheory.derivedInternalHomMixedUniverses` and the publicly preserved
  `derivedInternalHomOfUniverses` interface used by the fixed sequence model.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `CoefficientClosedStructure`, its tensor/evaluation, and `CoefficientTensorModels`.
- `def-weil-scheme-morphism-properties`: convention record; Mathlib's
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `IsOver` are used directly.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement` and its imported `Compactification`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`; its separately derived
  compactification formula is already realized on systems by Model.support.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `WeilConjectures.scalarReductionDerivedExtension` and `scalarReductionSource`;
  the recorded ScalarSpecialization.reductionModel identifies finite evaluations
  of M with these extensions, including transitions.
- `Sheaf.SixFunctors.CoefSystemProjectionEvaluation`:
  `CoefProjectionEvaluation.Model`, `projectionEvaluation`, Model.support/hom/h/b,
  Model.v/Pi/q/balance/beta, `ScalarSpecialization` and its
  reduced/supportTower/transported constructions.
- `Sheaf.SixFunctors.CoefHomTowerScalarModel`:
  `WeilConjectures.coefHomTowerScalarModel`, `coefHomTower`,
  `coefHomQuotientDerivedSections`, `coefHomPointDerivedRestriction`,
  `coefHomDerivedConstant` and `coefHomScalarMap`. The normalization of the
  Hom comparison is inherited through ScalarSpecialization, not re-assumed as
  a naturality law for the pairing.
- Proof imports `Sheaf.Paper.ProjectionMateExact`:
  `SheafOfModules.ringedProjectionMateExact`, and
  `Sheaf.Paper.CoefSupportOpenTensorModel`:
  `WeilConjectures.CoefSupportOpenTensor.supportOpenTensorModel`.

### Searches and edge cases

The following actual msearch.py searches were run for this group and item:

- LeanFinder, `Dinaturality of the system projection-evaluation word`: eight
  unrelated inverse-system/profinite results, no full-word match.
- Loogle, `CategoryTheory.ihom.ev_naturality, CategoryTheory.MonoidalClosed`:
  zero hits. A subsequent exact query `CategoryTheory.ihom.ev_naturality` found
  the generic closed-category target naturality lemma; it does not state the
  whole-system compact-support/scalar identities.
- grep, `dinatur|pairing.*naturality` in Mathlib/CategoryTheory: zero hits.
- LeanFinder, `Dinaturality in the source and naturality in the target of the
  derived compact support projection evaluation pairing on whole coefficient
  systems`: eight results including LightCondensed.ihomPoints_symm_comp and
  ihom_map_val_app, none the specified word.
- grep, `ev_naturality|dinatur` in CategoryTheory: fourteen hits, including
  DinatTrans.lean and Monoidal/Closed/Basic.lean:109. These are generic identities.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for the node id, dinaturality/pairing names and proposed full declaration names.
  The relevant existing `coefTowerEvaluationPairing` concerns a specialized
  finite-field dualizing target and its older frame; it does not cover arbitrary
  U,N, target naturality or this specified scalar-balanced word. The existing
  derived closed-evaluation lemmas cover only the normalization, not the item.
  No proposed fully qualified declaration exists.

Edge cases checked directly against the formulas: identity u or v reduces to
identity functor maps; zero maps and U=0 or N=0 remain permitted; no nonzero input
or nonempty scheme is assumed. Empty X and Y remain in the geometric hypotheses.
A point scheme with identity compactification retains the ordinary closed
pairing. Arbitrary torsion K and unbounded complexes are permitted; no coefficient
flatness or finite-Tor condition was inserted. All quotient levels are retained.
The first source orientation and the contravariant f.op direction were checked.

### Validation

Only scompile.py was used. A legacy non-module diagnostic initially exposed
private proof-import duplicate K-flat declarations; the required module header
and public dependency visibility resolved that, without editing any dependency.
The remaining scalar universe constraints came from broad imported
SemilinearSections instances. The same local instance removals as the recorded
CoefSystemProjectionEvaluation module resolve them without imposing any size
equality. Explicit universes are also supplied for scalar projections and the
existing functors. Diagnostic Check.lean has been removed.

The final module compiled as both the isolated sandbox module and its delivered
library module in 6.0 s and 5.0 s, with no errors or warnings. The file contains
one `sorry`, precisely the named theorem, and no data is postponed.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
