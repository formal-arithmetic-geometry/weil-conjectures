## Worker report

The packet states `WeilConjectures.RationalScalarTranspose.rationalScalarTransposeCompatibility`
in `Sheaf.Paper.RationalScalarTransposeCompatibility`. It preserves the node's mathematical
statement and all nine statement dependencies. The theorem's proof is `sorry`; the three
helpers give actual constructions, with no postponed data.

Source read: current blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
`lem-coef-rational-retract-evaluation.proof.md`, paragraph about the rationalized integral
comparisons carrying the specified maps and splittings. The DAG expands that paragraph
into its six evaluation/naturality/cancellation steps; the theorem docstring records them.

Hypotheses and objects, clause by clause:

- The global finite-field datum is `D : FiniteFieldDatum`; `C : D.CoefficientDatum`
  supplies the prime `C.l`, its primality, `C.different : C.l ≠ D.p`, and the fixed
  algebraic closure `C.Qbar` of the p-adic coefficient field.
- `X : Scheme` with `X.Over (Spec (.of D.k))` is a k-scheme.
  `LocallyOfFiniteType` and `QuasiCompact` of its structure morphism together mean
  finite type; `IsSeparated` is the diagonal closed-immersion condition.
  No properness or smoothness assumption is introduced.
- `E F : Padic.FiniteCoefficientFields C.l C.Qbar` and `h : E ≤ F` are precisely
  the two finite subextensions inside that closure and their inclusion.
  `IntermediateField.inclusion h` is the actual coefficient embedding.
- `sfRationalConstructibleCategory C.l E.val X` (and its F version) is the raw
  scalar localization, with the same integral objects and full rational Hom groups.
  Neither a Karoubi envelope nor a lattice-preserving subcategory is used.
- `wE,wF : IntegralFiniteExtension.DualizingDatum ...` are the dependency's
  coherent integral dualizing presentations. Their omega objects are localized by
  `sfRationalConstructibleLocalization` in the pairing targets.
- `A,B : RationalVerdier.Datum ...` are the recorded rationalized RHom dualities,
  including their object formulas, pure-tensor morphism formulas and normalized
  evaluation. These are presentations of the specified operations, not arbitrary
  contravariant functors.
- `extend` names `RationalVerdier.scalar` for the actual inclusion. This is the
  prescribed completed integral extension followed by raw rationalization.
- `e : RationalVerdier.Extension ...` gives `e.omega` = u and `e.comparison` = beta.
  `_he : RationalVerdier.ExtensionProperties ... e` retains the canonical integral
  u and beta normalizations and evaluation square. Thus the comparisons have the
  specified origins, rather than being arbitrary natural isomorphisms. The
  dependency's `coef_rational_verdier` provides these presentations and properties;
  its `Conclusion` quantifies over every coherent dualizing presentation.
- `K,L` and `b` have the exact tensor source and localized omega target.
  `a : K ⟶ A.dual.obj (op L)` and `c : L ⟶ A.dual.obj (op K)` are the two adjoints.
  `_ha` uses `adjointPairing ... a = b`; `_hc` uses the same equation for c and the
  pairing precomposed with the signed swap. `adjointPairing` swaps K,L, tensors
  `1_L` with a, and applies A's argument-first evaluation. By naturality of the
  signed braiding this is exactly evaluation with the Hom factor first as in the
  node. The completed/rational tensor-Hom bijection identifies these equations
  with being the stated transposes.
- `scalarPairing` is the composite `c_{K,L} ≫ T.map b ≫ e.omega.hom` in Lean order.
  Its first factor is `rationalTensorScalarComparison.inv.app (K,L)`: the recorded
  comparison has the opposite orientation from the node's c, so its inverse is
  essential. No arbitrary tensor comparison is supplied.
- `aF,cF` and `_haF,_hcF` describe the transposes over F by the same evaluation
  equations. Quantifying over those transposes states their asserted identification;
  their existence and uniqueness are already the tensor-Hom dependency.

Conclusions, clause by clause (Lean composition `f ≫ g` means g after f):

- The first two conjuncts identify `aF = T.map a ≫ beta_L` and
  `cF = T.map c ≫ beta_K`.
- The universal P,Q,i,p,j,q clause has `i ≫ p = 𝟙 P` and `j ≫ q = 𝟙 Q` as
  exactly the two splitting hypotheses.
- Its first equality is `T.map (i ≫ a ≫ A.dual.map j.op) ≫ beta_Q =
  T.map i ≫ aF ≫ B.dual.map (T.map j).op`, the first displayed restriction identity.
- Its second equality interchanges K,P,i,p with L,Q,j,q and uses c,cF, giving the
  full swapped restriction assertion.
- Under `∀ [IsIso a]`, the next equality starts with `beta_Q` inverse and then
  `T.map (A.dual.map q.op ≫ inv a ≫ p)`. This is exactly
  T(p a^-1 D_E(q)) beta_Q^-1, with source D_F(TQ) and target TP.
  The other side first applies D_F(Tq), then beta_L inverse, then T(a^-1), then T(p).
- Under `∀ [IsIso c]`, the final equality is the swapped candidate inverse formula
  with p, c inverse, q and beta_P inverse. Invertibility of a and c is conditional
  separately. No restricted transpose is assumed or concluded invertible.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum` and `FiniteFieldDatum.CoefficientDatum`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsSeparated`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, together with
  `QuasiCompact` from its imported quasi-compact module.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalScalarExtension`, its prescribed
  object/pure-tensor normalization, and `sfRationalCoefficientEquiv`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedTensor`, permitted internal-Hom
  pairs and `rationalDerivedInternalHom`, `rationalTensorScalarComparison` and its
  uniquely integral-normalized component specification.
- `Sheaf.SixFunctors.RationalVerdier`: `Datum`, `Extension`, `ExtensionProperties`,
  `tensor`, `scalar`, `units`, `Conclusion`, and `coef_rational_verdier`.
- `Sheaf.SixFunctors.CoefIntegralFiniteExtension`: `DualizingDatum`,
  `dualizingDatum_nonempty`, the canonical `u` and `beta` used by ExtensionProperties.
- `Sheaf.Paper.IntegralOperationsScalarExtension`: `scalarTensorCompleted` and its
  representative-normalized comparisons, underlying the rational tensor comparison.
- `Sheaf.Paper.CompletedTensorHomTranspose`: `CoefficientTransposeLaws` and
  `completedTensorHomTranspose`, whose evaluation and signed-symmetry bijections
  justify the transpose hypotheses. Its normalized closed data and braidings come
  from the recorded `podIntegralClosed`, `podRationalClosed`, and
  `pullbackTensorIntegralBraiding`, `pullbackTensorRationalBraiding` declarations.
- The proof-only tensor-complex dependency is imported through
  `Mathlib.Algebra.Homology.BifunctorShift`, as recorded by its node.

Edge cases checked: equality E=F is permitted (`h` is non-strict); zero objects,
zero pairings and empty X are not excluded; identity splittings reduce to ordinary
naturality; arbitrary non-adjoint retractions are permitted; noninvertible a,c
still retain both restriction conclusions and simply do not trigger the conditional
inverse formulas. The source and target of each inverse composite were checked,
especially that beta_Q inverse must come FIRST in Lean composition order. Rational
arrows with denominators are included in all map and evaluation binders. All universes
and variables are explicitly declared; no extra equality between site universes is used.

Searches retained from the saved packet (`searches.jsonl`, msearch.py):

- leanfinder: "A monoidal coefficient extension functor preserves the transposes of a
  pairing under evaluation compatible duality comparison and carries retract inverse
  formulas" returned eight generic rigid duality hits, including
  `ExactPairing.coevaluation_evaluation`, `tensorRightHomEquiv`, `tensorLeftHomEquiv`,
  `rightDualIso`, `leftDualIso`; none states these specified rational comparison identities.
- loogle: `CategoryTheory.Functor.map_inv, CategoryTheory.NatTrans.naturality` returned
  zero hits. These generic identities would in any case only prove pieces of the node.
- grep in Mathlib CategoryTheory/Monoidal:
  `expComparison_ev|ev_naturality|map_inv` returned eighteen hits in braided, monoidal
  functor, closed functor and rigid functor-category files. The cartesian exponential
  comparison is not this coefficient tensor comparison.
- Resumed direct rg searches of `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for the node id and declaration names found no
  existing statement. Broader transpose/pairing/scalar searches found the integral
  dual-formula scalar transpose node and generic Hom/evaluation constructions;
  none states both this pairing transport and these four retract identities.

Saved-packet repairs: restored the absent report; synchronized lean.statement with the
file, including the correctly ordered inverse composites; used the currently recorded
scalar-comparisons module import. No mathematical statement change and no disputed statement.

## Dependency modules

`lem-coef-completed-tensor-hom-transpose`: the saved packet already contained a section
1(B) elaboration repair. It names the repeated canonical residue-field inverse expression
once as `coefficientTransposeUnits` instead of re-elaborating the same structure-map
transport six times. This is the identical mathematical value, built from
`finiteFieldDatumPrimeUnit`, with no extra Invertible hypothesis and no dependency on
Verdier duality. The dependency's integral linear equivalence, rational additive
bijection, explicit E scalar preservation, evaluation formula, three-variable naturality
and signed-symmetry clauses remain intact. Its node changes only in lean and records
this reason. The helper definition has real data and its source/blueprint docstring.

Resume validation (2026-10-19): the saved-packet dry run found private imports hiding
public statement dependencies and an unscoped maxHeartbeats option. Promoted the
statement imports to public imports and removed that option. scompile.py then
compiled both delivered files separately without errors or warnings (dependency
7.4 seconds; consumer 40.4 seconds). Signatures and node statements are unchanged.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
