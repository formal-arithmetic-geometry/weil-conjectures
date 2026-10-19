## Worker report

This delivery states `AlgebraicGeometry.ProEtale.directImageEtaleMate` in
`Sheaf.Paper.DirectImageEtaleMate`. Its only postponed proof is that theorem.
The other declarations are concrete constructions or specializations of published
functors, isomorphisms, and maps. No mathematical statement is changed.

Hypotheses and objects, matched clause by clause:

- Prime ell: `ell : ℕ` and `_hell : ell.Prime`.
- Positive characteristic p different from ell: `p : ℕ`, `_hp : 0 < p`,
  `_hne : p ≠ ell`, `k : Type u`, `[Field k]`, and `[CharP k p]`.
- Separated finite type k-schemes: `[X.Over (Spec (.of k))]` and the corresponding
  Y instance; `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` of each
  structure morphism. These are exactly the geometric conventions of
  `sk-def-sfb-dc-setting`. This item uses only that geometric context, not that
  definition's condensed coefficients, constructibility notation, or compactification.
  Its geometric notions are the existing Mathlib ones and require no new definition.
- Proper k-morphism p: `f : X ⟶ Y`, `[f.IsOver (Spec (.of k))]`, `[IsProper f]`.
  Properness supplies the qcqs instances needed by the recorded beta.
- Finite commutative rings: `[CommRing A]`, `[CommRing B]`, `[Finite A]`, `[Finite B]`.
  Their ell-power annihilation is `_hA` and `_hB`, expressed by vanishing of a power
  of the natural-number scalar in each ring. `a : A →+* B` is the specified ring map.
- B as an A-module: `directImageEtaleMateCoefficient a Y` is the constant sheaf on
  `ModuleCat.restrictScalars a` applied to the regular B-module, placed in degree zero
  by `DerivedCategory.singleFunctor`. This retains the actual coefficient action.
- Ordinary uncompleted derived categories: `DerivedCategory (Sheaf ... (ModuleCat A))`.
  This is the recorded fixed-ring encoding; for finite rings the canonical
  `finiteCoefficientEtaleRealization` and `finiteCoefficientRealization` of
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` identify it with modules over
  the recorded constant ring sheaves. No completion or condensed coefficient is used.
- K in D+: `K` and `hK : DerivedCategory.TStructure.t.plus K`.
- H = K tensor B_X in D+: `hH` is precisely boundedness below of K tensor the
  exact derived inverse image of `directImageEtaleMateCoefficient a Y`.
  The canonical constant-section identification gives B_X. There is no boundedness
  assumption on the tensor of Rp_*K with B_Y.
- N = nu_X^*K: throughout the conclusion this is literally
  `(comparisonUpperStar (ModuleCat A) X).mapDerivedCategory.obj K`, the exact
  comparison applied termwise, rather than an arbitrary representative.
- beta_K and beta_H: `directImageEtaleMateBeta f K hK` and the same construction
  at H with hH. This definition transports the *recorded*
  `fixedComparisonDirectImageMatePlus` through `rightDerivedFunctorPlusCompatibility`
  and `mapDerivedCategoryPlusCompatibility`. Its invertibility comes from
  `isIso_fixedComparisonDirectImageMatePlus`. Thus it retains the normalized
  named morphism; it does not select an arbitrary isomorphism of its endpoints.
- Canonical tensor identifications: `directImageEtaleMateComparisonTensor` uses
  `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`, the exact-comparison
  realization of the K-flat-normalized tensor-pullback constraint. The geometry
  constraint is `directImageEtaleMatePullbackTensor`, obtained from the existing
  `ProEtale.leftDerivedUpperStarTensorIso` (the specialized canonical
  `Functor.leftDerivedTensorComparison`). `directImageEtaleMateSquare` is induced
  from `comparisonUpperStarCompUpperStarIso` and exact-functor composition.
- pi_K: `directImageEtaleMateProjection` is exactly the existing
  `Etale.rightDerivedLowerStarProjectionMap` evaluated at K and the constant coefficient.
- t: `directImageEtaleMateTransport` composes tensor(beta_K inverse,identity),
  the inverse source tensor identification, nu_Y^*(pi_K), beta_H, and the direct
  image of the target tensor and pullback-square identification, in that order.
  The target is written using p^*nu_Y^*B_Y, canonically the constant B_X.
- First conclusion: the inverse pullback tensor comparison followed by
  `Adjunction.homEquiv.symm` of t equals the tensor bifunctor applied to the
  pro-etale counit and the identity coefficient. This is exactly the requested
  precomposed adjoint-transpose normalization.
- Last conclusion: `IsIso pi_K → IsIso t`. Invertibility of pi_K is not assumed
  in the transpose clause or asserted unconditionally.

The tensor, pullback, pushforward, and exact-comparison specializations cache the
already existing functors and coefficient instances; they do not construct
another operation. The adjunction is the existing derived adjunction. They remove repeated expensive coefficient
instance elaboration. Every universe and variable is explicitly bound, including
section variables. Coefficients use the project's u+1 convention.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `Etale.rightDerivedLowerStarProjectionMap` and its counit-transpose signature.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonPullbackPlus`, `fixedComparisonDirectImageMatePlus`,
  `isIso_fixedComparisonDirectImageMatePlus`, and the specified counit normalization.
- The compatible `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived`
  modules: ordinary `derivedTensor`, `derivedUpperStarLowerStarAdjunction`, and
  `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  its unique K-flat representative characterization fixes the same constraints
  appearing here in fixed-ring coordinates.
- Ordinary operations are the finite fixed-ring presentation of
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, without changing
  either the action of the constant ring or the derived adjunction normalization.
- The geometric setting is rendered directly by the named Mathlib predicates above;
  no unrelated condensed-ring setting is imposed on the finite-ring categories.

Edge cases checked: X or Y empty, K=0, B the zero ring, and the identity ring map
are included. The hypothesis on H is retained: for A=Z/ell^2 and B=K=F_ell,
negative Tor groups can continue indefinitely, so boundedness of K alone does not
supply it. No assumption that B is flat, has finite projective dimension, is nonzero,
or has invertible ell is introduced. The zero ring remains allowed when the
annihilating exponent is zero; using positive exponents gives the same condition.

Searches (2026-10-18):

- msearch LeanSearch, "Adjoint transpose of etale proetale comparison projection
  formula is tensor counit": 8 hits, including `Adjunction.counit` and the sheaf
  pushforward counit; none states this site-comparison normalization.
- msearch LeanFinder, "comparison of etale and pro-etale derived direct image
  projection formula counit transpose": 8 hits, including
  `Condensed.profiniteSolidCounit` and ordinary scheme/sheaf counits; no exact match.
- msearch Loogle, `CategoryTheory.Adjunction.homEquiv`: 12 generic adjunction hits,
  including `homEquiv_counit`; no exact comparison statement.
- msearch grep, `rightDerivedLowerStarProjectionMap|fixedComparisonDirectImageMatePlus`
  in Mathlib CategoryTheory: no exact specialized statement.
- rg in Mathlib CategoryTheory and the upstream adjunction directory found generic
  projection-map transport in `ProjectionMapMate.lean`; its signature was read.
- rg in upstream WeilConjectures and side Sheaf found no declaration named
  `directImageEtaleMate` or `directImageEtaleMateTransport`, and no upstream tag
  for this DAG item. The upstream `LowerStarProjectionComparison` transports
  invertibility of the pro-etale projection, but does not state the full normalized
  transpose for the explicitly conjugated t, so it is not an existing exact match.
- Current finite-coefficient module sources were read with `scompile.py --source`.
  The older local tree's mixed legacy Iso imports caused duplicate declarations;
  this file uses the compatible finite-coefficient family and the recorded mate.

No STATEMENT-DISPUTED issue, statement correction, new node, or dependency-node
repair is needed. The only theorem proof is `sorry`, with all four DAG proof
steps in its docstring.

## Second reading by Q11

Author's separate self-check; the maintainer supplies the independent delivery review.
I reopened the node and the final signature and checked each binder and both
conclusions against the clauses listed above. In particular the tensor has B as
an A-module, the beta at H uses hH, inverse beta occurs before comparison of pi,
and the final target includes both the tensor comparison and the inverse
inverse-image square. The transpose is precomposed by c inverse, not c, and the
isomorphism assertion is conditional. The exact comparison uses mapDerivedCategory;
there is no arbitrary iso or stronger hypothesis replacing a canonical constraint.
The initial implementation used left-derived comparison coordinates; the final
one uses exact termwise comparison coordinates directly, with the same recorded
D+ mate and its canonical ambient transport. All operation aliases were checked to be direct applications of the published
functors, with real data and no new theorem. The specialized finite-coefficient
`leftDerivedUpperStarTensorIso` removes a generic-instance elaboration timeout
without changing the canonical tensor comparison.

Verification: the final module passed scompile.py in both sandbox and library
coordinates (7.9 s and 8.8 s), with no unexpected warnings or errors.
