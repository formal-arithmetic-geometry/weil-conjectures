## Worker report

Stated `AlgebraicGeometry.ProEtale.torsionOpenTest_devissage` in
`Sheaf.Paper.TorsionOpenTestDevissage`. Its proof is `sorry`. Four real-data helpers
specify the derived-section functors, their actual restriction natural transformation,
the principal-open test object, and its inclusion. They are particular objects and
arrows of this statement, recorded together in `lean.declarations`; they introduce no
independent mathematical notion. No statement correction or dependency repair is made.
Only the item's `lean` field changes.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Affine X | `(X : Scheme.{u}) [IsAffine X]` |
| Global section f; W = X[1/f], j its inclusion | `(f : Γ(X, ⊤))`, `(X.basicOpen f).ι` |
| Small pro-etale sites | `Scheme.ProEt.topology X`, objects `X.ProEt` |
| Constant abelian sheaf of M | `(constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj M` inside `torsionOpenTestSections` |
| Ordinary uncompleted D and placement in degree zero | `DerivedCategory`, `DerivedCategory.singleFunctor _ 0` |
| RΓ computed by K-injective resolutions | The actual evaluation functor's `rightDerivedFunctor`, using the published Grothendieck-abelian sheaf/K-injective instances |
| Every cyclic coefficient exponent s >= 1 | `hcyclic : ∀ (s : ℕ), 1 ≤ s → ...` |
| A_s is Z/ell^s as module over itself | `ModuleCat.of (ULift.{u + 1} (ZMod (ℓ ^ s))) (ULift.{u + 1} (ZMod (ℓ ^ s)))`, then its constant sheaf |
| Actual module-derived adjunction unit is invertible | `IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat ...) (X.basicOpen f).ι).unit.app (...))` |
| Affine pro-etale test v:V→X | `(V : X.ProEt) [IsAffine V.left]`, with morphism `V.hom` |
| Weak contractibility | `(hV : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} V)` |
| T = V×_X W = V[1/v*f] | `torsionOpenTestObject f V`, whose underlying scheme is exactly `(V.left.basicOpen (V.hom.appTop.hom f)).toScheme` |
| Every n >= 1 | `(n : ℕ) (hn : 1 ≤ n)` |
| Every abelian M killed by ell^n | `(M : AddCommGrpCat.{u + 1}) (hM : ∀ m : M, (ℓ ^ n) • m = 0)` |
| Infinite groups included | There is no `Finite`, `Fintype`, finite-generation, or cardinality hypothesis on M |
| Actual restriction is invertible in D(Ab) | First conjunct, `IsIso ((torsionOpenTestRestriction (torsionOpenTestInclusion f V)).app M)` |
| Source concentrated in degree zero | Second conjunct, `∀ q : ℤ, q ≠ 0 → IsZero (H^q(source))` |
| Positive target cohomology vanishes | Third conjunct, `∀ q : ℤ, 0 < q → IsZero (H^q(target))` |
| Naturality in homomorphisms of M | Fourth conjunct, the explicit restriction square for every `a : M ⟶ N` |
| V and T affine, hence qcqs | V affine is a hypothesis; T is its principal open, hence affine. No separate qcqs assumption is imposed. |
| Empty schemes and identity open | No nonemptiness, proper-open, or nonzero-section hypothesis |

The use of a common site is the standard definition of derived sections at an object.
Its localization at V is the small pro-etale site of V, and restriction preserves
injectives and constant sheaves. Thus derived evaluation of the constant sheaf on X
at V computes `RΓ(V, underline M_V[0])`; evaluation at T computes
`RΓ(T, underline M_T[0])`. The localization comparison is the published
`proEtale_restriction_injectives` interface, with the underlying abelian comparison
given by `leftModuleDerivedEvaluationForget`. In particular, these are the requested
coefficient sheaves on V and T, with their canonical restrictions.

`torsionOpenTestRestriction` is constructed with
`Functor.rightDerivedFunctorNatTrans` from
`(sheafSections ...).map i.op`, and then whiskered by the constant-sheaf and
degree-zero functors. It is a specified morphism in the derived category, not a
per-degree surrogate or an arbitrary isomorphism. The naturality conjunct refers to
this same arrow. The functorial resolution/localization model supplies all its data.

The cyclic hypothesis uses the published fixed-scalar sheaf category with coefficient
ring `ULift (ZMod (ℓ ^ s))`. This is the ordinary constant-ring module realization,
the same actual unit already used in `TorsionAcyclicNormCoefficientTest.lean`.
`ULift` only implements the small-site size convention; it changes neither the ring
nor the module. There is no completion or finite restriction on M. Schemes have
object universe u, the pro-etale site has object universe u+1 and arrow universe u,
and abelian coefficients have universe u+1. No equality of the two site universes
is assumed. Since u is arbitrary, this convention accommodates coefficients of
arbitrary size after choosing the ambient universes.

Statement dependencies read and used:

- `def-pur-ringed-site-zeroth-hypercohomology`:
  `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`,
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`. Its construction is
  H^0 composed with the unbounded K-injective right derived sections functor.
  This theorem needs all degrees and the derived object, so it uses that same generic
  `Functor.rightDerivedFunctor`, followed by `DerivedCategory.homologyFunctor`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`; single objects and homology use its API.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `Spec.map`. Here X is an arbitrary affine scheme via
  `IsAffine`, retaining every affine scheme rather than fixing a presentation.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`, the sheafification of the constant presheaf.
- `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
  `Scheme.proEtaleConstantRingDerivedPullback` and the publicly reexported ordinary
  module operations. For the cyclic unit the fixed-scalar presentation is
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`,
  `ProEtale.derivedUpperStarLowerStarAdjunction`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`.
- `sk-def-pe-weak-contractible`:
  `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`,
  `CategoryTheory.GrothendieckTopology.IsWeaklyContractible`; its full definition
  quantifies over locally surjective set-sheaf morphisms and demands surjectivity
  on sections, equivalent to the node's epimorphism condition.

All stated proof-dependency modules are imported. Mathlib proof dependencies use
the recorded sheafification, homology-sequence, single-triangle, and short-five-lemma
modules. The six-step docstring retains the complete argument: the cyclic actual unit,
forgetting scalar action, exact extension closure, induction for finite primary groups,
finite-subgroup filtered unions, and assembly into an isomorphism in D(Ab).

Edge cases checked: M=0; finite cyclic and noncyclic groups; infinite direct sums of
Z/ell^n; n=1; disconnected V; empty X or V; nilpotent f and the empty open; f=1 and
the identity open. Empty-open hypotheses rule out a nonempty test with nonzero cyclic
sections; none of these cases is silently removed. Negative cohomology is included
in the source-concentration clause, while the target vanishing clause has q>0 exactly.

Searches performed with msearch.py:

- LeanFinder: "Derived open adjunction units for constant cyclic prime power coefficients
  imply derived sections restriction isomorphisms for arbitrary bounded primary torsion
  groups on affine weakly contractible pro etale tests". Eight hits, all affine
  scheme/basic-open or affine-limit section lemmas; no matching theorem.
- Loogle: `"IsWeaklyContractible", "IsIso"`. Zero hits.
- Mathlib grep: `(torsion|ZMod).*(cohomology|Sheaf)|(cohomology|Sheaf).*(torsion|ZMod)`.
  Zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for torsion/open/test and
  cyclic-primary restriction expressions found no matching declaration. The broader
  search found `TorsionAcyclicNormCoefficientTest`, which assumes cyclic units but
  concludes norm-coefficient lisse units, not this torsion devissage theorem.
- The exact item-id search in `lean/WeilConjectures` found no match.

The complete source paragraph (3) was read. It provides the parent open-direct-image
route and does not itself assert this sublemma; the node's agent-formulated attribution
is retained. No statement dispute was found. The previous refusal concerned the
already-reviewed stage-1 split; this delivery supplies its previously absent stage-2
Lean statement and does not reopen or change the split.

Validation: scompile.py compiled the module in sandbox mode (7.0 s) and its actual
library-module mode (6.2 s), without errors or warnings. All variables and universes
are explicitly bound. The main theorem is the sole postponed theorem.

## Second reading by Q76

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
