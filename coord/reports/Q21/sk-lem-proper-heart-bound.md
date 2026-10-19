## Worker report

The module `Sheaf.Paper.ProperHeartBound` states `AlgebraicGeometry.ProEtale.properHeartBound`
for finite E and `properHeartBound_padicAlgCl` for the condensed algebraic closure. Both proofs
are `sorry`, with the node's seven-step proof plan in their docstrings. The two subsidiary
real-data definitions only expand the canonical functor and the three conclusions; they do
not choose a derived functor, replace a coefficient structure, or posit a comparison map.
The node is unchanged outside `lean`; no dependency repair or new node is required.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The size convention is explicit `universe u`, schemes `Scheme.{u}`, abelian coefficients
  `Ab.{u + 1}` on the small pro-etale site (object universe u+1, morphism universe u),
  `ObjectProperty.ind.{u + 1}`, and sum index `S : Type (u + 1)`. No independent derived
  or filtered-index universe is introduced.
- The standing prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The base is `(k : Type u) [Field k]`,
  with `(p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)`.
- X and Y carry `.Over (Spec (.of k))`. Each structure map is `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact`; the latter two jointly mean finite type.
  `[p.IsOver (Spec (.of k))]` says the given morphism is a k-morphism.
  No Noetherian or qcqs premise is added: those follow as in proof step 1.
- The finite coefficient is `E : PadicAlgCl.FiniteIntermediateField ℓ` and the canonical
  `Profinite.continuousMapRingObj.{u} E`, with its existing ring-object structure.
  The fixed algebraic closure and its finite intermediate subfields are the published
  coefficient framework's encoding of finite extensions, also used by the IndCons
  dependencies. Every abstract finite extension embeds over Q_ℓ into this closure;
  the embedding identifies its topological condensed ring, so this loses no coefficient
  case. The auxiliary integral ring/uniformizer occur in the source proof, not an extra
  premise of the rational direct-image conclusion; their recorded module is imported.
- The second coefficient is exactly `Profinite.padicAlgClRingObj.{u} ℓ`, whose definition
  uses finite-subextension-valued sections. It is not the full continuous-function
  condensed ring of the algebraic closure.
- The module categories are `CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X)
  Ab.{u + 1}) (condensedRingObj Λ X)` and the corresponding category on Y. The coefficient
  object is the recorded `p_X^* Λ`, with the canonical scoped `CategoryTheory.Obj` instance.
- Properness is `[IsProper p]`. The bound is `(d : ℤ)`, without assuming nonnegativity.
  For each `y : Y`, the fibre is the recorded `pullback p` along
  `Spec.map (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))`
  followed by `Y.fromSpecResidueField y`. The bound `hd` says that every natural finite
  lower bound n of its `topologicalKrullDim` satisfies `(n : ℤ) ≤ d`. This is precisely
  dimension ≤ d in {-∞,0,1,...,∞}: bottom has no such lower bound, a finite dimension m
  tests in particular n=m, and infinite dimension would force every integer n≤d.
- M belongs to IndCons exactly when `ObjectProperty.ind.{u + 1}
  (IsConstantModelConstructible Λ X) M`, the dependency's full replete filtered-colimit
  closure. No arbitrary-local-matrix version of constructibility is substituted.
- `properHeartHigherDirectImage Λ p q` is the actual composite
  `DerivedCategory.singleFunctor _ 0 ⋙ (CondensedRing.lowerStar Λ p).rightDerivedFunctor
  ⋙ DerivedCategory.homologyFunctor _ q`. Thus its value is H^q(Rp_*(M[0])), using the
  derived functor of the full module-object pushforward, including scalar restriction.
- In `ProperHeartBoundAssertions`, the first conjunct universally quantifies over such M.
  Its first clause is `∀ q : ℤ, 2 * d + 1 < q → IsZero (...)` and its second is
  `∀ q : ℤ, 0 ≤ q → ObjectProperty.ind ... (...)` on Y. These are the two displayed
  conclusions with the exact strict endpoint and exact nonnegative-degree condition.
- Its second conjunct quantifies over `q : ℤ` with `0 ≤ q`, every small family M of
  ind-constructibles, and every ambient colimit cofan c. It asserts
  `Nonempty (IsColimit ((properHeartHigherDirectImage Λ p q).mapCocone c))`.
  This states that the functor sends the original coprojections to coprojections of a
  coproduct, hence its canonical direct-sum comparison is invertible. The closure
  theorem `det-ind-heart-filtered-colimits` puts the source and target ambient sums in
  IndCons; membership above puts all images there; fullness and repleteness of
  `det-ind-heart-full-faithfulness` make this equivalent to preservation by the restricted
  functor IndCons(X) → IndCons(Y). The colimit cofan is not an arbitrary map and the
  assertion is not conditional on an additional preservation hypothesis.

Dependency declarations read and used:

| Node | Module and declarations |
| --- | --- |
| def-weil-size-convention | Recorded metatheoretic convention: explicit universes, no declaration. |
| sk-def-sfb-dc-setting | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, `CondensedRing.compactificationOverField`; the setting itself is explicit binders. |
| def-weil-l-adic-coefficient-extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`, importing the degree, absolute value, integers, uniformizer, quotient and transition constructions in `CoefficientExtension`. |
| sk-def-sfb-qlbar-condensed | Closed upstream audit: `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`, `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`; no Lean-record repair needed. |
| sk-def-sfb-module-objects | `Sheaf.Paper.ModuleObjects`, `CategoryTheory.moduleObjects`, `AlgebraicGeometry.ProEtale.pulledBackModuleObjects`, reducing to the same Mathlib `CategoryTheory.Mod` used here. |
| sk-def-sfb-pulled-back-coefficients | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `coefficientRing`, `condensedRingObj`. |
| sk-def-sfb-constructible | `Sheaf.Paper.CondensedConstantConstructibility`, `IsConstantModelConstructible` and its local-model/stratification and derived-category declarations. |
| det-ind-heart-full-faithfulness | `Sheaf.Paper.IndHeartFullFaithfulness`, `IndHeartFullFaithfulnessAssertions`, `indHeart_fullFaithfulness`; clause (2) is exactly `ObjectProperty.ind.{u + 1}` of this constructible predicate. |
| sk-def-sfb-module-derived-pushpull | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`, `CondensedRing.derivedUpperStarLowerStarAdjunction`, `rightDerivedLowerStarIso`, generic `Functor.rightDerivedFunctor`. |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `IsProper`, `IsSeparated`, `UniversallyClosed`. |
| def-weil-geometric-fibre | Recorded specialization of `CategoryTheory.Limits.pullback` along the algebraic-closure residue-field point; `Mathlib.AlgebraicGeometry.Fiber`, `Scheme.fromSpecResidueField`. |
| def-kun-topological-krull-dimension | `Mathlib.Topology.KrullDimension`, `topologicalKrullDim : WithBot ℕ∞`. |

Statement imports are public; all recorded available proof modules are imported privately.
The two proof dependencies `det-proper-heart-bound-rational` and
`det-thm-sfb-proper-base-change-rational` have no recorded declaration, Mathlib match or closed
upstream declaration, so there is no proof import yet for them. Their role and route remain
in the docstrings. They are proof inputs, not missing notions needed to state this theorem.
The current published source of `InternalAbelianSheafModuleEquivalence` was read through
`scompile.py --source`, because the older shared source lacked that recorded module.

Edge cases checked before writing:

- Empty X and empty geometric fibres have dimension bottom, so hd permits any integer d,
  including negative d. For d<0, n=0 excludes every nonempty fibre. Nothing casts d to Nat.
- Empty Y forces empty X, and hd is vacuous as it should be.
- d=0 gives exactly the claimed upper bound q>1, without claiming an optimal bound.
- q=2d+1 is excluded from vanishing, q=0 is included in membership and sum preservation,
  and negative q satisfying q>2d+1 when d<0 are still covered by the vanishing clause.
- Zero M is allowed. No nonzero, connected, geometrically connected, smooth, or surjective
  premise appears.
- Empty S is included; colimit cofans then state preservation of zero. Infinite small S
  and u+1-sized filtered presentations are allowed.
- The algebraic-closure coefficient retains its finite-subextension-valued section condition.

Searches for an existing statement (2026-10-18):

- `msearch.py` leanfinder, query “Higher direct images of a proper morphism vanish above twice
  fibre dimension plus one on ind constructible condensed coefficient sheaves and preserve
  arbitrary direct sums”: eight hits on condensed module categories and affine limits;
  no matching theorem.
- `msearch.py` loogle, query `AlgebraicGeometry.IsProper`: twelve properness-definition and
  stability hits, no higher-direct-image theorem.
- `msearch.py` grep, query `IndConstructible|ind.constructible|cohomologicalDimension|higherDirectImage`
  in `AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py` leansearch, query “proper higher direct image on ind constructible sheaves
  preserves direct sums”: eight generic direct-sum and adic-completion hits; no match.
- `rg` of `properHeartBound|proper_heart_bound|sk-lem-proper-heart-bound|IndCons|indConstructible`
  in upstream `WeilConjectures`, side `lean/Sheaf/Paper`, and the published module-object
  framework: no proper-heart-bound statement; only the IndCons dependencies and related
  statements listed above. The older upstream checkout has no ModuleObject directory,
  so the framework search used the exact shared `lean/WeilConjectures` sources.

No statement correction, disputed statement, dependency module, or new node is introduced.

Validation: the revised module compiled cleanly with `scompile.py` in both sandbox and
library modes. A temporary `#check` pass with `pp.universes` confirmed that each helper
and the theorem has exactly the single scheme universe parameter, with no extra inferred
universe. Those diagnostics were removed before delivery. The first compile's unresolved
geometric-fibre coercion was repaired by annotating the pullback as `Scheme.{u}`.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
