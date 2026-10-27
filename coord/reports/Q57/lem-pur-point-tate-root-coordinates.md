## Worker report

The module `Sheaf.Paper.PointTateRootCoordinates` states
`WeilConjectures.point_tate_root_coordinates`, with its proof `sorry`.
No mathematical statement or dependency is changed. Its three auxiliary definitions
are real terms: `purPointConstant` is the actual sheafification unit on constant
labels; `IsPurPointSignedCoordinates` and `HasPurPointRootCoordinates` expand the
normalization clauses of this one theorem. They do not introduce another Tate line,
coefficient sheaf, inverse limit, tensor product, or dual. No additional theorem is
postponed and no data is chosen from an unproved existence theorem.

The source was read directly: Deligne, La conjecture de Weil I, (2.2), printed
pp. 280--281, and (2.13), printed p. 283. The current blueprint source is
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-purity-conv/def-weil-frobenius-coefficient-twists.md`.
The root coordinates are the geometric-point construction preceding the Frobenius
scalar computation. The node is an auxiliary lemma, not the unit's own statement.

Hypotheses and conclusion, clause by clause:

| Node text | Lean rendering |
| --- | --- |
| Algebraic closure k of a finite field k0 of characteristic p | `D : FiniteFieldDatum.{u}`, with `D.k`, `D.k₀`, `D.p` and its field/algebraic-closure/cardinality data |
| Prime ell different from p | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` |
| s = Spec k | Every site and sheaf is on `Spec (.of D.k)` |
| Finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` |
| Valuation ring, uniformizer and positive quotient levels | Existing `Padic.coefficientExtensionIntegers`, its fixed coefficient uniformizer, and `Padic.coefficientExtensionRing l E (n + 1)` |
| A compatible primitive root sequence exists | The first conjunct is `∃ ζ : ℕ → D.k`, with `IsPrimitiveRoot (ζ n) (l ^ (n + 1))` and `ζ (n + 1) ^ l = ζ n` |
| The conclusion holds for every such sequence | The second conjunct universally quantifies `ζ`, then assumes both its primitivity and compatibility |
| Finite constant sheaf isomorphisms | `f n` is an isomorphism from the finite coefficient unit to `purTwistRootsModule` |
| j maps to ζ_r^j on every site object | The first clause of `HasPurPointRootCoordinates` evaluates `f n` on `purPointConstant ... j`, applies `proEtaleRootsOfUnitySections`, and equates the resulting unit value to the pullback of `ζ n ^ j.val` through `ΓSpecIso.inv` and `U.unop.hom.appTop` |
| Locally constant, possibly nonconstant labels | An actual sheaf morphism `f n`, natural on all objects, is normalized on every constant label on every object. Such labels locally generate the constant sheaf, so this fixes the map on every locally constant label, including disconnected objects |
| Reduction and power transitions commute | The second clause equates the actual `proEtaleRootsOfUnityTransition` after `f (n+1)` with `f n` after `purTwistFiniteTransition`, for arbitrary section `a` on every `U` |
| Completed Z_ell and the root inverse limit are identified | `g` is a module-sheaf isomorphism from the unit of `purTwistZlCompletion` to `purTwistZlModule`; both use the recorded categorical limits |
| The inverse limit is the limit of the stated finite coordinates | The third clause uses `limit.π (proEtaleRootsOfUnityTower ...) (op n)` and `purTwistZlProjection`, for every coefficient section |
| 1 maps to e=(ζ_r)_r | Substitute the ring element 1 in that projection equation and j=1 in the finite normalization. Thus `g.hom.val.app U 1` is exactly the prescribed compatible root tuple, with no independent choice of e |
| Integral B_s is the completion | `c m` has source the unit of `completedIntegralCoefficientSheafUnrestricted` |
| Finite B_s is the constant coefficient sheaf | `d n m` has source the unit of `integralCoefficientSheaf l E ... n` |
| Integral e_B=e tensor 1 | The fourth clause sets the degree-one image of 1 equal to `purTwistIntegralTensor ... U 1 (g.hom.val.app U 1)`; the published scalar-extension tensor stores its scalar factor first |
| Finite e_B=e tensor 1 | The fifth clause uses the actual `scalarExtensionSection` for `purTwistIntegralQuotient` with scalar 1 and the integral degree-one generator |
| e_0,B=1 | The first clause of `IsPurPointSignedCoordinates` makes `c 0` the identity on every section |
| Positive generators are tensor powers | Its second clause identifies the degree-(r+2) generator with `siteSheafTensorTmul` of the degree-(r+1) generator and the degree-one generator; powers use the existing left-associated `coefficientTwistPower` |
| Every integer coordinate b maps to b e_m | `c m` and `d n m` are isomorphisms for all `m : ℤ`, and the third signed clause explicitly states `hom b = b • hom 1` on every object |
| Positive inverse b e_r maps to b | The fourth signed clause states this for every `r+1`, every object and every scalar |
| Negative inverse is evaluation on e_r | The fifth signed clause evaluates the actual internal-Hom section `φ` at the identity object of `Over U.unop`, on the prescribed positive generator |
| e_-r(e_r)=1 | The sixth signed clause applies the negative image of 1 to the positive generator and equates the value to the ring element 1 |
| Γ(s,B_s)=B, canonically | The last two clauses give ring equivalences `ι`, normalized by `integralScalarConstant` in the completed case and by the actual constant-presheaf sheafification unit in the finite case |
| Γ(s,B(m)_s)=B e_m,B | Those same clauses require bijectivity of `b ↦ (c m).hom (ι b)` or `b ↦ (d n m).hom (ι b)` at the terminal object. The scalar-multiple formula already imposed on every object identifies these with exactly `b e_m,B` |

The use of `n : ℕ` consistently indexes the paper's exponent `n+1`, so no positive
level is omitted. The integer cases `Int.ofNat` and `Int.negSucc` cover all signs.
`1` is annotated with its coefficient ring type: a unit module does not separately
register an `OfNat` instance, though its underlying carrier is that ring.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its field/closure instances.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`: `Scheme.proEtaleRootsOfUnitySheaf`, `proEtaleRootsOfUnitySections`, `proEtaleRootsOfUnityTransition`, `proEtaleRootsOfUnityTower`; the recorded normalized roots module is retained through `purTwistRootsModule`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.limit` and `limit.π`, used by the recorded roots and coefficient completions.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: its public imported `coefficientTwistLine`, `coefficientTwistPower` and `integralTwistLine`, defined in `Sheaf.Paper.CoefficientTwistsDetailed`; the predicates use these literal signed tensor/Hom objects, not a new definition of a twist.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: its public imported `completedIntegralCoefficientSheafUnrestricted`, `completedIntegralCommRingSheafUnrestricted`, `integralCoefficientSheaf`, and `integralCoefficientCommRingSheaf`.
- The same twist dependency publicly supplies `Scheme.purTwistZlCompletion`, `purTwistZlProjection`, `purTwistFiniteRing`, `purTwistFiniteTransition`, `purTwistZlModule`, `purTwistIntegralModule`, `purTwistIntegralOne`, `purTwistIntegralTensor`, `purTwistIntegralQuotient`, and `purTwistFiniteOne` from the recorded coefficient and root-tower modules.
- The signed dual uses `SheafOfModules.homObj` from `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`, with sections literally maps on the localized site.
- The tensor clauses use `SheafOfModules.siteSheafTensorTmul` from the public imports of `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`; `scalarExtensionSection` is the existing pure tensor/sheafification map from `Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions`.

All stated proof dependencies are imported directly, including
`IsSepClosed.exists_isPrimitiveRoot`, `AlgebraicGeometry.proEtale_finite_constant_sections`,
`Scheme.pur_twist_sheaf_locally_free`, and `WeilConjectures.connected_adic_integral_basis`.
The theorem docstring carries every step of the node's natural-language proof.

Edge cases checked before and after writing:

- The smallest root level and coefficient quotient level are 1; the transition formula
  starts at exponents 1 and 2, including ell=2 away from characteristic 2.
- Degree 0 is the actual unit, degree 1 is the recorded first line, degree 2 uses its
  pure tensor with itself, and degree -1 uses internal Hom of the first line.
- Every pro-etale object is quantified over, including empty, disconnected and
  non-quasi-compact objects. Empty-object sections are the unique zero-ring/module
  sections and the normalization equations still make sense. No connectedness
  assumption is made on these test objects.
- The base point itself is nonempty and connected, so its normalized coefficient
  global-sections isomorphisms do not assert the false empty-base version.
- The source of `g` is the completed coefficient unit, never the discrete constant
  Z_ell sheaf. Similarly `c m` uses completed integral coefficients.
- The coefficient field and the finite-field closure fit in an arbitrary universe `u`;
  the pro-etale site has object universe `u+1` and morphism universe `u`, unchanged.
  The constant-label helper has an explicit independent coefficient universe `v`,
  necessary because `ZMod` lives in universe 0. No universe is auto-bound.

Searches for an existing statement and for the helper names:

- `msearch.py leanfinder`: “Compatible primitive roots trivialize pro-etale roots of unity sheaves and their inverse limit, signed completed Tate tensor powers and duals”. Eight results, including `BDeRhamPlus` and cyclotomic-character formulas. None states this sheaf-coordinate theorem.
- `msearch.py loogle`: `"rootsOfUnity", "Sheaf"`. Zero results.
- `msearch.py grep`: `TateTwist|tateTwist|rootsOfUnity.*[Ss]heaf|[Ss]heaf.*rootsOfUnity` in Mathlib. Zero results.
- `msearch.py leansearch`: “Compatible primitive roots give coordinates for the inverse limit Tate module and its tensor powers and duals as pro-etale sheaves”. Eight results concerning profinite inverse limits, algebraic inverse systems, direct-limit tensor products and `IsPrimitiveRoot.primitiveRootsPowEquivOfCoprime`; no matching pro-etale sheaf statement.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf`: Tate/root coordinate and signed-coordinate patterns find upstream etale Tate twists, local root-cover statements and Frobenius/scalar comparison modules. They provide existing constructions but do not assert this complete point theorem for every prescribed root sequence. Direct search for this item id in `lean/WeilConjectures` has no result.
- Exact searches for `point_tate_root_coordinates`, `purPointConstant`,
  `IsPurPointSignedCoordinates`, and `HasPurPointRootCoordinates` in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no result.

Validation: `scompile.py Q57 lem-pur-point-tate-root-coordinates` compiled both the
sandbox-name and library-name forms cleanly, without errors or warnings. Only the
main named theorem has a `sorry`. No statement dispute or dependency fault remains.

## Second reading by Q57

No second worker was started: the dispatched brief requires direct delivery and assigns
independent review to the maintainer. The worker self-audit above reopens the node and
all four declarations, matching every hypothesis and clause. It caught the need to
annotate ring-valued ones and to separate the coefficient universe of constant labels;
both were repaired before the final clean compile. This is not claimed to be an
independent review.
