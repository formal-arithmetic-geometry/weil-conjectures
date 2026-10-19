## Worker report

Item: `lem-wf-curve-kummer-jacobian-tate-module` (Q77, stage 2).

The module `Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule` states
`AlgebraicGeometry.exists_curve_kummer_jacobian_tate_comparison`. Its only theorem
has proof `by sorry`; it defines no new object and proves no auxiliary lemma.
The item JSON changes only in `lean`. There are no new nodes, dependency repairs,
or statement corrections. No mathematical defect was found in the node.

Sources read: the complete DAG statement and seven proof steps; the recorded
interfaces of all seven statement dependencies; the master blueprint node and
its four proof paragraphs; the current main-20261015 node, separate proof file,
and `sk-d-real-jacobian/_section.md`. The current source has the same finite-level
statement. The stage-1 node has made the finite site interpretation, prime and
positive level, and left Galois action explicit; the Lean follows those clauses.
No unit statement is altered.

Hypotheses and conclusions, clause by clause:

| Node text | Lean rendering |
| --- | --- |
| Ground field k0 and an algebraic closure K | `(k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosure k₀ K] [IsAlgClosed K]`. These are precisely the closure interface of the recorded Galois-action theorem, with an arbitrary universe u. |
| C0 a smooth projective geometrically connected curve | `C₀ : Scheme.{u}`, its `Over (Spec k₀)` structure, `SmoothOfRelativeDimension 1`, `IsProper`, and `GeometricallyConnected` for its structural map. For a smooth proper curve over a field, proper and projective are equivalent. This is the recorded geometric-Jacobian theorem's curve convention, not a finite-field restriction. |
| C the geometric base change | `p : C ⟶ C₀` and `hC : IsPullback p (C ↘ Spec K) (C₀ ↘ Spec k₀) (Spec.map (algebraMap k₀ K))`. An arbitrary pullback model is admitted, not only Mathlib's chosen fibre product. |
| Geometric smooth proper integral curve | `C.Over (Spec K)`, `IsCurve`, `Smooth`, `SmoothOfRelativeDimension 1`, `IsProper`, `GeometricallyIntegral`. These are the properties of the displayed base change and the exact interface of the recorded dependency. They exclude no smooth projective geometrically connected curve. |
| The fixed Jacobian and its representing identification | `J : Over (Spec K)`, `[CommGrpObj J]`, `[IsJacobian (C ↘ Spec K) J]`, `φ : (picardFunctorDegree ... 0).obj.RepresentableBy J`, and `hφ : IsPicardZeroMul ... φ`. IsJacobian provides an abelian variety of the required genus; φ and hφ expose the pair in def-sc-jacobian and are exactly the inputs of the recorded action theorem. |
| Prime ell distinct from the characteristic | `(ℓ : ℕ) [Fact ℓ.Prime] (c : ℕ) [CharP k₀ c] (hℓ : ℓ ≠ c)`. Characteristic zero is allowed; k0 is not assumed finite or perfect. |
| Every positive n | The Lean index `n : ℕ` denotes the node's positive exponent `n+1`. The lowest level is ell^1, and every integer n>=1 occurs. |
| The canonical point/Pic0 comparison | `∃ Φ : Additive (picardZero K C) ≃+ Additive (𝟙_ (Over (Spec K)) ⟶ J)`, followed by the sheafification-unit formula using `φ.homEquiv`. This is the exact normalization from the recorded geometric-Jacobian theorem, including the canonical pullback of C over the terminal K-scheme. It forbids an unrelated additive equivalence. |
| H1 with the Kummer twist identifies with Jacobian prime-power torsion | `α : ∀ n, Sheaf.H (C.rootsOfUnitySheaf (ℓ^(n+1))) 1 ≃+ AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec K)) ⟶ J)) ((ℓ : ℤ)^(n+1))`. The target is the standard group of K-points killed by the indicated integer, exactly the torsion-system convention of the recorded Tate-module definition. |
| Kummer gives these isomorphisms canonically | For every n and x, the underlying Picard class of `Φ.symm (α n x).1` equals `Pic.toCohomologicalPicardGroup C |>.symm` applied to `Sheaf.H.map (kernel.ι ((ℓ^(n+1)) • 𝟙 C.gmSheaf)) 1 x`. The map is H1 of the inclusion mu -> Gm, not a connecting homomorphism. Phi's normalization fixes the representing comparison; this equation fixes alpha. |
| Naturality | The next universal clause admits a second smooth proper geometrically integral K-curve D, its Jacobian J', its Pic0/point comparison Φ', and any family α' with the identical Kummer normalization. For every curve map `g : D ⟶ C` and point homomorphism `j` compatible with Picard pullback through Φ and Φ', it supplies the canonical roots-of-unity comparison `q` and the equation `(α' n (H(q) (cohomologyMap g ... x))).1 = j (α n x).1`. The compatibility assumptions are inside this naturality conclusion and describe exactly “a pullback of curves compatible with these data” in proof Step 7; they add no premise to the main theorem. |
| Transition z -> z^ell | For every n, the statement supplies a sheaf map `pₙ : mu_(ell^(n+2)) ⟶ mu_(ell^(n+1))` with `pₙ ≫ kernel.ι ... = ℓ • kernel.ι ...`. The inclusion is monic, so this uniquely specifies the power map on roots, with no arbitrary transition. |
| Transition on Jacobian torsion is multiplication by ell | The accompanying equation is `(α n (Sheaf.H.map pₙ 1 x)).1 = (ℓ : ℤ) • (α (n+1) x).1`. It is written in the ambient point group, so it expresses precisely the restricted torsion transition without a second torsion-map construction. |
| Galois action on cohomology is pullback along id_C0 times Spec(sigma) | For every `σ : K ≃ₐ[k₀] K` and every `g : C ⟶ C` satisfying `g ≫ p = p` and `g ≫ structureMap = structureMap ≫ Spec.map σ`, the theorem supplies `q : g^* mu ≅ mu`. These two equations characterize the canonical base-change map, which exists by hC. The condition `q.hom ≫ kernel.ι ... = (g^*).map (kernel.ι ...) ≫ upperStarGmSheafToGmSheaf g` characterizes the canonical roots-of-unity comparison on local units. |
| Galois action on Jacobian points is the specified canonical semilinear action | The equivariance equation says the underlying point of `α n (H(q)(cohomologyMap g ... x))` is `Spec.map σ ≫ (α n x).1.toMul.left ≫ (a σ).hom`, where a is `Classical.choose (existsUnique_geometricJacobian_galoisAction k₀ K C₀ C p hC J φ hφ).exists`. This is a unique action fixed by the recorded theorem. It is not an arbitrary action supplied as a new hypothesis. The base of a is Spec(sigma inverse); the point is precomposed by Spec(sigma), as required. |
| A_n=Z/ell^n and its finite pro-etale twist | We use the node's explicit canonical model `ν_C^* μ_(ell^(n+1))`, spelled `(ProEtale.comparisonUpperStar AddCommGrpCat.{u+1} C).obj (C.rootsOfUnitySheaf (ℓ^(n+1)))`. The node itself identifies this with A_(n+1)(1) by lem-amb-finite-tate-site-descent, specialized to Q_l and its uniformizer l. Using this stated canonical model avoids a second definition of the twist or an arbitrary coefficient sheaf. No choice of roots of unity or basis is used. |
| H1 may be computed on either site | `αPro : ∀ n, Sheaf.H (ν_C^* mu) 1 ≃+ torsionBy ...` and `αPro n (ProEtale.comparisonCohomologyMap C mu 1 x) = α n x`. The map is the recorded canonical cohomology pullback, not an unspecified equivalence. The dependency proves it bijective. |
| Compatibility for the pro-etale form | The last equality uniquely identifies αPro with alpha through the canonical bijective comparison. Its naturality and compatibility with powers, together with the recorded finite Tate descent, transport all transition/pullback/Galois equations. Thus these are the same compatible finite system in either site; no inverse-limit cohomology theorem is asserted. |

`Sheaf.H` is the existing Ext model of right-derived global sections used by the
recorded cohomology comparison and pullback interfaces. Its identification with
`Etale.cohomology` is the accepted convention of def-weil-pbc-etale-cohomology;
we do not define another cohomology functor. Both sites use AddCommGrpCat in
universe u+1, retaining the small-site object universe u+1 and arrow universe u.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AbelianVariety.GeometricJacobianGaloisAction`:
  `AlgebraicGeometry.existsUnique_geometricJacobian_galoisAction`, with its full
  representing normalization, point-action, torsion and Tate clauses. The chosen
  action in the conclusion is literally the action of this declaration.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian`:
  `AlgebraicGeometry.IsJacobian`, its abelian-variety and genus structure, and
  `IsPicardZeroMul` for the fixed representation.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule`:
  `AlgebraicGeometry.IsAbelianVariety.tateModule`, plus its documented
  K-point/geometric-point comparison. The node asserts a finite compatible
  system, whose torsion and multiplication-by-ell convention is used verbatim.
- `Sheaf.Paper.IntrinsicCoefficientTwists`, publicly importing
  `Sheaf.Paper.CoefficientTwistsDetailed`:
  `WeilConjectures.finiteCoefficientTwist` and its positive-level convention.
  The intrinsic/Qbar repair is not reimplemented or specialized to finite fields.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison` and its module specialization. The abelian
  form used here is `ProEtale.comparisonUpperStar`, already the recorded
  cohomology-comparison dependency's inverse image.
- `Sheaf.Paper.FiniteTateSiteDescent`:
  `Scheme.finite_tate_site_descent`, `finiteTateCoefficient`, `finiteTateProSheaf`,
  and its root-projection normalizations. Its Q_l specialization is the
  canonical identification of the coefficient in the statement with ν-star mu.
- `Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison`:
  `ProEtale.comparisonCohomologyMap` and `comparisonCohomologyMap_bijective`.
- Proof imports include every recorded proof-dependency module: Kummer sequence
  and exactness; the cohomology long-exact ladder; Gm/Picard comparison and
  pullback; global functions; degree-zero and functorial cohomology pullback;
  etale finite twist pullback; torsors; and derived global sections. The existing
  curve/Pic0/Jacobian/Tate definitions are public transitive imports. Imports
  only needed for the proof remain ordinary `import`.

Edge cases checked mathematically before finalizing:

- Genus zero (P1): Pic0 and the Jacobian point torsion are trivial, and Kummer H1
  is zero. All equations become the unique zero-group equations, with no
  positivity of genus or rank assumption.
- Genus one: Phi is the fixed Picard representation and alpha has ell^(2n)
  torsion points; no identity point of C itself is chosen.
- Smallest positive level: Lean n=0 means ell^1, and the first transition is
  ell^2 -> ell. The forbidden ell=0,1 cases are excluded by primality, not by
  extra inequalities. There is no claim about n=0 in the node's indexing.
- Characteristic zero and positive characteristic p different from ell are
  allowed. No finite-field, Frobenius, separability of k0, primitive-root, or
  polarization hypothesis is added.
- Identity sigma and products: the canonical action from the dependency has
  a_1=id and a_(sigma*tau)=a_sigma composed with a_tau over Spec of the inverse.
  Precomposition by Spec sigma gives the left action on points required by the
  node; it is not the incorrect action by postcomposition alone.
- Identity curve pullback and arbitrary compatible pullbacks are both included
  in the universal naturality clause. No injectivity or isomorphism condition
  is imposed on that arbitrary map.
- An empty scheme is not a geometrically connected integral curve. The
  coefficient/site constructions themselves impose no extra nonemptiness.
- All variables and universes are explicit. Definitions contain no sorry:
  there are no new definitions, and the only proof is the named theorem's sorry.

Searches (through the prescribed msearch wrapper and direct rg):

- LeanFinder: “Kummer identifies first etale cohomology of roots of unity on a
  smooth proper geometric curve with Jacobian torsion naturally and Galois
  equivariantly.” Eight hits, including Hilbert 90, cyclotomic character and
  Selmer group declarations; none states this sheaf/Jacobian comparison.
- LeanSearch: “The Kummer isomorphisms from first cohomology of a curve to the
  torsion subgroup of its Jacobian commute with power transition maps and
  Galois pullback.” Eight hits on field Kummer theory and group cohomology
  functoriality, none matching this statement.
- Loogle: `"Kummer"` returned eight field-theory/Kummer-Dedekind declarations.
  The initial expected-name query for roots-of-unity power/transition maps
  returned no matches (unknown identifier `power`).
- msearch grep `rootsOfUnity.*map|power.*roots` in AlgebraicGeometry returned
  no matches. Direct rg in Mathlib AlgebraicGeometry for
  `sheafH|Kummer|Jacobian|[Tt]ate[Mm]odule` found elliptic-curve Jacobian
  coordinate declarations, not the Jacobian of an arbitrary curve or this
  compatible cohomology isomorphism.
- Direct rg in upstream WeilConjectures and side lean/Sheaf for
  `kummer.*jacobian|jacobian.*kummer|lem-wf-curve-kummer-jacobian-tate-module`
  found only the upstream `FundamentalGroup/Frobenius.lean` proof commentary
  and the side H1DualTateModule consumer. The former's full
  `EtaleTorsor.exists_picTorsionPairing` signature was inspected: it is a
  finite-field torsor/character pairing, not this theorem. The latter assumes
  this item in its proof and cannot be used as an existing match.
- Broader upstream/side searches for H1, roots-of-unity, torsionBy, Kummer and
  Tate found `nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one_of_isProper` in
  Curve/Kummer: it compares only with the cohomological Picard torsion and
  has no representing normalization, Jacobian, Galois or transition clauses.
  Its full docstring and signature were read; it does not duplicate this item.
- `dag/lean_names_upstream.json` has no declaration matching the proposed name.
  The proposed full declaration name was also checked in both source trees.

Validation: the module is checked using only the prescribed scompile.py
single-file wrapper, including a check under its actual module path. The
ordinary sorry warning is expected. Final compiler and delivery-preflight
results are recorded below after the last run.

## Second reading by Q77

This is the worker's separate clause audit, not a claim that another agent
reviewed the work. The dispatch brief forbids starting agents and assigns the
independent review to the maintainer. With the JSON, source and final Lean open,
the audit checked the following points for that reviewer:

- The representation is fixed, including its group law, so the action and
  torsion equivalences cannot be replaced by arbitrary group isomorphisms.
- Positive indexing was checked on n=0,1: alpha 0 is level ell and alpha 1 is
  level ell^2; the displayed p and ell-smul equation connect those two levels.
- Both roots-of-unity comparisons are normalized by the inclusion into Gm.
  This pins the actual power and pullback maps rather than assuming arbitrary
  maps with compatible cohomology.
- Equivariance is checked on every x, not only on zero, and uses the same
  unique semilinear action as the dependency; Spec sigma is on the source of
  the point and the inverse is in the base of the semilinear morphism.
- The canonical Kummer inclusion is H1(i), never a connecting map to Pic.
- Naturality was expanded from the normalization formula to an explicit
  arbitrary compatible curve-pullback square before final delivery.
- The pro-etale equivalence uses the specified ν-star mu model, with a
  commuting equation for the canonical cohomology pullback. It carries all
  finite-level equations via this bijective map.
- No extra helper, statement amendment, coefficient-field finiteness condition
  on k0, or restriction to Frobenius automorphisms has been introduced.

Final validation:

- `scompile.py Q77 lem-wf-curve-kummer-jacobian-tate-module <module>` passed
  both sandbox and real-module checks, with no errors or warnings. The final
  run used 39.3 s for the sandbox and 13.7 s for the actual module check.
- `deliver2.py Q77 lem-wf-curve-kummer-jacobian-tate-module --no-push` printed
  `OK (dry run): commit be4517a358 passes the preflight and compiles; nothing pushed`.
- The node delta was checked independently as exactly the `lean` field. The
  final Lean module has one named theorem with one sorry, 179 lines and a
  maximum line width of 96 characters. No global build was run.
