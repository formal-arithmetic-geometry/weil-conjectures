## Worker report

This repairs H3 on returned immutable head `1e89832b0c71`. The saved packet's required
initial dry run returned `OK` at `79ea1f2636`; mechanical success did not resolve the
returned mathematical defects. I retained its module location and main declaration,
then replaced its identity comparison and added the omitted clauses. The node copy is
rebased by copying the current shared node in full before replacing only `lean`, so it
retains the reviewed 12-step proof and the current prerequisite records.

The declaration is `WeilConjectures.PurityFiniteSetting.finiteKummerLevel` in
`Sheaf.Paper.PurityFiniteKummerLevel`. It is a stage-2 statement with one `sorry`.
All helpers have real bodies, are parts of this same comparison, and are listed in
`lean.declarations`. No dependency record or informal statement is changed.

Clause-by-clause correspondence:

* Fixed finite-field datum, coefficient prime, finite subextension, valuation ring,
  chosen uniformizer, and positive coefficient level: the published
  `PurityFiniteSetting P` supplies exactly those data, with no new choices.
* `e` and `e | n`: `P.ramificationIndex` (uniformizer multiplicity of ell) and the
  binder `h : P.ramificationIndex ∣ P.level`.
* `N >= 1` and `N = n/e`: `1 ≤ P.kummerLevel`, where `kummerLevel` is the recorded
  quotient `P.level / P.ramificationIndex`, and
  `P.level = P.ramificationIndex * P.kummerLevel`.
* Normalization `v_ell(ell)=1`, `v_ell(varpi)=1/e`, and `N=n*v_ell(varpi)`:
  the three real equalities use `-Real.log (coefficientExtensionAbsoluteValue ... x)
  / Real.log ell`. This is the normalized additive valuation of the specified
  spectral extension absolute value, not a new valuation supplied as a hypothesis.
* Equality `varpi^n O_E = ell^N O_E`: equality between the existing
  `coefficientExtensionIdeal ... P.level` and `Ideal.span {P.exponent}`.
* The canonical first quotient identification: the ring equivalence `r` from
  `P.Ring` to `O_E / Ideal.span {P.exponent}`, with its equation on EVERY element
  of `O_E`. Thus its underlying map is the identity-induced quotient map.
* Annihilation and the least exponent: `(P.exponent : P.Ring) = 0` and the
  quantified implication for every `j : ℕ`. In particular, `j=0` is included.
* Positive-level indexing: the published finite twist uses index `n` for exponent
  `n+1`. The final part is `∀ n, P.level = n+1 → ...`. This excludes no setting:
  `P.level_pos` supplies `n=P.level-1`. The coefficient quotient at that index is
  therefore literally the prescribed `A_{E,P.level}`, via the displayed equality.
* The positive Kummer exponent is indexed similarly by `∃ N, P.kummerLevel=N+1`.
  The actual roots exponent in every subsequent expression is `ell^(N+1)`.
* The natural `Z/ell^(N+1)` scalar map is `a : ZMod (...) →+* A`; a unital ring
  homomorphism out of `ZMod` is uniquely determined by integer representatives,
  so this existential does not introduce an arbitrary coefficient action.
* Residue degree `f`: `Nat.card (coefficientExtensionResidueField ...) = ell^f`.
  For this finite residue field this specifies exactly its degree over `F_ell`.
* Finite freeness of rank `e*f`, including the second quotient identification:
  the additive equivalence `b : A ≃+ (Fin (e*f) → ZMod (...))` satisfies
  `b (a z * x) = z • b x` for EVERY scalar and element. This is precisely a
  linear equivalence for the natural scalar action; it supplies a finite basis
  without asking Lean to install a new global `CharP` or scalar-action instance.
  The basis is only existential and does not define the canonical sheaf map.
* ANY scheme with ell invertible: `α` is quantified over all `Scheme.{u}` and
  the stalkwise unit condition `hT`; neither a k-structure nor finite type is added.
* `A(1)_T`: `kummerLine` is an abbreviation for `purTwistFiniteOne`, the published
  ordinary tensor reduction of `purTwistIntegralOne`. The latter is the recorded
  scalar extension of the actual inverse-limit root sheaf over the CONSTANT
  discrete `Z_ell` sheaf. No completed-ring/constant-ring identification is made.
  This is the finite first coefficient line in `finiteCoefficientTwist ... n 1`.
* `mu_(ell^N) tensor_(Z/ell^N) A`: `kummerRootsTensor` uses the existing
  `changeOfRingsOfUniverses` applied to `purTwistRootsModule`, which is the
  recorded kernel roots sheaf with its torsion action, transported only across
  `purTwistFiniteRingIso`. This is an EXPLICIT roots tensor and does not use
  `finiteEtaleTateSheaf` or `P.twist`.
* Canonicity: `IsKummerComparison` sends the local iterated tensor
  `z tensor (b tensor x)` to `z*bar(b) tensor p_N(x)`, using the actual
  `limit.π` at level `N`. The theorem asserts the unique isomorphism with this
  formula, for every scheme. It is not an identity normalization.
* Derived tensor compatibility: `kummerTensorMap` is precisely the published
  `siteSheafTensorRightMap α.hom`, natural in the other module. The predicate
  `KummerDerivedCompatible` requires its termwise map on EVERY K-flat complex
  to be a `QuasiIso`. This is the representative form of applying derived tensor
  to the SAME canonical comparison: K-flat representatives compute the recorded
  `ringedSiteDerivedTensorOfUniverses`. It supplies the induced isomorphism in
  the derived category, naturally in the complex; no unrelated isomorphism or
  tensor functor is taken as input.
* Base-change compatibility: `KummerBaseChangeCompatible` quantifies over EVERY
  `f : T' ⟶ T`, including identities. The map `c` is fixed by its equality with
  the recorded `proEtaleRootsOfUnityDirectImageMap` after every root projection.
  The vertical isomorphisms `β, δ` use the recorded constant-ring module inverse
  image `tatePullback`; BOTH are normalized on inverse-image units of all local
  pure tensors. The source uses the coordinatewise root-limit map and the
  integral/finite constant coefficient maps; the target uses the level-N root
  map and the finite coefficient map. The final equality is the actual square
  `f*α_T ≫ δ = β ≫ α_T'`. Applying the natural tensor comparison termwise to
  this equality gives the joint derived/base-change square. No commutation of
  inverse image with an infinite limit is hypothesized, and neither vertical map
  is an arbitrary isomorphism.

Dependency declarations used:

* `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `ramificationIndex`,
  `kummerLevel`, `Ring`, `exponent`.
* The current recorded `Sheaf.Paper.IntrinsicCoefficientTwists` publicly retains
  `CoefficientTwistsDetailed`, its finite line `finiteCoefficientTwist`, and the
  constructions in `Sheaf.Paper.PurTwistSheafLocallyFree`: `purTwistZlOne`,
  `purTwistIntegralOne`, `purTwistIntegralTensor`, `purTwistFiniteOne`,
  `purTwistIntegralQuotient`, `purTwistRootsModule`, `purTwistFiniteRingIso`.
* `Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses`:
  `SheafOfModules.ringedSiteDerivedTensorOfUniverses`, the current K-flat tensor.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
* `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `proEtaleRootsOfUnitySheaf`, `proEtaleRootsOfUnityModule`,
  `proEtaleRootsOfUnityTower`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`:
  `siteSheafTensorRightMap`, and publicly imported `changeOfRingsOfUniverses`.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` and
  `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage`:
  `proEtaleBaseChange`, `proEtaleSheafDirectImage`,
  `proEtaleRootsOfUnityDirectImageMap`.
* `Sheaf.Paper.TateInverseLimitBaseChange`: `tateModules`, `tatePullback`,
  `tateUnit`, `tateRingUnit`, retaining canonical module pullback/constant-ring maps.
* `Sheaf.Paper.PurInverseImageTensorHom`: `purScalarSection`, the existing
  pure-scalar-tensor/sheafification-unit construction.

The statement uses no new scheme or morphism property beyond those supplied by these
recorded dependencies. Proof-dependency modules with recorded declarations are imported
privately, as stage 2 rule 7 requires; statement constructions are imported publicly.

Edge cases checked: `P.level=1`, `e=1`, `N=1` (root-tower index zero), and all
positive levels not equal to 1; smaller annihilating exponent `j=0`; residue degree
one and ramified coefficients (rank is `e*f`, not one); the empty scheme; arbitrary
non-affine schemes; identity and arbitrary base-change maps; the zero complex and
unbounded K-flat complexes. The source arithmetic assumes `e|n`, so no nondivisible
level is silently rounded. There is no STATEMENT-DISPUTED finding or statement correction.

Searches (also retained in the node's pre-existing search history):

* `msearch.py leanfinder`, query “Finite Kummer comparison from the inverse limit Tate
  sheaf to roots of unity tensor finite coefficient quotient, compatible with derived
  tensor and scheme base change”: 8 hits concerning period rings, affine-limit sections
  and adic-completion tensor equivalences; none states this sheaf comparison.
* `msearch.py loogle`, query `"rootsOfUnity", "tensor"`: OK, 0 hits.
* `msearch.py grep`, query `TateTwist|tateTwist|rootsOfUnity.*sheaf|sheaf.*rootsOfUnity`:
  OK, 0 Mathlib hits.
* `rg` in both named project source trees for `finiteKummerLevel`,
  `IsKummerComparison`, `kummerRootsTensor`, and upstream for the DAG id: no existing
  declaration of this comparison. Searches for `ramificationIndex`, residue fields,
  and Tate constructions located the coefficient and root constructions reused above.

Validation: the repaired module passed `scompile.py`, both the sandbox-name and
library-name checks, with no errors or warnings. The initial saved packet's pass is
not used as evidence for the repaired statement.

## Second reading by Q122

I compared the source statement, the current node and its reviewed 12-step proof,
the returned packet's identity statement, and the repaired Lean signatures. The return
is resolved by using the inverse-limit scalar-extension source and the explicit roots
tensor target, with projection normalization, instead of comparing a finite Tate
object with its definition. The valuation equations, ideal equality, canonical quotient
ring equivalence, residue degree, and scalar-linear finite rank `e*f` equivalence now
occur as actual conclusions. Derived tensor is the image of this same map on K-flat
representatives. Base change has normalized vertical isomorphisms and the commuting
square for all morphisms. Positive predecessor indexing represents every allowed n
and N; it is not an additional mathematical restriction. All helper bodies reuse the
recorded constructions. Only the main named theorem has `sorry`.
