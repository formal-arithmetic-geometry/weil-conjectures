## Worker report

The module `Sheaf.Paper.FiniteExceptionalInternalHom` states
`lem-per-finite-exceptional-internal-hom`, using the canonical ambient internal
adjunction and transporting its first Hom argument by proper coincidence. All
postponed assertions are named theorems with `sorry`; all definitions have real
categorical data. The node statement is unchanged. No new nodes or dependency
repairs are needed.

Hypotheses and clauses:

* A finite commutative ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  The site has scheme universe `u`, and coefficients have universe `u + 1`, the
  published ordinary-etale convention; no equality of independent site universes
  is imposed.
* The finite morphism is `{T S : Scheme.{u}} (f : T ⟶ S) [IsFinite f]`.
  Noetherian means `[IsLocallyNoetherian T] [CompactSpace T]` and the same for S.
  These are explicit on the compatibility theorems. The canonical constructions
  themselves exist in the stronger generality of the published ambient interface.
* Constant-A module sheaves are `Sheaf T.smallEtaleTopology (ModuleCat A)`.
  `DerivedCategory` is ordinary unbounded D; `DerivedCategory.Plus` is the strictly
  full D-plus subcategory. The arguments of `finiteExceptionalInternalHomPlusIso`
  are precisely M and N in these bounded-below categories; its result is in the
  unbounded category, with no boundedness assertion about internal Hom.
* Exactness of finite direct image and its termwise derived interpretation are the
  existing `preservesFiniteColimits_lowerStar_of_isFinite` and
  `rightDerivedFunctorLowerStarIsoMapDerivedCategory` in
  `WeilConjectures.SixFunctors.Finite.Exact`. They are used without copying them.
* `finiteExceptionalSupportIso` is Rf_! ≅ Rf_*, constructed using the proper
  compactification `(id_T,f)` and the published normalized proper comparison.
  `finiteExceptionalAdjunction` transports the actual ambient adjunction by this
  comparison, including its counit. `finiteExceptionalInternalHom_boundedBelow`
  says its right adjoint preserves D-plus. Restricting the ambient Hom bijections
  to the strictly full D-plus categories therefore gives the stated adjunction;
  uniqueness identifies any independently chosen bounded-below right adjoint
  compatibly with the counit.
* `finiteExceptionalInternalHomIso` is a natural isomorphism of bifunctors. It is
  `derivedHomRightDerivedLowerShriekIsoOfFinite` followed by inverse proper
  normalization in the contravariant Hom argument. Its (M,N) component is
  `finiteExceptionalInternalHomPlusIso`, exactly f_*RHom(M,f^!N) ≅ RHom(f_*M,N).
* `finiteExceptionalInternalHom_evaluation` quantifies over every test Q and every
  map h from Q to the left side. It identifies the tensor-Hom transpose with the
  canonical projection followed by the direct image of the transpose of h and
  the exceptional counit. The proper comparison and its inverse explicitly
  convert the compact-support projection to the finite direct-image projection.
  The tensor convention is M tensor f^*Q rather than f^*Q tensor M; composing with
  the canonical symmetry gives exactly the node's order, as in the dependency
  `internalAdjunctionEvaluation`. No arbitrary arrow or isomorphism is assumed.
* `finiteExceptionalInternalHom_commShift` says the second-variable natural
  transformation commutes with the canonical integer shifts. The source-variable
  comparison `finiteExceptionalSourceShiftIso` is constructed by conjugating the
  tensor-shift isomorphism and commuting the negative shift. The theorem
  `finiteExceptionalInternalHom_sourceShift` states the resulting square for
  every integer n, retaining the opposite shift and its Koszul sign convention.
* `finiteExceptionalSliceAdjunction` derives the exact sum-extension/restriction
  adjunction. `finiteExceptionalEtaleBaseChange_isIso` states invertibility of the
  canonical finite direct-image base-change map. `finiteExceptionalSliceSumExchange`
  is its inverse mate, and `finiteExceptionalRestriction` is its conjugate under
  the exceptional adjunctions. `finiteExceptionalHomRestriction` is restriction of
  evaluation transposed using the canonical tensor-pullback comparison.
  `finiteExceptionalInternalHom_restriction` asserts invertibility of these
  exceptional and Hom comparisons and their full commutative square with the
  internal adjunction. The etale object U is arbitrary: no quasi-compactness,
  separatedness or global Noetherian condition on U is added.
* `finiteExceptionalInternalHom_unit` states the isomorphism for M equal to the
  derived tensor unit (the constant A sheaf in degree zero). Its docstring fixes
  the identification RHom(A_T,I) ≅ I by evaluation at 1. It is a consequence of
  the already canonical bifunctor isomorphism, not replacement data for it.
* `finiteExceptionalCompIso` is the counit-compatible adjunction conjugate of
  `rightDerivedLowerStarComp`. `finiteExceptionalInternalHom_composition` is the
  full equality between the composite-map internal adjunction and the successive
  internal adjunctions, including the direct-image and contravariant-Hom
  comparisons. Both g and f are finite, with all three schemes Noetherian.
* `finiteExceptionalInternalHom_counit` takes each morphism a : M → f^!N and
  states that precomposing its adjunct with f_*(epsilon_g) equals the composite
  adjunct of g^!a. Evaluation and the composition square identify this with the
  internal-Hom assertion in the final sentence of the node.

Recorded statement dependencies used:

* `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the ordinary ModuleCat
  encoding, `DerivedCategory`, `DerivedCategory.Plus`, and standard t-structure.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` and the
  compactification-independent `rightDerivedLowerShriek`.
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: the generic derived
  internal Hom interface and its public ordinary-etale presentation
  `AlgebraicGeometry.Etale.derivedHom`, `derivedTensorHomAdjunction`.
* `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`;
  its ambient chosen right adjoint and adjunction are the existing `R(f)^!` and
  `rightDerivedUpperShriekAdjunction` of the upstream UpperShriek module.
* `WeilConjectures.SixFunctors.Etale.Derived.TensorHom`:
  `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIsoOfFinite`.
* `Sheaf.SmoothPurity.InternalAdjunctionEvaluation`:
  `AlgebraicGeometry.Etale.internalAdjunctionEvaluation`.

The source signatures and docstrings were read in the named source checkouts.
The migrated DerivedCategories source was read with `scompile.py --source`.
The earlier attempt's saved current TensorHom source was also checked: its
finite-coefficient canonical isomorphism is an ambient one for arbitrary schemes.
All stated proof-dependency modules are explicitly imported, with non-public
imports where only proof work needs them. The proper normalization additionally
uses `unboundedEtaleProperCandidateIso` from
`Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition`.

Edge cases checked: empty schemes and empty finite fibres; zero objects; the zero
coefficient ring; shifts n = 0 and arbitrary positive/negative n; unbounded
internal Hom despite bounded-below inputs; nonseparated and non-quasi-compact
etale slice objects. The finite-product/sum exchange handles empty fibres and
arbitrarily large slice-index sets. There is no constructibility, invertible
prime, finite Tor dimension, or bounded-above hypothesis.

Searches (retained `searches.jsonl` records the tool responses):

* LeanFinder, “For a finite morphism of schemes derived internal Hom of direct
  image is direct image of internal Hom into exceptional pullback”: results are
  scheme module pullback/pushforward adjunctions, not this statement.
* LeanSearch, “finite etale derived direct image exceptional inverse image
  internal Hom adjunction”: generic adjunctions only, no exact statement.
* Loogle, `derivedHomRightDerivedLowerShriekIsoOfFinite`: no Mathlib hit; the
  declaration does exist upstream and is used here for the ambient clause.
* Loogle, `CategoryTheory.MonoidalClosed.unitIsoSelf`: exact unit-Hom identification.
* msearch grep, `finite.*[Ii]nternal|[Ff]inite.*[Ee]xceptional`, including restricted
  CategoryTheory searches: unrelated finite-module results; no exact match.
* rg of the upstream source and project `lean/Sheaf` for `finiteExceptional`,
  finite internal adjunction, and the node id: the constructible/system exceptional
  functors and general compact-support compositor have different domains or
  scopes. The ambient canonical Hom isomorphism exists and is reused; no existing
  declaration states this node's finite normalization and all compatibilities.

Source checked: ILO XVII Proposition 5.4.1, pp. 291,293, the Hom-dualized finite
triangles; the expanded twelve-step proof in the current DAG node. No statement
fault or disputed assertion was found.

Validation: the retained draft timed out in its explicit unit-Hom definition.
This was repaired by stating that specialization as a theorem consequence of the
canonical bifunctor isomorphism; the other constructions remain concrete.
The exact slice-adjunction invocation was also repaired. Final compilation and
server preflight are recorded by the delivery tool.

## Second reading by N6

I reread the complete current node and the module clause by clause as listed
above. The initial draft's unit-Hom definition caused kernel reduction to exceed
the limit; it is now a named theorem with its evaluation-at-1 proof plan, without
changing the canonical main isomorphism. I checked the source-shift sign, the
contravariant direction of the direct-image compositor, and the restriction
square with an arbitrary etale U. Each postponed theorem has the source and its
corresponding proof steps in its docstring. No node text was changed.

This is the dispatcher's single-worker workflow: no second agent was started.
This section records a fresh self-reading, not an independent-agent review; the
maintainer's independent review remains required by the task brief.
