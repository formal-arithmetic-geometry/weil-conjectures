## Worker report

`Sheaf.PoincareDuality.OpenModuleKFlatProjectionModel` states
`AlgebraicGeometry.ProEtale.CondensedRing.openModuleKFlatProjectionModel` with one `sorry`.
Its four endpoint/comparison helpers have real data; they introduce neither a second tensor
nor a choice of projection morphism. The node's statement and dependencies are unchanged.

Source read: the current blueprint, `literature/blueprint/latest/blueprint/`
`sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-projection.proof.md`,
Derived version. The nine expanded proof steps in the DAG are included in the theorem's
docstring, including signed totalization, the acyclic tensor tests and normalization of
the actual derived mate. The source record's historical snapshot was not used.

Hypotheses and objects, clause by clause:

- The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The field is `(k : Type u) [Field k]`;
  `[Fact (ringChar k).Prime]` expresses its positive prime characteristic and
  `[Fact (ringChar k ≠ ℓ)]` gives the required inequality.
- `U Z : Scheme.{u}`, their `Over (Spec (.of k))` structures, and separated,
  locally-of-finite-type and quasi-compact structure morphisms express precisely the
  separated finite-type setting. `[j.IsOver (Spec (.of k))]` makes `j` a k-morphism;
  `[IsOpenImmersion j]` is the open immersion hypothesis.
- The section variable `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}` with
  `[MonObj Λ] [IsCommMonObj Λ]` is an arbitrary commutative condensed ring, including
  those without a topological-ring presentation. `condensedRingObj Λ T` is its actual
  pulled-back coefficient object. `supportModules Λ T` is the recorded internal `Mod`
  category over that object. The site retains its original object and morphism universes.
- Module tensor `⊗` is the recorded relative balanced tensor. The complexes are arbitrary
  `CochainComplex (supportModules Λ T) ℤ`. `HomologicalComplex.tensorObj` is the existing
  direct-sum total over p+q=n with differential d_P tensor 1 + (-1)^p 1 tensor d_Q.
  No boundedness or finite-total alternative is introduced.
- E and R are exactly `openImmersionLowerShriek Λ j` and `upperStar Λ j`.
  Their levelwise applications are `mapHomologicalComplex (.up ℤ)`.
  The endpoints `openModuleProjectionSource` and `openModuleProjectionTarget` are
  respectively E Tot(P tensor RQ) and Tot(EP tensor Q), with no data chosen.
- `ObjectProperty.flat` is the existing categorical exact-tensor predicate (both sides,
  equivalent by symmetry). `IsKFlatModuleObject T (CommMon.mk (condensedRingObj Λ T))`
  is exactly the dependency's one-sided acyclic total-tensor test. `CommMon.mk` merely
  bundles the actual coefficient object and its existing structures.

Conclusions, clause by clause:

- The first conjunct states that E preserves every flat module. The second states that
  E preserves every K-flat complex, with no hypothesis on its terms.
- The third conjunct assumes Q is K-flat with every term flat, and states that RQ is
  K-flat and every term of RQ is flat. There is no extra assertion required of Q.
- `∃ Φ : ∀ P Q, source ≅ target` supplies a chain isomorphism for every unbounded pair.
  Its first clause quantifies p,q,n and h:p+q=n. The bidegree isomorphism `b` has
  `b.hom = openModuleBalancedProjectionMap Λ j (P.X p) (Q.X q)`. The two following
  equations are exactly E(iota) followed by Phi = theta followed by target iota,
  and target iota followed by Phi inverse = theta inverse followed by E(iota).
  Thus the inverse uses the same inverse bidegree maps, not an unspecified chain inverse.
  The auxiliary existential `b` expresses the already recorded invertibility of theta;
  its forward map is fixed, so its inverse is uniquely determined.
- The next clause quantifies arbitrary chain maps a and b and states the naturality square
  using `HomologicalComplex.tensorHom` and the specified levelwise functors.
- For K-flat P,Q with flat terms, the last clause asserts `IsIso` of both canonical
  localization comparisons. The source comparison is e of tensoring the exact-factor
  comparison r(Q_Z Q) -> Q_U(RQ), followed by the lax tensorator of Q_U, followed by
  the exact factorization of E. The target comparison is the tensor of E's exact-factor
  comparison with identity, followed by the lax tensorator of Q_Z.
- The final equation is sourceComparison followed by Q_Z(Phi.hom) = e(eta tensor 1),
  followed by e(mu), followed by epsilon, followed by targetComparison. Since both
  endpoint comparisons are asserted invertible, this is exactly the node's equality
  after the specified identifications. Here e is E.mapDerivedCategory and r is the
  recorded `moduleObjectDerivedPullback`, namely the actual total left derived pullback.
- Eta and epsilon are those of `ModuleRingedComparison.internalOpenAdjunction`, which
  derives the specified ordinary module adjunction and transports its right adjoint by
  `leftDerivedUpperStarIsoMapDerivedCategory`. Mu is explicitly the inverse of
  `(upperStar Λ j).leftDerivedTensorComparison`, exactly the expression defining
  `internalDelta`/`internalMu` in the recorded internal-to-section derived comparison.
  No arbitrary monoidal structure, adjunction, isomorphism or mere Nonempty witness replaces it.
- On every bidegree theta is the existing `openModuleBalancedProjectionMap`, whose body is
  E(u tensor 1 followed by nu) followed by v. Its `openModuleTensorComparison` is the
  transported inverse of `supportTensorComparison`. Thus the final representative clause
  in the node is retained by definition, with the specified inverse ordinary tensor map.

Dependency declarations read and used (all in their owning namespaces):

- `sk-def-sfb-dc-setting`: the explicit field/scheme setting of
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`;
  no compactification is needed in this open-immersion statement.
- `sk-def-sfb-condensed-ring`: `Profinite.CondensedRing`,
  `Sheaf.Topology.ProfiniteCondensedRing`; its transparent underlying sheaf/ring-object encoding.
- `def-weil-pbc-proetale-site`: `Scheme.ProEt` and `ProEt.topology`,
  `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `sk-def-sfb-pulled-back-coefficients`: `coefficientRing`, `condensedRingObj`,
  `isCommMonObj_condensedRingObj`, in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
- `sk-def-sfb-module-objects`: `CategoryTheory.Mod`, `Mathlib.CategoryTheory.Monoidal.Mod`.
- `def-sfb-modobj-relative-tensor`: `Mod.monoidalCategory`,
  `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`; the tensor's underlying object
  and balanced quotient are the existing `tensorObj_X` and `tensorObjπ`.
- `def-sfb-module-open-lower-shriek`, `def-sfb-module-open-lower-shriek-adjunction`, and
  `sk-def-sfb-module-lower-shriek`: `openImmersionLowerShriek` and
  `openImmersionLowerShriekUpperStarAdjunction`,
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`.
- `def-sfb-module-upper-star`: `upperStar`,
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`.
- `def-sfb-condensed-pullback-tensor-comparison`: `supportModules`,
  `supportPullbackIsoUpperStar`, `supportTensorComparison`,
  `supportComplexTensorComparison`, `supportDerivedTensorComparison`,
  `Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison`.
- `sk-def-sfb-module-derived-pushpull`: `moduleObjectDerivedPullback`,
  `Sheaf.Paper.CondensedModuleDerivedPushpull`; its body is the generic left derived functor.
- `sk-def-sfb-derived-tensor-hom`: `derivedTensor`/`derivedHom`,
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` (and its Tensor import).
  The canonical derived tensor is used through its monoidal instance, not redefined.
- `pur713-def-kflat-module`: `IsKFlatModuleObject`,
  `Sheaf.Algebra.Homology.KFlatModuleObject`; `HomologicalComplex.tensorObj` and
  `HomologicalComplex.ιTensorObj`, `Mathlib.Algebra.Homology.Monoidal`.
- `lem-pd-open-module-balanced-projection`: `openModuleBalancedProjectionMap`,
  `openModuleTensorComparison`, `openModuleBalancedProjection`,
  `Sheaf.PoincareDuality.OpenModuleBalancedProjection`.
- `lem-pd-module-ringed-topos-derived-comparison`: `internalOpenAdjunction`,
  `internalDelta`, `internalMu`, `internalOpenProjection`, `openProjection_comparison`,
  `Sheaf.Paper.ModuleRingedToposDerivedComparison` and its public SectionDerived imports.
  The displayed mate unfolds the very same internal formula; the fixed ringed comparison
  remains the existing dependency, without a new section-module construction or size restriction.
- Proof inputs are imported explicitly: `Adjunction.leftAdjoint_preservesColimits`,
  `Functor.homologyFunctorIso`, `Functor.mapDerivedCategoryFactors`,
  `Adjunction.localization` and its unit/counit formulas, and `Mod.symmetricCategory`.
  The theorem docstring maps each of the node's nine proof steps to those inputs.

Edge cases checked before writing: zero P or Q; the zero coefficient ring (no Nontrivial
hypothesis); identity j; the empty open U; negative cochain degrees and parity of p; infinite
families p+q=n. The insertion equations quantify every integer triple and use the actual
unbounded direct-sum tensor. No restriction on support, Tor dimension, boundedness or
constructibility occurs. There is no new hypothesis about site universes or a chosen
section-module derived-category instance.

Searches for an existing statement:

- `msearch.py leanfinder`, query “Extension by zero of internal modules preserves K-flat
  complexes and the total tensor projection isomorphism localizes to the derived adjunction
  mate”: 8 results, ordinary module-flatness criteria and scalar descent; no matching theorem.
- `msearch.py loogle`, query “HomologicalComplex.tensorObj, Functor.mapHomologicalComplex”:
  0 hits, with service note unknown identifier Functor.mapHomologicalComplex.
- `msearch.py grep`, query `openModule.*[Kk][Ff]lat|[Kk][Ff]lat.*[Pp]rojection`: 0 hits.
- `msearch.py leansearch`, query “K flat complex extension by zero open immersion tensor
  projection formula”: 8 results about ordinary module flatness and flat scheme morphisms,
  no internal-module chain projection theorem.
- `rg` on Mathlib/WeilConjectures/Sheaf for KFlat/kFlat, openModule, projection models,
  total tensor and derived comparison names: the existing generic total tensor,
  ringed-site models and internal/section comparison were found and reused. None states
  this natural internal open chain isomorphism together with its normalized mate equality.
- Searching the upstream WeilConjectures tree for the exact node id returned no hit.
  The DAG search for the item found only this item and its exceptional-projection consumer.
  No new independent notion or dependency repair was needed.

Validation: scompile.py compiled the final body in both sandbox and library module modes,
with autoImplicit false and no errors or warnings. The initial single long-line warning
was repaired. All proof work remains postponed in the named main theorem.

## Second reading by Q88

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
