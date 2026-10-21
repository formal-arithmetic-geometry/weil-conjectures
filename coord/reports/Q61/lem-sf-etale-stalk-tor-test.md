## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleStalkTorTest` states
`AlgebraicGeometry.Etale.geometricStalk_torAmplitude_test`, with one `sorry` proof.
It states the geometric-stalk equivalence and, as a second conjunct, inverse-image
preservation of the identical interval. No definition, helper theorem, new node,
dependency repair or statement correction is needed. The original node is unchanged
outside `lean`.

Hypotheses and clauses, checked against the node and the local source of Stacks
0DJJ (`sites-cohomology.tex`, lemma-tor-amplitude-stalk), and 03Q1
(`etale-cohomology.tex`, lemma-stalk-pullback):

- A commutative ring: `(A : Type (u + 1)) [CommRing A]`. There is no nontriviality,
  Noetherian, finite, Artinian, local or torsion hypothesis.
- A scheme: `(T : Scheme.{u})`, without separation, size-of-cover or finiteness
  assumptions. This is the recorded ordinary etale encoding, with coefficients
  and module carriers in universe `u + 1` and geometric fields in `u`.
- An arbitrary derived object: `(K : DerivedCategoryModule A T)`. This is the
  existing unbounded localization of module-valued small-etale sheaf complexes;
  no boundedness or constructibility predicate is assumed.
- Integers with a <= b: `(a b : ℤ) (_hab : a ≤ b)`. The underscore merely suppresses
  an unused-argument warning for the stage-2 statement; the hypothesis is retained.
- Tor amplitude [a,b]: `DerivedCategory.hasTorAmplitudeIn A T a b K`, the recorded
  predicate testing every module sheaf in degree zero. Its `↔` has both directions.
- Every geometric point: `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ T)`. No chosen point or rational-point restriction occurs.
- Every ordinary A-module: `(M : ModuleCat.{u + 1} A)`, with no finite-generation
  or flatness condition. `(_root_.DerivedCategory.singleFunctor ... 0).obj M`
  places it in degree zero.
- The derived stalk of K: `((pointSmallEtale t).sheafFiber
  (A := ModuleCat.{u + 1} A)).mapDerivedCategory.obj K`. The existing additive
  instance is `moduleSheafFiber_additive` from `EtaleDerivedTensorStalk`.
  `Point.sheafFiber` is the same pointed-neighbourhood colimit as the recorded
  `pointedEtaleStalk`: unfold `pointedEtaleStalk`, `pointedEtaleStalkDiagram`,
  `Point.sheafFiber` and `Point.presheafFiber`. Both have diagram
  `(CategoryOfElements.π (pointSmallEtale t).fiber).op ⋙ F.obj` and its colimit.
  The former packages the same construction as a functor, needed for derived passage.
- Derived ordinary-module tensor: `...mapDerivedCategory.obj K ⊗ ...singleFunctor...M`
  in `DerivedCategory (ModuleCat A)`, using the existing derived monoidal structure.
- Cohomology only in [a,b]: `(i : ℤ), i < a ∨ b < i → IsZero
  ((_root_.DerivedCategory.homologyFunctor (ModuleCat A) i).obj (...))`.
  This tests every integer outside the closed interval and asserts vanishing of
  the ordinary module object, not categorical zero for a bare carrier type.
- The consequence covers every scheme morphism: the second conjunct begins
  `∀ (U : Scheme.{u}) (f : U ⟶ T)`. The implication takes exactly the original
  amplitude hypothesis and concludes `DerivedCategory.hasTorAmplitudeIn A U a b`
  of `((upperStar (ModuleCat A) f).mapDerivedCategory.obj K)`. This is termwise
  passage of the exact constant-coefficient inverse image; both endpoints are
  unchanged and no geometric property of f is imposed.

Dependency interfaces read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its public source
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`:
  `AlgebraicGeometry.pointedEtaleStalkDiagram`, `pointedEtaleStalk`.
  The functorial form is Mathlib `GrothendieckTopology.Point.sheafFiber`.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: the recorded node's owning module;
  its docstring identifies the bounded predicate above as the existing one and
  only adds `hasTorAmplitudeGE`, which this item does not need.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`. Its full signature packages
  the constant-ring identification, unique transported action, exactness and
  adjunction. In the already recorded module-valued etale sheaf encoding,
  inverse image is `AlgebraicGeometry.Etale.upperStar`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` exposes that exact
  inverse image and its `Functor.mapDerivedCategory` interface.
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk`:
  `moduleSheafFiber_additive` is needed by the signature; its
  `exists_derivedTensor_stalk_iso` is the proof's unbounded tensor comparison.
- Proof-only imports include
  `Sheaf.SixFunctors.GeometricStalkTensorConstantSingle`:
  `geometricStalk_tensor_constant_single`;
  `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`:
  `Scheme.preservesFiniteLimits_geometricStalkFunctor`,
  `Scheme.preservesFiniteColimits_geometricStalkFunctor`,
  `Scheme.shortExact_map_geometricStalkFunctor`;
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`:
  `Functor.preservesHomologyOfExact`;
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`:
  `Scheme.isIso_of_isIso_sheafFiber_map`;
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`:
  `Etale.upperStarCompSheafFiberIso`.
  Thus every recorded proof dependency has its module imported, with the
  tensor/stalk module public because its additive instance enters the signature.

Edge cases checked before writing and in the final reading: empty T (all sheaves
and derived objects are zero and the geometric-point test is vacuous); K = 0;
the zero ring (all modules zero); M = 0; a = b; an interval not containing zero
(the unit in degree zero fails the test for nonzero A and nonempty T); arbitrary
shifts and unbounded K; non-Noetherian A; empty U; identity f; arbitrary f. The
criterion only uses enough geometric points and exactness, so no cohomological
dimension or finiteness hypothesis is hidden. The interval-order binder is the
node's own restriction. There is no statement dispute.

Searches for an existing statement, all on 2026-10-21:

- `msearch.py ... leansearch "Tor amplitude of sheaf complexes detected by stalks"`:
  eight hits, including `TopCat.Presheaf.stalk`, `ModuleCat.Tilde.stalkIso`, and
  `Module.rankAtStalk_tensorProduct`; no derived etale Tor criterion.
- `msearch.py ... leanfinder "Tor amplitude of derived etale module sheaves detected
  on geometric stalks and preserved by inverse image"`: eight hits about etale ring
  maps, e.g. `RingHom.Etale.propertyIsLocal`, `Algebra.etaleLocus`; no match.
- `msearch.py ... loogle '"hasTorAmplitudeIn"'`: zero hits.
- `msearch.py ... grep 'torAmplitude|hasTorAmplitude|stalk.*[Tt]ensor'`: thirteen
  hits about rank at stalks and surjective ring maps, no derived sheaf criterion.
- `rg -n 'hasTorAmplitude|[Tt]orAmplitude|tor_amplitude'` on both the project's
  `lean/WeilConjectures` and `lean/Sheaf`: the existing interval predicates, flat
  models, residue tests and pullback stability are present; no statement with
  both this criterion and its consequence. The residue test in
  `Derived/Finiteness/ResidueTorTest` assumes an Artinian local ring and tests one
  constant residue module; it is a different theorem. The existing
  `torAmplitudeIn_leftDerivedUpperStar` supplies the pullback clause in a generic
  coefficient category, but does not state the geometric-stalk equivalence.
- `rg -n 'lem-sf-etale-stalk-tor-test'` on both source roots, and
  `rg -n 'geometricStalk_torAmplitude_test'` on those roots and
  `dag/lean_names_upstream.json`: no existing declaration.

Validation: `scompile.py Q61 lem-sf-etale-stalk-tor-test <file>` compiled the sandbox
and library forms cleanly, in 4.5 s and 5.3 s respectively. There are no extra
assumptions supplied by binders, no file-local notation or instances, and all
variables/universes are explicitly bound (`set_option autoImplicit false`).

## Second reading by Q61

I reopened the node and final module for a separate clause-by-clause pass; this
is a worker self-check, with independent delivery review left to the maintainer
as specified by the dispatcher. The first conjunct is exactly the node's iff,
quantifying over all geometric points and all ordinary modules, with the
out-of-interval cohomology condition. The second conjunct states preservation
for every f with the same K, A, a and b. The node's a <= b binder is retained.
I checked that tensor here is in ordinary derived modules, whereas the left
predicate uses the existing etale derived tensor. No boundedness, finiteness,
flatness or invertibility hypothesis was introduced. `pointedEtaleStalk` and
`Point.sheafFiber` use the same opposite neighbourhood diagram; the latter's
functor structure is required for localization. The natural-language proof has
all four DAG steps, including constant-module tests in the forward direction
and arbitrary stalk modules in the reverse direction. No mismatch found and
no statement changes made.
