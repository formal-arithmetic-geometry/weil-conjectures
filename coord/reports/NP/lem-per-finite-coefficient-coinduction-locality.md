## Worker report

This repairs the returned delivery `ce48b7ab406c`, specifically the maintainer's
H13/H4 finding. The saved packet's initial resumed dry run passed automated checks,
but the dependency-record replacement was still present. Removed the sandbox copy of
`def-pur-etale-supported-kernel` and removed
`Sheaf.AlgebraicGeometry.EtaleSupportedKernelCoefficients`. The live dependency record
continues to name the existing abelian-sheaf `supportedKernel` and
`supportedClosedInverseImage` in `EtaleSupportedKernelAdjunction`.

Moved the two constant-module coefficient constructions and their additivity
results, with item blueprint and Stacks 09XQ docstrings, into the owning item module
`Sheaf.AlgebraicGeometry.FiniteCoefficientCoinductionLocality`. They are now listed
in this item's `lean.declarations`. The main module directly imports the original
abelian-sheaf module, upstream coextension and the additive-functor API. Its main
signature and the node's natural statement, dependencies, proof and proof dependencies
are unchanged. Definitions contain real data; the named theorem postponements have
source and proof docstrings. No dependency node is delivered or overwritten.

Hypotheses and clauses, matched against the node:

* Arbitrary commutative rings and their homomorphism are `{A B : Type (u + 1)}`,
  `[CommRing A]`, `[CommRing B]`, `(φ : A →+* B)`. Schemes are `Scheme.{u}`;
  coefficient sheaves are `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` and
  the corresponding B category. These are the existing six-functor coefficient
  conventions, with no finite-ring, noetherian, characteristic or torsion assumption.
* The augmented resolution is `P : CochainComplex (ModuleCat A) ℤ` and
  `ε : P ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
  ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))`.
  `hε : QuasiIso ε` says exactly that the augmented complex resolves B[0].
  `hP` makes every positive-degree term zero; `hfree` identifies each term with
  `ModuleCat.of A (Fin r → A)` for some finite r. There is no bound below on P,
  nor an assumption of finite projective dimension.
* `C_X` is the existing `(coextendScalars φ X).rightDerivedFunctorPlus`.
  Underived `coextendScalars` is sectionwise `ModuleCat.coextendScalars`, whose
  carrier is `B →ₗ[A] M` and whose B-action is `(b h)(b') = h(bb')`.
  `coinduction_injective_representative` asserts that its canonical derived unit
  is invertible on every bounded-below complex of injective sheaves. Thus this
  is precisely the node's Hom(B_X,I) construction, not a freely chosen functor.
  `finiteCoinduction_underlying_rhom` additionally identifies its scalar restriction
  with the recorded `derivedHom` from the actual constant A-module sheaf B in degree
  zero. The isomorphism is natural in the derived input.
* `finiteCoinductionAdjunction` is the actual derived adjunction of the existing
  sectionwise restriction/coextension adjunction. Its left adjoint is exact
  restriction's `mapDerivedCategoryPlus`; no arbitrary adjunction is assumed here.
* The lower cohomology bound is `coinduction_preserves_lower_bound`:
  `K.IsGE a → (C_X.obj K).IsGE a`, in the standard bounded-below t-structure.
* Arbitrary scheme inverse image is `(upperStar (ModuleCat A) g).mapDerivedCategoryPlus`.
  `coinductionScalarPullbackIso` is the conjugate of the sectionwise direct-image /
  coextension identity. Its localization is `coinductionScalarPullbackIsoPlus`.
  `finiteCoinductionPullbackMap` is its mate under the derived scalar adjunctions,
  so its adjunct is pulled-back evaluation, and it is a morphism over B.
  The principal theorem asserts `IsIso (finiteCoinductionPullbackMap φ g)`.
* Closed extraordinary restriction is
  `(supportedClosedInverseImageCoefficients R i j).rightDerivedFunctorPlus`,
  where j is the complementary open immersion. The theorem
  `coinduction_supported_closed_adjunction` supplies the coefficient closed adjunction
  for every closed i, open j and `IsCompl (Set.range i.base) (Set.range j.base)`.
  Thus the adjunction arguments of `finiteCoinductionClosedIso` are available from
  the hypotheses of the node; they are not an extra existence assumption.
  That definition conjugates `coinductionScalarClosedImageIsoPlus`, the localization
  of the sectionwise identity commuting scalar restriction with closed direct image.
  It gives the required B-linear natural isomorphism, with the indicated direction.
* `finiteCoinductionClosedIso_counit` states the counit equation for the two pasted
  adjunctions, including the scalar/direct-image isomorphism. It fixes the requested
  normalization explicitly rather than asserting existence of an arbitrary iso.
* Pullback composition and identity are the equality of transformations in
  `finiteCoinductionPullbackMap_comp` and `finiteCoinductionPullbackMap_id`, using
  `upperStarCompDerivedPlus` and `upperStarIdDerivedPlus`. Closed composition is
  `finiteCoinductionClosedIso_comp`: conjugating the pasted scalar/direct-image
  square equals pasting the two closed comparisons. Composite closed right adjoints
  are identified by their composite adjunctions, the canonical composition convention.
* For a point x, `finiteCoinductionCostalkMap` uses precisely `X.fromSpecStalk x`
  and the closed immersion `Spec.map (X.residue x)` from Spec(kappa(x)) to
  Spec(O_X,x). It first applies the pullback comparison and then the closed one.
  `finiteCoinduction_costalk_locality` asserts invertibility. Its final universally
  quantified clause composes with inverse image along every
  `e : Spec (.of Ω) ⟶ Spec (X.residueField x)`, `[Field Ω] [IsAlgClosed Ω]`,
  then the comparison for e. This is the geometric-fibre clause, in the coefficient
  category over Spec(Ω); it does not invoke an extraordinary base-change theorem.
* The rank-one hypothesis in `finiteCoinduction_rank_one_twist` says that for
  every etale U there is a covering sieve S and, on every arrow in S, an isomorphism
  `L.over V ≅ (𝟙_ (Sheaf ... (ModuleCat A))).over V`. The monoidal unit is A_X,
  so this is exactly local freeness of rank one, including nontrivial lines.
  `coinductionCoefficientLine` constructs L_B by sheafifying the presheaf
  `L.obj ⋙ ModuleCat.extendScalars φ`; it is B_X tensor_A_X L. The twist theorem
  is an isomorphism of functors, hence natural in K. Tensor by a locally trivial
  line is exact, so its `rightDerivedFunctorPlus` in that statement agrees with
  ordinary tensor by the line on complexes. The displayed direction is
  C_X(K tensor L) ≅ C_X(K) tensor L_B.
* Shift compatibility is asserted by `NatTrans.CommShift ℤ` for the pullback,
  closed, costalk, geometric-fibre, and rank-one twist comparisons.
* No clause assumes constructibility or a Tor bound on K. K ranges over the full
  bounded-below category; the resolution is allowed infinitely many negative terms.

Dependency declarations actually used, with their owning modules:

* `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule` and the existing `DerivedCategory.Plus` convention.
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses` publicly exposes the
  ordinary-etale specialization `Etale.derivedHom` from
  `WeilConjectures.SixFunctors.Etale.Derived.Hom`. The RHom comparison uses this
  specialization, retaining the dependency's generic independent-universe interface.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction`.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`
  and the instance for `Spec.map (X.residue x)`.
* `Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction`:
  `Etale.supportedKernel`, `Etale.supportedClosedInverseImage`, and its adjunction
  statement; the main module imports this original abelian interface directly.
  The coefficient helpers belong to the present item, not to that dependency node.
* `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.residue`, `Scheme.fromSpecStalk`; `IsAlgClosed` is from
  `Mathlib.FieldTheory.IsAlgClosed.Basic`. Geometric points are inline as recorded.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` retains the
  generic sheaf-tensor dependency; ordinary fixed-coefficient etale tensor uses
  its existing `Sheaf` monoidal specialization, imported through the recorded
  ordinary-etale Hom module. Scalar extension uses `ModuleCat.extendScalars`
  followed by the existing sheafification functor.
* `WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars`:
  `Etale.coextendScalars`, `Etale.lowerStarCompCoextendScalarsIso`,
  `Sheaf.restrictScalars`, `Sheaf.restrictCoextendScalarsAdj`.
  Derived localization, adjunction, mate and coherence interfaces are the existing
  `Functor.mapDerivedCategoryPlus*`, `Adjunction.derivedPlus`, `conjugateIsoEquiv`,
  `mateEquiv`, `upperStarCompDerivedPlus`, and `upperStarIdDerivedPlus`.

The proof-dependency modules are retained as non-public imports: ringed-site modules,
sheaf internal Hom, injective preservation, module-sheaf enough injectives, injective
representatives, homotopy adjunction, K-injective localization, constant exactness,
bounded-free RHom, RHom quasi-isomorphism invariance, inverse-image exactness,
cohomology detection, adjoint uniqueness and mate pasting. They are proof inputs,
not hypotheses added to the theorem. Every proof remains `sorry`.

Edge cases checked: A=B with identity coefficient map; the zero ring; zero terms and
rank r=0 in the resolution; empty schemes and empty complementary opens; identity
and empty closed immersions; unbounded periodic finite-free resolutions (each Hom
diagonal remains finite); arbitrary lower bound a; nontrivial as well as trivial lines;
and arbitrary geometric points over kappa(x). No termwise strict B-action is placed on
P. The schemes' site and coefficient universe convention is the recorded one.

Searches: retained `searches.jsonl` records the earlier LeanFinder query
"Derived coinduction of etale module sheaves commutes with inverse image and closed
extraordinary restriction" (8 hits, only underived pullback/restriction), Loogle
`"SheafOfModules", "restrictScalars"` (12 underived hits), and Mathlib grep
`coextendScalars|coinduc` in CategoryTheory (2 unrelated hits). Earlier node searches
also include LeanSearch for this locality statement and the bounded-free Hom model.
Fresh grep of `lean/Sheaf` and upstream `WeilConjectures` for `finiteCoinduction`,
`coinductionScalarPullbackIso` and `supportedKernelCoefficients` found no duplicate
of these interfaces. Upstream blueprint-id search found no existing declaration for
the item. Existing coextension, scalar restriction, tensor and internal Hom were
therefore used, not redefined. Read the actual Stacks 08JI finite-diagonal model and
09XQ closed-support adjunction proof, and the retained Gabber extract, printed p. 294.
There is no statement correction and no outstanding statement dispute.

## Second reading by NP

This is the dispatched worker's second pass; no sub-agent was started, in accordance
with the dispatcher's explicit instruction. The maintainer's independent reading
remains the delivery review. I reopened the node and both module files and checked
every clause against the correspondence above. The pass found and repaired the
missing principal theorem and lean record, the incorrect inference of a composite
in the scalar/closed-image localization, and an attempted use of `single₀` (which is
N-indexed) for the Z-indexed resolution. The augmentation now uses the actual Z-indexed
single complex. It also added explicit composition equalities, the counit equation,
actual costalk and geometric-fibre maps, a genuine local-rank-one hypothesis and
constructed scalar-extension line, and shift compatibility for every stated
comparison. The RHom bridge is a natural isomorphism; its source and target use the
recorded constant-coefficient category. No arbitrary iso is substituted for the
normalized pullback, closed or costalk comparison. The returned H13/H4 issue is repaired by leaving that dependency record intact and
owning the coefficient helpers in this item's module.

## Returned-delivery repair self-check

Reopened the retained report, both original modules, the item record, and the live
`def-pur-etale-supported-kernel` node and its full source. The latter is explicitly
an abelian-sheaf notion with `existing: true`; replacing its record by a
ModuleCat-valued specialization was the mismatch. The current `SupportedBottomGluing`
source uses `Etale.supportedKernel`, confirming why the landed interface must stay.
This repair changes no existing library declaration or consumer file.

Compared the repaired item against the live node outside `lean`, checked the main
signature verbatim, the declaration inventory, source/item blueprint tags, explicit
binders, line lengths, all actual definition bodies, and the retained clause mapping.
The two coefficient definitions and both additivity results are the same constructions
as the returned version, now inside the item module. No mathematical statement was
changed and no new node or dependency module is included. No outstanding statement
dispute remains. The main module compiled cleanly through `scompile.py`, both in its
sandbox probe and under its library module name (12.6 s and 13.0 s respectively).
