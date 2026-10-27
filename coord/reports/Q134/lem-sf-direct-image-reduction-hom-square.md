## Worker report

Item: `lem-sf-direct-image-reduction-hom-square`. Module:
`Sheaf.Paper.DirectImageReductionHomSquare`. Namespace:
`WeilConjectures.DirectImageReductionHom`.

The statement is unchanged. There are no new DAG nodes and no dependency-record
repairs. The main postponed theorems are `hom_square`, `transition_representation`, and
`hom_square_transitions`. The repair also states the named additivity/exactness,
normalized geometric derived-adjunction existence/uniqueness, and normalized
pullback/tensor comparison existence/uniqueness facts needed to construct beta.
All theorem proofs are `sorry`; each has a source and complete proof docstring.
All definitions have real data, using Mathlib constructions or uniquely normalized
universal objects. These helpers express the projection mate already required by
this node and do not introduce a new coefficient or derived-category notion.
The maintainer supplies the independent delivery review; the second reading below
is this worker's separate final pass, without spawning another agent.

### Hypotheses and clauses

- Prime ell: `l : ℕ` with `[Fact l.Prime]`. The field extension is `E : Type u`
  with `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  The recorded Padic coefficient construction fixes its valuation ring,
  uniformizer and quotient rings. Its index `n : ℕ` represents exponent `n+1`,
  so every positive exponent occurs, including exponent one.
- Schemes and map: `{Z X : Scheme.{t}} (f : Z ⟶ X)`. Invertibility of ell on
  both schemes is `_hZ : IsUnit (l : Γ(Z, ⊤))` and the analogous `_hX`.
  There is no properness, constructibility, boundedness or field-of-definition
  hypothesis. Scheme and coefficient universes `t,u` are independent. The small
  sites keep object universe `t+1`, morphism universe `t`; module coefficients
  have universe `max u (t+1)`.
- Completed coefficient sheaves and ordinary unbounded module derived categories:
  `DerivedCategory (scalarReductionSource l E W)` and
  `DerivedCategory (scalarReductionTarget l E W n)`. Their rings are precisely the
  recorded completion and constant finite quotient. These are neither condensed
  categories nor modules over a discrete constant integral ring.
- Normalized coefficient-comparison datum: `(D : ComparisonData l E f)` retains
  the actual ordinary module direct images, their universal right-derived units,
  exact restriction localization factors, sectionwise identity comparisons and
  quotient coherence. This is a choice of the normalized models already supplied
  by `CompletedCoefficientPushforward.comparison`, not an arbitrary functor/map
  hypothesis. Its existence theorem is already a statement dependency. Every
  such normalized model is allowed, rather than selecting an unrelated isomorphism.
- `F` is `D.completedImage.functor`. `finiteImage` is exactly
  `(D.finiteImage n).functor`; its wrapper only supplies the datum's stored
  additivity instance. Reduction is the dependency's
  `scalarReductionDerivedExtension l E W n`.
- Restriction is `(D.source.V n).functor` or `(D.target.V n).functor`, the
  dependency's normalized termwise restriction models. `restrictionIso` is the
  fully faithful localization preimage of the two recorded factorization
  isomorphisms. `scalarAdjunction` transports the *normalized* dependency
  adjunction along that comparison, so its `unit.app` is the actual c of the node.
- Alpha is `(D.finiteSquare n).comparison.symm`. Its direction is
  `Res_Z ⋙ F ≅ F_n ⋙ Res_X`, as in the node. This comparison already carries
  composition normalization and all quotient-restriction coherence.
- Beta is now independently defined as `mateEquiv completedGeometricAdjunction
  finiteGeometricAdjunction (TwoSquare.mk ... tensorPull.hom)`. This is the
  geometric counit/tensor mate of Stacks 0B56. `geometricPull` is Mathlib's actual
  module pullback, using the existing general-universe pullback-existence theorem.
  Its ordinary adjunction is retained by `geometricOrdinaryAdjunction`.
- `geometricAdjunction_existsUnique` pins the geometric derived adjunction to the
  ordinary adjunction and `RightImage.unit`, by the explicit localized Hom equation
  on every cochain map. This uniquely fixes the geometric derived unit/counit.
- `ordinaryTensorPull` is the ordinary adjunction conjugate of
  `(D.finiteSquare n).ordinary.symm`. This ordinary square is sectionwise identity
  by D, so its conjugate is actual sheafified pullback/scalar balancing. It has no
  reference to alpha, a derived scalar unit, or the Hom equation being stated.
- `tensorPull_existsUnique` pins its derived extension by an explicit equation
  with `scalarCochainCounit` on every cochain representative. The right side is
  `ordinaryTensorPullComplex`, ordinary balancing applied degree by degree.
  The two sides are universal left-derived comparisons; K-flat computations make
  the comparison unique. Thus the chosen comparison is not arbitrary iso data.
- `hom_square` asserts invertibility and both Hom equations for this geometric
  beta. In particular the scalar-unit equation is now mathematical content,
  obtained by comparing the geometric mate with the augmented strict-tower mate.
- Derived completeness is `_hP : IsDerivedCompleteUnrestricted l E Z P`.
  This is definitionally the global `none` branch of the recorded
  `IntegralOnSlice.IsComplete`; no alternative completeness predicate is used.
  Shifts are all `m : ℤ`. The statement is evaluated at `P⟦m⟧`, so its reduction
  is reduction of the shifted object and its image is `F(P⟦m⟧)`. The canonical
  exact-functor shift identifications give precisely `P_n[m]` and `(FP)[m]` of
  the node; no special value of m is selected.
- For every `M` in the finite coefficient derived category and every
  `u : reduction.obj (P⟦m⟧) ⟶ M`, the first conjunction in `hom_square` is the
  displayed scalar-unit equation, using Lean's left-to-right `≫` convention.
  The left side is `F.map (c_Z ≫ Res_Z.map u) ≫ alpha.hom.app M`, and the right
  side is `c_X ≫ Res_X.map (beta ≫ F_n.map u)`.
- The second equality writes the same correspondence with the two actual
  `Adjunction.homEquiv`s. Since u is arbitrary and these are equivalences, it
  says exactly that h mapped to `F(h) ≫ alpha` is conjugate to u mapped to
  `beta ≫ F_n(u)`.
- Quotient legs are constructed by `quotientLeg`: transpose the lower scalar
  unit using the higher scalar adjunction after the normalized inverse
  `projectionComposition` comparison. This is precisely the adjoint form of the
  quotient-unit/successive-reduction associator, and needs no flat quotient.
  `transition` restricts this quotient-linear leg and composes restrictions.
- `transition_representation` identifies this transition with
  `representativeTransition` on *every* K-flat representative P and localization
  isomorphism e. `restrictedModelIso` consists solely of the existing universal
  derived counit computation and exact restriction localization isomorphisms;
  the central map of `representativeTransition` is the actual map of
  `canonicalIntegralReductionTower`. This theorem fixes the transition to the
  dependency's canonical one. No resolution is an extra hypothesis of the main
  Hom or transition statements.
- `imageTransition` first applies finite direct image to the source quotient
  leg, then uses `D.quotientSquare` and the target restriction-composition
  isomorphism. In particular it is constructed independently of alpha and of
  the asserted commuting square; the conclusion is not built into its definition.
- The final clause binds every derived-complete Q in `hom_square_transitions`.
  Its first conjunct is the completed-ring Hom square for every h into the
  higher restricted Q reduction. Its second conjunct is the finite-coefficient
  square for every u, where `homTransition` conjugates postcomposition with the
  actual quotient transition by the two scalar adjunction bijections. This is
  the precise finite Hom transition, rather than an inverse to scalar restriction.
  Consecutive squares cover all quotient transitions by composition.
- No full faithfulness of restriction is assumed or asserted anywhere.

### Dependency declarations read and used

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its publicly imported coefficient
  extension constructions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`, as used by the coefficient
  modules. The module source and site size conventions were inspected.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantRingOfUniverses`, `integralConstantToCompletionOfUniverses`,
  and the publicly imported completion/finite quotient sheaves.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  exactly `SheafOfModules`; `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, and its localization Q.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` and its public
  arbitrary-ring operations: the ordinary uncompleted module/derived direct
  images, realized here by the `RightImage` models stored in D.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionSource`, `scalarReductionTarget`,
  `scalarReductionDerivedExtension`, `scalarReductionDerivedRestriction`,
  `scalarReductionRestriction`, `scalarReductionCounit`, and
  `derivedScalarExtensionRestrictionAdjunction` (including its full unit
  normalization, not merely existence of an adjunction).
- `Sheaf.Paper.CompletedCoefficientPushforwardComparison`, publicly exporting
  `CompletedCoefficientPushforwardModels`: `ComparisonData`, `SiteCoefficientData`,
  `finiteSquare`, `quotientSquare`, `projectionComposition` and their normalization
  and coherence fields. All actual source/target restrictions and direct images
  come from these interfaces.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete` and its
  global branch `IsDerivedCompleteUnrestricted`.
- `Sheaf.Paper.CompletedDirectImageLimits`:
  `AdicCoefficientDatum.towerProjection`, `towerProjection_properties`,
  `towerPushReductionEvaluation`, and finite projection normalization from the
  publicly imported `CompletedTowerDirectImage`. These supply the proof route
  identifying/inverting the independently constructed geometric beta; they remain
  a plain proof import, since the actual geometric mate is constructed in this module.
- `Sheaf.Paper.IntegralReductionTowerCanonical`:
  `canonicalIntegralReductionTower` and its public K-flat computation interface.
  Remaining stated proof dependencies are imported privately by their recorded
  modules: sheaf-ring derived coefficient adjunction, successive quotient
  normalization, augmented diagram projection mate, constant-tower normalization,
  profinite coefficient inverse image, and ring-sheaf-change adjunction.

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses`:
  `SheafOfModules.module_pushforward_isRightAdjoint_of_universes`; its full
  general-site signature and proof were read. It supplies exactly the needed
  independent-universe instance, so no duplicate existence theorem is stated.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`:
  `SheafOfModules.pullback`, `pullbackPushforwardAdjunction`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `conjugateIsoEquiv`.
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`:
  `Adjunction.mapHomologicalComplex`. The normalization uses the recorded
  derived-scalar counits and exact-functor localization comparisons.

### Searches and edge cases

The persisted msearch results are in the sandbox `searches.jsonl`.
LeanFinder: “The derived direct image commutes with scalar reduction adjunction
Hom bijections and their quotient transitions”, and “Normalized derived direct
image and scalar reduction commute with the extension restriction adjunction Hom
bijection and quotient transitions”. Hits included ordinary module scalar
adjunctions and normalization of schemes; none states the completed derived square.
Loogle `CategoryTheory.Adjunction.homEquiv_apply` returned the general transpose
formula. Grep `reduction.*homEquiv|homEquiv.*reduction|pushforward.*restriction`
in Mathlib/CategoryTheory returned no matching theorem.
LeanSearch “Derived direct image preserves scalar reduction adjunction units and
Hom bijections compatibly with quotient transitions” returned derived-adjunction
unit formulas, ordinary module scalar adjunctions and sheafification adjunctions,
none with this normalized completed/finite comparison or tower coherence.
Direct rg searches of both `lean/WeilConjectures` and `lean/Sheaf`, including the
item id and `DirectImageReductionHom`, found no existing statement. Existing
`IntegralHomReduction` concerns tensor-Hom, and `SfCompleteDirectImageReduction`
provides reduction isomorphisms without the two Hom and quotient-transition
squares. `AdicRoos.quotientUnit` uses the same mate recipe in a different normalized
restriction model; the helpers here transport the actual D model rather than
creating a second scalar extension, coefficient object, or module category.

Checked exponent one (n=0 in Lean), zero P/Q/M, empty schemes, identity f, all
positive and negative shifts, and independent coefficient/site universes. None
is excluded by a hidden nonempty, boundedness, flatness or finite-cohomological-
dimension hypothesis. Quotient restrictions can be nonflat; the transition map
is obtained from an adjunction, not from a purported fully faithful restriction.
No statement dispute or correction was found.

Validation: the module and its main/transition statements passed both sandbox and
library module-mode scompile checks, with only the expected sorry warnings. The repaired geometric-mate module passed both compilation modes and the
required delivery preflight (dry-run commit e2c90c06a4e).

## Second reading by Q134

I reopened the unchanged node and the final module. I checked that alpha has the
node's direction (the inverse of `finiteSquare.comparison`), that the unit is the
normalized scalar adjunction unit after the localization transport, and that the
first equality reverses the printed composition order correctly for `≫`.
The second equality explicitly uses both Hom equivalences rather than inferring
full faithfulness of restriction. I checked every binder listed above against the
node: prime/finite field extension, both invertibility conditions, arbitrary scheme
morphism, complete P, every integer shift, every positive quotient, arbitrary M/u,
and complete Q for the transition clause. I checked the finite transition uses
`quotientSquare.inv` in the correct direction and its final codomain is
`Res_X,n F_n Q_n`. The completed square and its transposed finite square both
appear in `hom_square_transitions`.

This reading prompted adding `transition_representation`: it records explicitly
that the adjunction-defined transition agrees with the actual canonical K-flat
quotient tower. The K-flat representative is bound only in that normalization
assertion, not imposed on objects in either main statement. The three main postponed
theorems and the geometric construction helpers have complete proof docstrings. This is
a worker self-check; independent review remains with the maintainer as dispatched.


## Returned H3/H4 repaired

The immutable returned head e1369e672a59 defined beta by the scalar adjunct of
F(c_Z) followed by alpha. The saved packet initially passed the prescribed dry
run (3fea58a2dfc), but this did not repair the mathematical defect. Beta has now
been replaced by an independent geometric mate. Its definition does not contain
alpha, scalarAdjunction, or the direct image of a scalar unit. The old claim that
the scalar-mate definition by itself specified the geometric projection has been
removed. The two Hom equations and both transition equations now use this beta.

The comparison needed for that mate is fixed at the ordinary level: the same
coefficient ring square with sectionwise identity direct images has its unique
ordinary pullback/scalar balancing conjugate. Its derived version is fixed by
its universal-counit equation on every cochain representative. The derived
geometric adjunction is separately fixed by its localized ordinary Hom formula.
Consequently no desired Hom identity has been used as a definition or hypothesis.
The geometric counit/tensor characterization agrees word for word with Stacks
sites-cohomology.tex, equation-projection-formula-map, read in this repair.

Additional searches in this repair: rg over lean/WeilConjectures and lean/Sheaf
for the item id and helper names found no duplicate. Searches for independent
pullback interfaces found PullbackExistsOfUniverses, which is reused, and
IntegralAmbientOperationModels, which uses that same theorem. SfCompleteDirectImageReduction
and ProEtaleRingSheafChangeAdjunction expose only equal-universe geometric APIs;
the present helpers retain t and u independent. Loogle query
`CategoryTheory.mateEquiv, CategoryTheory.conjugateIsoEquiv,
SheafOfModules.pullbackPushforwardAdjunction` returned zero hits. LeanFinder query
“Geometric derived adjunction mate of pullback tensor balancing for reduction
from completed coefficient rings to finite coefficients, on normalized direct
image models” returned eight scheme tensor-pullback hits, none this statement.

### Repair self-check

I reread the node and the repaired file. Prime, finite coefficient extension,
both invertibility assumptions, independent universes, arbitrary f, complete P,
all shifts, all positive exponents, arbitrary M/u, and complete Q still have the
same binders. Alpha and all quotient transition constructions are unchanged.
Beta is now the independent geometric projection mate required in the node.
The normalization clauses specify the actual adjunctions and balancing maps;
there is no new mathematical hypothesis. For f=id the normalized geometric
adjunctions and balancing give the usual reduction identity. Zero objects,
empty schemes, exponent one and nonflat quotient transitions remain allowed.
All helper theorem proofs remain sorry; their docstrings describe the necessary
normalization and computation proofs. This is the dispatched worker's self-check;
the maintainer supplies the independent review.
