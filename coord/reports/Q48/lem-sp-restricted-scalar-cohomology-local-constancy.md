## Worker report

The module `Sheaf.Paper.RestrictedScalarCohomologyLocalConstancy` states
`AlgebraicGeometry.Scheme.restrictedScalarCohomology_finiteLocalModels` with `sorry`.
It retains the B-action on the output rather than merely asserting local constancy
of its underlying A-module or set sheaf. The item's mathematical statement is unchanged.

Hypothesis and conclusion correspondence:

- Schemes and their arbitrary morphism: `{T X : Scheme.{u}} (a : X ⟶ T)`.
- Finite commutative rings and a unital homomorphism:
  `{A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (f : A →+* B)`.
  There is no algebra structure, flatness, nonzero-ring, or characteristic binder.
- Small pro-etale sites: `ProEt.topology T` and `ProEt.topology X` in every
  coefficient, pullback, stalk and local-model construction. Objects remain in
  `Type (u+1)` and morphisms in `Type u`; the site is not made a SmallCategory at u.
  Finite coefficient rings live in the chosen bound u and are lifted to u+1.
- The constant ring sheaves are `proEtaleConstantRing T A` and its X/B variants:
  the existing constant CommRingCat sheaf on `ULift A`, with commutativity forgotten
  by `proEtaleRingModules`. No alternate ring or module-sheaf category is defined.
- Ordinary derived categories: `DerivedCategory (proEtaleRingModules T ...)`,
  with independently chosen localization sizes `wA` and `wB`. The explicit
  `HasDerivedCategory` binders are localization choices, not boundedness assumptions.
- The object is exactly `(K : DerivedCategory ...)`. Its sole bound is `hKb`,
  `∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((DerivedCategory.homologyFunctor ... j).obj K)`.
- For EVERY integer j, `hK` asserts
  `IsLocallyConstantProEtaleModuleSheafOfUniverses.{u,u} X A` of
  `proEtaleConstantModulePullback a A ((homologyFunctor ... j).obj K)`.
  The conjunction's second clause quantifies over every algebraically closed field
  Ω in the chosen bound and every `x : Spec (.of Ω) ⟶ X`, and asserts `Finite`
  of its `proEtaleGeometricModuleStalk`. The zero degrees are included.
- The exact pullback is the dependency's actual `proEtaleConstantModulePullback`,
  inverse image followed by sheafified tensor along the canonical coefficient map.
  The imported coefficient-comparison theorem gives its usual exactness.
- K_B is the object of `constantCoefficientScalarExtensionOfUniverses` applied to K.
  The map passed to it is f conjugated by the ULift ring equivalences, hence precisely
  the induced constant coefficient map. This is the left-derived sheafified extension,
  with its ordinary right-factor B-action, computed by the existing K-flat counit.
- The conclusion takes an arbitrary `(q : ℤ)` and asserts
  `IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses.{u,u} X B
  (fun M ↦ Finite M)` of the B-pullback of H^q(K_B).
  Expanding this existing definition gives an index type I, objects U of X.ProEt,
  arrows to `ProEt.mk (𝟙 X)`, `Presieve.ofArrows U f` in `ProEt.precoverage X`,
  and for each i a module `M : ModuleCat.{u+1} (ULift.{u+1,u} B)`, `Finite M`,
  and `Nonempty (F.over (U i) ≅ proEtaleConstantModuleSheafOverOfUniverses X B (U i) M)`.
  Thus it is exactly a pro-etale cover and finite B-module models, with B-linear
  isomorphisms over the restricted B_X ring on localized sites. The ULift ring
  equivalence identifies these with B-modules without changing their elements.
- The cover existential is inside the assertion for each q. There is no common-cover,
  lower-bound, stratification, Tor-amplitude, flatness, or prime-invertibility hypothesis.

Dependency declarations used, with the recorded declaration inspected in its source:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `ProEt.topology`, `ProEt.precoverage`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `proEtaleConstantRing`, `proEtaleConstantModulePullback` (and the inverse-image
  construction reexported by the recorded `proEtaleSheafInverseImage`).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors` (the dependency's
  existing `mathlib_match`; its specialized Lean record is preserved).
- `Sheaf.CategoryTheory.ConstantCoefficientScalarExtension` preserves and imports
  NK's original six-declaration interface. The helper
  `SheafOfModules.constantCoefficientScalarExtensionOfUniverses` now belongs to
  the item module itself; it exposes the existing universal cochain model with
  independent site and localization universes.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  `AlgebraicGeometry.ProEtale.derivedTensor`, the recorded K-flat tensor construction
  in the fixed-ring presentation, retained as a proof-plan import. The conclusion
  directly uses derived extension, which retains the target-ring action.
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`:
  `IsLocallyConstantProEtaleModuleSheafOfUniverses`,
  `IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses`,
  `proEtaleConstantModuleSheafOverOfUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor` reexports
  `proEtaleGeometricModuleStalk` from `ProEtaleGeometricStalk`; the recorded
  `geometricRingModuleStalkFunctor` is the same construction on objects and maps.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `SheafOfModules.over` as used by the local-model predicate.

All available proof dependencies are imported privately; the theorem docstring gives
the node's six proof steps and their named inputs, including the underlying-sheaf
comparison, empty-member case, and finite B-action refinement.

Edge cases checked from the mathematical statement and the definitions: empty X and
empty covering members (zero models); zero coefficient rings and zero modules; K=0;
identity and nonflat coefficient maps (e.g. Z/4 to Z/2); arbitrarily negative q and
bounded-above complexes with no lower bound; an arbitrary scheme morphism a; no
prime or invertibility condition. These cases require no change to the statement.
A finite model means `Finite M`, not finite rank or merely finite generation.

Searches actually run:

- `msearch.py ... leansearch "Derived change of finite coefficients preserves finite
  locally constant cohomology on a pro etale scheme after pullback"`: eight hits
  concerning locally constant functions, condensed constant functors and etale
  base change, with no matching derived-coefficient theorem.

- `msearch.py ... leanfinder "For finite rings A to B derived scalar extension of a
  bounded above complex whose pullback cohomology is finite locally constant has
  finite locally constant B module cohomology"`: eight results about constant
  condensed module functors; none states this scheme/pro-etale/derived assertion.
- `msearch.py ... loogle "SheafOfModules, DerivedCategory"`: zero results.
- `msearch.py ... grep "derived.*[Tt]ensor|[Ll]ocally[Cc]onstant"
  Algebra/Category/ModuleCat`: zero results.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `restrictedScalar|restricted_scalar|scalar.*localConst|scalar.*LocallyConstant`:
  unrelated affine-module restricted-scalar cone lemmas, no matching theorem.
- `grep -rn "lem-sp-restricted-scalar-cohomology-local-constancy"
  lean/WeilConjectures`: no result.
- Broader project searches for constantCoefficientScalarExtension,
  restricted tensor/local-constant cohomology, and finite geometric stalks found
  the dependencies used above, not a theorem with this target B-module conclusion.
- The two proposed declaration names were checked against both project roots and
  `dag/lean_names_upstream.json`; no existing declarations had those names.

Source read: Stacks `sites-cohomology.tex`, lemma-locally-constant-tensor-product
(Tag 094H), and `sites-modules.tex`, lemma-morphism-locally-constant (Tag 093S).
Also read the current blueprint unit sk-def-sp-scalar-extension. The node is its
auxiliary restricted-cohomology lemma, not the unit's own scalar-extension statement.
No mathematical fault or STATEMENT-DISPUTED issue was found.

## Returned-review repairs

The independent review of immutable head `b6fbd77f9cd8` accepted the mathematical
statement and returned two dependency-ownership faults (H13).

F1: Moved `SheafOfModules.constantCoefficientScalarExtensionOfUniverses` into
`Sheaf.Paper.RestrictedScalarCohomologyLocalConstancy`, as the reviewer explicitly
permitted. Its source/blueprint docstring now names the item, and the item's
`lean.declarations` lists both the helper and the theorem. Removed the separate
`ConstantCoefficientScalarExtensionOfUniverses.lean` module and the sandbox copy
of `def-weil-pbc-constant-coefficient-scalar-extension.json`. The NK module and
its six-declaration record remain owned and untouched. Its same-universe API
cannot handle the small pro-etale site's object universe u+1 and Hom universe u;
the helper retains those universes independently and selects the `.T` field of
the existing `DerivedChangeOfRingsCochainModel` for the constant-ring map.
The model prescribes ordinary sheafified scalar extension, its universal counit,
and the computation on K-flat representatives, so the functor is determined up to
the required canonical isomorphism. Its data contains no sorry.

F2: Removed the sandbox copy of `def-weil-derived-cohomology-sheaves.json`.
The N5 `SfCommonStageWeilCohomology` record with its twelve declarations remains
untouched. Added the requested `lean.note` to the item explaining direct use of
the dependency's exact existing Mathlib match, `DerivedCategory.homologyFunctor`,
and its cochain comparison `homologyFunctorFactors`. The specialized
`sfModelCohomology` applies to common-stage Weil objects and cannot take this K
in an ordinary derived category. This delivery changes no dependency record.

Compared the saved packet with the returned-head description and current live
records: the saved packet still replaced NK's six-declaration record and N5's
twelve-declaration record, although its initial dry run passed. Those replacements
are removed rather than restored with another binding. The theorem's signature,
node statement, hypotheses, conclusion, statement dependencies and proof plan
are unchanged. The final packet has one module, the item's node, and this report.

## Second reading by Q48

I reread the node and the final combined module in a separate pass. This is a worker
self-check, not a claim that a second agent reviewed it; the dispatch explicitly
forbids starting agents and the maintainer supplies the independent review.

Checked separately the arbitrary morphism, both finite rings, the actual unital map,
ordinary derived K, upper cohomology bound, all integer input degrees, both halves
of the local-constancy/finite-geometric-stalk conjunction, output degree q, target
coefficient action, localized module isomorphism, finiteness of the model's elements,
and degree-dependent covering quantifiers. The input bound is on T, not only after
pullback. The conclusion remains B-linear, including for nonflat B over A.

The first compile found a missing public import for `proEtaleRingModules`; that was
added. Subsequent elaboration exposed imported max-universe instance registrations
leaving auxiliary universes undetermined. Explicit universe arguments and selection
of the existing fixed-size site instances resolve this without an additional
hypothesis or a changed site. The helper in the item module keeps independent
site Hom and object sizes and independent derived localization sizes. No definition contains
sorry; the only new theorem is the item, whose proof is exactly `by sorry`.

Repair self-check: opened the final item module, the saved and live node records,
the original NK module, the existing cochain-model signature, and Mathlib's
homology-functor definition and comparison. The helper's definition is unchanged
apart from moving into the item's module and making `noncomputable` explicit.
The first repair compile exposed changed universe-parameter order after the move;
the explicit universe declaration order was restored before recompiling.
Every variable and universe is explicitly bound. The only postponed theorem
remains `restrictedScalarCohomology_finiteLocalModels`, with its full proof
plan in the docstring. Neither F1 nor F2 requires a mathematical statement change.
The existing edge-case and hypothesis/clause check above still applies verbatim.

Validation: the saved packet initially passed deliver2.py --no-push at
`a11224e9972`, but was then repaired to address both independent-review findings.
The final single-module packet compiled cleanly with scompile.py (sandbox 20.1 s,
module 16.1 s). It is checked again by deliver2.py --no-push before pushing. Scoped instance-selection attributes
remain restricted to elaboration of the theorem.
