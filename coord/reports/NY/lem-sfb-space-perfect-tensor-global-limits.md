## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePerfectTensorGlobalLimits` states
`AlgebraicGeometry.AlgebraicSpace.perfectTensorGlobal_preserves_products_limits`.
Its sole proof is `sorry`. No definition, axiom, private notation, local instance,
chosen cone, or replacement tensor/global-sections functor is introduced.
The node's mathematical statement, proof and source are unchanged. The statement
was checked against `literature/stacks-project/spaces-flat.tex`, lines 2188–2237,
Tag 0CX6: the exact global Hom/product/derived-limit assertion and its final
translation by perfect duality. The formal statement intentionally concerns that
general functor assertion, not the infinitesimal perfectness conclusion.

Hypothesis and clause correspondence:

- Size convention: explicit `universe u w`; `A : Type u`, algebraic spaces over
  `Spec (.of (ULift.{u} ℤ))`, and `[HasDerivedCategory.{w} X.SmallModules]`.
  The existing small model has both objects and arrows in u and the unchanged
  module section universe u. The localization Hom universe w remains independent.
  Product families use `I : Type u`; no finite/nonempty/countability condition
  is imposed on the product assertion.
- A commutative ring: `(A : Type u) [CommRing A]`, allowing the zero ring and
  every characteristic.
- The map to Spec A: `Y : Over (Spec (.of (ULift.{u} ℤ)))`,
  `e : Y.left ≅ Spec (.of A)`, `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`,
  and `f : X ⟶ schemeSpace Y`. This is the standard existing affine-target
  presentation required by `affineDerivedSections`. It does not assume any
  property of A or an extra morphism: take Y to be Spec A with its unique map to
  Spec Z and e the identity. Allowing all isomorphic presentations includes the
  literal Spec A case. ULift only places the integer base in universe u.
- Quasi-compactness: `_hqc : IsQuasiCompactPresheafMap f.hom.hom`, the recorded
  affine-test etale atlas predicate. Its equivalence to quasi-compactness on all
  quasi-compact scheme tests is `quasiCompact_iff_quasiCompact_scheme_tests`.
  This is the existing encoding of the geometric quasi-compact hypothesis,
  not an assumption that f is representable.
- Quasi-separatedness: the same predicate on `pullback.diagonal f.hom.hom`.
  This is the actual relative diagonal; absolute separation, finite type,
  properness and nonemptiness are not assumed.
- Small etale structure sheaf and its modules: `X.smallStructureSheaf` and
  `X.SmallModules`, with the recorded `smallModuleEquivalence` to the original
  `X.Modules`. These use actual chart regular functions, not a freely chosen
  ringed site or a changed coefficient universe.
- Unbounded derived category and C_X: `X.DerivedModules` and `X.DerivedQCoh`.
  The latter is the full subcategory for `derivedQCohProperty`, which tests every
  integer cohomology object after the actual inverse small-model equivalence.
  It is not `DerivedCategory X.QCoh`. Its shifts and distinguished triangles are
  the inherited ones supplied by `qcohDerivedTriangulation`.
- Perfect E in C_X: `E : X.DerivedQCoh` and
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
  X.smallStructureSheaf E.obj`. The recorded definition requires local bounded
  finite-free retract models, with ranks and bounds allowed to vary by chart.
- The precise functor and its action in E: T has type
  `X.DerivedQCoh ⥤ X.DerivedQCoh ⥤ DerivedCategory (ModuleCat.{u} A)` and `_hT`
  equates it to the curry/flip of the composite of the two full inclusions,
  `X.derivedDualityModel.closed.tensor`, and `affineDerivedSections A Y e X f`.
  Thus `(T.obj E).obj H` is exactly RΓ(X,H tensor^L E), and `(T.map v).app H`
  is exactly RΓ(1_H tensor^L v). The equality constrains the entire functor,
  including maps, rather than supplying an arbitrary functor with only desired
  properties. Substituting `_hT` gives the node's stated functor without any
  additional mathematical hypothesis. This equation avoids a second definition
  and an import cycle through the downstream tensor-test theorem.
- K-flat tensor and K-injective sections: the tensor is the already normalized
  derived closed model, and `affineDerivedSections` is literally
  `affineScalarSections.rightDerivedFunctor`. The latter is Hom(O,-) with
  restriction of scalars along `affineGlobalScalar`, preserving the A-action
  from f. No abelian-group forgetful functor replaces it.
- Exactness: `(T.obj E).Additive` and the existential `σ : (T.obj E).CommShift ℤ`,
  together with preservation of every distinguished triangle with last arrow
  `map Δ.mor₃ ≫ (σ.commShiftIso 1).hom.app Δ.obj₁`. `CommShift` includes the
  zero and addition coherences for all integer shifts, not just an unrelated
  degree-one object isomorphism.
- All products and the specified comparison: for every I and H the conclusion
  gives `HasProduct H` and `HasProduct (fun j ↦ (T.obj E).obj (H j))`.
  For arbitrary limiting fans P and Q, every c satisfying
  `c ≫ Q.proj j = (T.obj E).map (P.proj j)` is an isomorphism. Since Q is a
  limiting fan, those equations specify exactly one c and it exists by the
  universal property. This is precisely the canonical comparison of the node;
  no unconstrained map, chosen substitute, or ambient-product hypothesis appears.
- Naturality in H_j: the next conjunct quantifies over arbitrary family maps v,
  source and target product fans, and their component-characterized comparisons.
  The equality is `F_E(product v) ≫ c' = c ≫ product(F_E(v))`; the two product
  maps are actual `IsLimit.lift (Fan.mk ...)` constructions.
- Naturality in perfect E: the next conjunct quantifies over perfect E' and
  `v : E ⟶ E'`. The equality uses `T.map v` on the product vertex and the
  product lift of `(T.map v).app (H j)`. Because `_hT` fixes the entire curried
  tensor/sections functor, this is the stated tensor-induced transformation,
  not an arbitrary natural transformation with a stipulated behavior.
- Every countable tower: `H : ℕ → X.DerivedQCoh` and `t : ∀ n, H (n+1) ⟶ H n`.
  Index n in Lean denotes level n+1 of the source. P is an arbitrary product fan.
  The binder named s is the source's entire `1-s` endomorphism, characterized by
  `s ≫ P.proj n = P.proj n - P.proj (n+1) ≫ t n`. Likewise s' is `1-s'`
  on the image tower. This is only a binder-name convention; the actual signs,
  transition direction and projection equations agree with the node.
- Given product triangle: L, p and δ are arbitrary with
  `Triangle.mk p s δ ∈ distTriang X.DerivedQCoh`.
  This is `IsDerivedLimitTriangle` expanded for an arbitrary specified product
  fan rather than Mathlib's selected product; it is the same property.
- Image triangle is a derived limit: the conclusion supplies an isomorphism c
  satisfying all product-comparison components. The triangle has arrows
  `F_E(p) ≫ c.hom`, s', and
  `c.inv ≫ F_E(δ) ≫ (σ.commShiftIso 1).hom.app L` and is distinguished.
  Both product vertices therefore use exactly the same comparison, and the
  connecting morphism uses that same coherent shift comparison.
- Every other derived limit: for all R, p' and δ' with their stated Roos
  triangle distinguished, there exists `φ : (T.obj E).obj L ≅ R` satisfying
  `φ.hom ≫ p' = F_E(p) ≫ c.hom`. Composing with any Q.proj n and using the
  equations on c gives `φ.hom ≫ p' ≫ Q.proj n = F_E(p ≫ P.proj n)`, precisely
  the projection clause with q_n. No uniqueness/canonicity of φ is asserted.
- No tower surjectivity, module concentration, finite presentation, proper
  support or nilpotent-ring-tower condition occurs in any binder.

Recorded dependency declarations used (namespace AlgebraicGeometry.AlgebraicSpace
unless otherwise indicated):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf`, `Modules`, and the actual natural-transformation morphisms.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent alias to Mathlib's `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the
  unchanged Mathlib predicate `SheafOfModules.IsQuasicoherent`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses` and its local strict-perfect
  definition; read its complete definition including the variable-binder context.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`, retaining the
  canonical K-injective interpretation of sections; the scalar version used
  in the statement is the separately recorded `affineDerivedSections`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimit`, `CategoryTheory.IsDerivedLimitTriangle`;
  expanded into the corresponding distinguished Roos triangle to allow arbitrary
  product fans, exactly as the existing downstream tensor-test statement does.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, the existing acyclic-test
  predicate underlying the normalized tensor model, not a second tensor.
- Added already-landed statement dependencies:
  `def-sfb-space-small-ringed-model` (`smallModuleEquivalence`, `SmallModules`,
  `smallStructureSheaf`); `def-sfb-space-derived-module-calculus`
  (`DerivedModules`, `derivedQCohProperty`, `DerivedQCoh`, `derivedDualityModel`);
  `def-sfb-space-qcoh-derived-triangulation` (`qcohDerivedTriangulation`);
  `def-sfb-space-affine-global-sections` (`affineScalarSections`,
  `affineGlobalScalar`, `affineDerivedSections`);
  `def-sfb-space-quasi-compact-presheaf-map`
  (`IsQuasiCompactPresheafMap`, in Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal).
  These are additions to stmt_deps only; no other node is changed.

The imports include every currently stated proof dependency, including the Mathlib
`DerivedCategory.isIso_iff` and triangulated-category modules. The three proof nodes
`lem-sfb-space-qcqs-source-products`, `lem-sfb-space-qcoh-kernels-colimits`, and
`lem-sfb-ringed-site-global-rhom-derived-limits` have no recorded declaration in
the read clone and are not restated: their notions are not needed to type this
statement. Their proof steps remain in its complete nine-step proof docstring.

Edge cases checked before finalizing:

- Empty product family: the fan equations have no components but Q being limiting
  still determines c uniquely; exactness/product preservation sends the zero
  product to zero. Naturality still makes sense.
- Zero E or zero objects in H: perfect zero and arbitrary zero derived objects
  are permitted, without any nonzero hypothesis or a boundedness condition on H.
- Empty X and the zero ring: both are valid objects of the existing framework;
  the statement has no points, charts, nonempty-index or nontrivial-ring binder.
- Constant towers, zero transitions, and arbitrary non-surjective transitions:
  the coordinate difference formula still applies, with no Mittag-Leffler
  hypothesis. The countable indexing starts with Lean n=0/source level 1.
- Unbounded complexes and independently chosen localization universe w: neither
  gets truncated, equated to u, or replaced by module concentration.
- Arbitrary choices of source/target products and of R: all limiting fans and
  all derived-limit triangles are quantified; only existence of a compatible
  isomorphism is asserted.

Searches made for existing declarations:

- `msearch.py NY <item> leanfinder "Perfect tensor derived global sections on quasi
  compact quasi separated algebraic spaces preserves products and derived inverse
  limits"`: 8 results concerning scheme-valued limit diagrams and ordinary Γ;
  none gives this derived quasi-coherent functor statement.
- `msearch.py ... loogle "PreservesLimitsOfShape, Discrete"`: 0 results, diagnostic
  `unknown identifier 'PreservesLimitsOfShape'`; this external query failure was
  not treated as evidence of absence on its own.
- `msearch.py ... leansearch "Derived tensor with a perfect complex followed by
  global sections preserves products and homotopy limits"`: 8 results, including
  ordinary flat tensor finite-limit preservation, homological finite products,
  and affine scheme Γ; no matching statement.
- `msearch.py ... grep "preserves.*[Pp]roduct|[Pp]roduct.*[Tt]ensor" CategoryTheory`:
  25 hits about finite products, localizations and generic monoidal operations;
  no exact theorem for this derived functor.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for perfectTensor, PerfectTensor,
  tensor/global combinations, DQCoh, globalSections, and the exact item id:
  no upstream theorem for this item. The related module
  `Sheaf.AlgebraicGeometry.SpacePerfectTensorTestHolim` has
  `perfectTensorTest`, `perfectTensorTestProductComparison`, and
  `perfectTensorTest_preserves_products_holim`. Its proof explicitly cites this
  item. Its theorem uses absolute qcqs assumptions and states a related test,
  without the two explicit naturality clauses and the transported image-triangle
  clause required here. Importing it would invert the intended dependency.
  Instead this statement uses the underlying recorded constructions directly,
  introducing no duplicate functor definition or product-comparison definition.
- Read the recorded node statements, full signatures and docstrings of all
  statement dependencies, including Mathlib matches and the new already-landed
  definition dependencies. The prescribed CompactObject example module is now a
  withdrawn declaration-free module; its node's current binding was also read.

Validation: scompile.py compiled this sole delivered file in both sandbox and
library module modes on the server, with no errors or warnings (3.5 s and 3.2 s
on the first pass). After the final import-only cleanup, deliver2.py --no-push
compiled both modes again and returned OK: the preflight and per-file compilation
both passed. No STATEMENT-DISPUTED issue or statement correction.

## Second reading by NY

A separate reading pass compared the complete node and source with the final
Lean signature. It checked the order of currying and flip: E is the second tensor
argument and H the first. It checked that equality `_hT` fixes morphisms in E as
well as H; using only an equality of object values would have lost the required
naturality. It checked that products live in the intrinsic full subcategory and
that their existence is a conclusion. It checked all three arrows of the transported
triangle, in particular the inverse comparison on its final product vertex, and
that the final equality implies the projection identities with the correct Lean
composition order. It checked that s and s' denote the difference endomorphisms,
not the shifts alone, and that the shift structure is coherent over all ℤ.
No mathematical mismatch was found. An import used only for the proof was changed
from public to plain, with the owning predicate module made public instead.
This is a second pass by the assigned worker, not a claim of an independent agent
review: the dispatcher's instructions forbid starting other agents. The delivery
is left for the maintainer's independent review as required by the assignment.
