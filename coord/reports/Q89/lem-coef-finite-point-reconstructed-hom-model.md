## Worker report

The module `Sheaf.Paper.FinitePointReconstructedHomModel` states
`WeilConjectures.FinitePointHom.finite_point_reconstructed_hom_model`.
It imports the dependency declarations rather than redefining their categories,
coefficient rings, tensor, Hom complexes, constructibility, or cohomology finiteness.
Every theorem proof in this delivery is `sorry`; definitions have actual data.

Clause-by-clause correspondence:

- The global datum is `D : FiniteFieldDatum.{u}`. The prime is `l` with
  `[Fact l.Prime]`, `_hl : l ≠ D.p`; `E` has Field, Algebra (Padic l), and
  FiniteDimensional instances. `n : ℕ` and `hn : 1 ≤ n` retain the positive exponent.
  `A l E n` is ULift of the recorded `Padic.coefficientExtensionRing l E n`.
  `B D l E n` is precisely its constant ring sheaf on `ProEt.topology (Spec (.of D.k))`.
  The valuation ring and uniformizer are the choices already inside that quotient.
- The existential `L` has the exact `PointDerivedHom.extensionObject` objects and
  `extensionMorphism` maps; `hobj` and the map equality forbid an arbitrary functor.
  The multiplication natural isomorphism identifies L with `constantModules` and its
  equation sends every `b tensor x` generator to `b` times the sheafified constant x.
- `G` is the existing `PointDerivedHom.sections`, final-object evaluation followed
  by scalar restriction along the actual constant-section map. Exactness of L and G
  is asserted by PreservesFiniteLimits and PreservesFiniteColimits, on all modules.
  Bijectivity of `PointDerivedHom.scalar` at `finalObject D.k` is Gamma B = A,
  normalized by a maps to a times 1. Its source and target have their actual ring data.
- The existential adjunction is supplied as a conclusion.
  `PointDerivedHom.ExplicitAdjunction` states both h maps to h_s(1 tensor m) and
  the inverse formula b tensor m maps to b times t(m) restricted to U.
  The subsequent universal exactness/additivity instance binders expose the already
  asserted facts to `mapDerivedCategory`; they add no mathematical hypotheses.
- `Reconstruction` quantifies every C with `intrinsicFiniteTorsionConstructible`.
  It asserts `pointFiniteCohomology A (G.mapDerivedCategory.obj C)`, invertibility
  of the actual `adj.mapDerivedCategoryAdjunction.counit.app C`, and the triangle
  equality `unit ≫ G.map counit = identity` on c = Gamma C.
- `Comparison` quantifies all bounded finite-cohomology ordinary source objects and
  all ambient V in the unbounded derived category of B-module sheaves. No
  constructibility, finiteness, boundedness, or flatness condition is imposed on V.
  For all complexes V and K-injective J and every quasi-isomorphism V to J, it
  asserts K-injectivity of Gamma J and the sections quasi-isomorphism.
- The P quantifier ranges over every representative with bounded finite cohomology.
  Its K-flat condition is the definition: tensor with every acyclic F is acyclic;
  every P.X i is flat. This is the ordinary-module specialization of the recorded
  K-flat notion, also rendered by `PointDerivedHom.Statement`. It does not require
  P bounded termwise or its terms finite or projective.
- `qPJ` is an actual chain isomorphism from sections of `sheafHom (LP) J` to
  `CochainComplex.moduleHomComplex P (Gamma J)`. `ChainComparison` fixes each
  degree j, product component p, cochain h and element x to h(1 tensor x).
  The imported sheaf Hom and ordinary Hom definitions both have precisely
  differential d_J h - (-1)^j h d_P, so a chain isomorphism retains this sign.
- `sourceModelMap` uses the actual `IntegralHom.homModelMap`, exact-sections
  factorization, and the exact-extension factorization. `targetModelMap` uses the
  transpose of ordinary signed evaluation and exact-sections factorization.
  Both model maps are asserted invertible for the specified representatives.
  The equality `sourceModelMap ≫ q.hom = Q.map qPJ.hom ≫ targetModelMap`
  fixes q to the localized chain comparison; it is not an arbitrary isomorphism.
- `QNatural` is the contravariant/covariant naturality square for arbitrary derived
  f and g. The `∃! q` states independence of resolving representatives explicitly.
  `ReconstructedComparison` supplies Q for every constructible C and ambient V,
  forces its hom to be `G.map (RHom.map (counit.op, identity)) ≫ q.hom`, and
  states its naturality for every derived f and g, exactly the displayed composite.

Helpers and deferred obligations: `ordinaryEvaluation_existsUnique` is the unique
ordinary signed tensor-evaluation chain map; the following definition chooses only
from this uniqueness theorem. The elementary evaluation construction and proof are
spelled out in its docstring. It belongs to this node's ordinary Hom resolution model,
not a new independent notion. `ordinaryModelMap` is its actual localized transpose.
The other helpers are abbreviations, existing-instance specializations, or explicit
predicates assembling the clauses above. All declarations are listed in lean.declarations.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its original public
  imports: `Padic.coefficientExtensionRing`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, and `finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`;
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, `constantSheafAdj`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, with the existing changeOfRings tensor.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `HasDerivedCategory.standard`; exact termwise descent is
  `Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible` (the exact recorded predicate).
- `Sheaf.Paper.PointFiniteCohomologyComplexes`: `DerivedCategory.pointFiniteCohomology`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, and its public generic
  `derivedInternalHomOfUniverses` with the actual K-injective localization.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: the recorded K-flat
  interface, retaining ordinary-module specialization through kFlat; the equivalent
  acyclic-total-tensor condition is written in the representative assertion.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`.
- `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex` and
  `homComplexFunctor`; the selected PointDerivedHom.sheafHom is this construction.
- `Sheaf.Paper.PointDerivedHomModels`: all extension/sections/generator/scalar
  constructions, `ExplicitAdjunction`, and the same `moduleTotal` tensor.
- `WeilConjectures.Algebra.Homology.ModuleHomComplex`:
  `CochainComplex.moduleHomComplex`, reusing Mathlib linear homogeneous cochains.
- `Sheaf.Paper.IntegralHomReductionModels`: `IntegralHom.homModelMap` is the actual
  localization comparison, used with the finite constant coefficient sheaf.
- `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`:
  `Adjunction.mapDerivedCategoryAdjunction`, with its actual unit and counit.

All stated proof-dependency modules are imported, including Mathlib matches for
exact derived factorization, K-injective Hom-to-derived bijectivity, localization,
module sheafification, and finite valuation-ring quotients. Existing source helpers
are cited by adding their three already landed owning definition nodes to stmt_deps.
No dependency node is changed and no independent new definition node is needed.

Edge cases checked: n=1 remains allowed; n=0 is excluded exactly as in the node.
The zero source, zero target, acyclic representatives, and arbitrary shifts are
allowed. No finite product replaces the infinite product of Hom cochains. The
ordinary evaluation uses (-1)^(p*j) when the P argument comes first, whereas both
Hom differentials use (-1)^j; these are compatible by the tensor differential.
The source may have unbounded flat terms, and V and J may be unbounded in both
cohomological directions. No perfectness, finite Tor dimension or finite source
terms are assumed. The small site has object universe u+1 and morphism universe u;
ULift places coefficients and module elements in u+1, with no equality of site
object and morphism universes. Ordinary modules use the existing small Grothendieck
localization; sheaf modules use the existing standard localization, exactly as
intrinsicFiniteTorsionConstructible does. These are fixed canonical API choices,
not new data or assumptions.

Searches:

1. msearch.py leanfinder: `exact constant module sheaf sections adjunction derived
   internal Hom algebraically closed point arbitrary target` returned unitHomEquiv,
   constantSheafAdj, Gamma Hom equivalences and condensed-module adjunctions; none
   states this finite-point reconstruction with arbitrary ambient target.
2. msearch.py loogle: `CategoryTheory.constantSheafAdj, CategoryTheory.homComplex,
   CategoryTheory.Adjunction` returned zero hits (homComplex is project, not Mathlib).
3. msearch.py grep: `point.*[Hh]om|constantSheafAdj` in CategoryTheory returned the
   constant-sheaf adjunction and generic pointed-category matches, no target result.
4. rg on lean/WeilConjectures and lean/Sheaf for reconstructed/point Hom/adjunction
   found PointDerivedHomModels, PointHomComplexAdjunction, PointDerivedHomEvaluation
   and PointSectionsReconstruction. Their interfaces were read in full where used:
   the existing derived comparison only targets the coefficient unit's resolution;
   it does not give the present arbitrary-V comparison or reconstructed composite.
   ExactExtensionSections provides the adjunction clause but does not state the rest.
5. rg for the item's id in lean/WeilConjectures and dag/lean_names_upstream.json:
   no existing matching declaration. Searches of the published ordinary Hom/module
   evaluation files found moduleHomComplex and precomposition helpers but no
   ordinary evaluation with the required full signed normalization; only that helper
   is supplied here. No duplicate construction of Hom or tensor was introduced.

Validation: scompile.py compiled both its sandbox and final-module forms cleanly
within the required per-file 60 seconds. Only the prescribed wrapper was used.
No statement correction and no STATEMENT-DISPUTED issue were needed.

## Second reading by Q89

This is the worker's additional self-check; no second agent was started, as the
explicit dispatcher brief forbids that. The maintainer supplies the independent
review promised in the task. I reread the actual node and module together.

The rereading found and repaired three concrete omissions: multiplication was
initially only an unspecified natural isomorphism (now normalized on every b tensor x);
the two representative maps were initially only present in a commuting square
(now explicitly asserted invertible); and q initially lacked an explicit uniqueness
assertion (now existential uniqueness, with arbitrary-derived naturality). I checked
that the final counit formula has the contravariant direction RHom(C,V) to
RHom(L Gamma C,V), and that the triangle composite is unit then Gamma(counit).
I also checked every ambient V binder for added restrictions: none has any.
The hypothesis/clause table above gives the full matching used in this reading.
