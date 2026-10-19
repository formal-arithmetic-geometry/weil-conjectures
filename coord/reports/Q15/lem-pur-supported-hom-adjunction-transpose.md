## Worker report

Delivered module: `Sheaf.Paper.SupportedHomAdjunctionTranspose`.
Main declaration: `AlgebraicGeometry.ProEtale.supportedHom_adjunction_transpose`.
It states the supported-Hom / derived-adjunction comparison, with the evaluation
normalization specified on injective cocycles. Its single postponed proof is the
main theorem. All eight supporting declarations have real bodies and source / blueprint
docstrings. No node statement or dependency binding is changed; no new nodes are needed.

The existentially bound natural isomorphism is constrained by its actual cocycle
normalization, rather than chosen from `supported_cohomology_hom`'s bare `Nonempty`.
This is a direct way to state that the canonical normalized isomorphism satisfies
the asserted equality. The last clause quantifies over every representing derived
morphism. It uses the inverse of the stated class-to-morphism identification, so
its domain includes every supported cohomology class.

Clause-by-clause correspondence:

- The fixed finite ring A=A_{E,n} is `P : WeilConjectures.PurityFiniteSetting.{u}`
  and `P.Coefficient`. This is the standard ULift of the already defined quotient,
  not a new coefficient ring. `supportedHomCoefficientFinite` uses the existing
  `Padic.finite_coefficientExtensionRing` at `P.level`, with `P.level_pos`, and
  transports finiteness through `Equiv.ulift`. There is no extra finiteness assumption.
- The schemes and closed immersion are `{Z X : Scheme.{u}}`, `(i : Z ⟶ X)` and
  `[IsClosedImmersion i]`. Locally Noetherian is exactly `[IsLocallyNoetherian X]`.
- The site is literally `Scheme.ProEt.topology X`. Sheaves are the existing fixed-ring
  `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)` presentation,
  and derived categories are Mathlib `DerivedCategory` of that category. This is the
  presentation explicitly used by the recorded supported-exterior-product dependency;
  its `fixedRingDerivedTransport` is the finite-coefficient equivalence with intrinsic
  constant-ring module sheaves. Neither site universe is forced to equal the other.
- The underived direct image is the one in `supportedCoefficients A i`, whose body is
  `constantSheaf ... ⋙ lowerStar ... i`. Thus its value at `ModuleCat.of A A` is
  exactly the underived closed direct image of A_Z, and
  `supportedHomMorphismFunctor` places this object in degree zero. This is C_i(A),
  not a derived direct image or an arbitrary supported object. The intrinsic direct-image
  module is also imported; the fixed-ring presentation is the one mandated by the
  recorded C_i declaration.
- C_i and RΓ_Z are precisely `supportedCoefficients` and `supportedSectionsDerived`.
  Both adjunctions are the dependency's `supportedCoefficientAdjunction` and
  `supportedCoefficientDerivedAdjunction`, with no freely supplied adjunction datum.
  The quotient and its normalization remain the dependency's
  `supportedCoefficientQuotient` / `exists_unique_supportedCoefficientAdjunction`.
- Bounded below F is an arbitrary `DerivedCategory.Plus` object. This includes the
  localized image of every bounded-below cochain complex and every isomorphic object.
  The isomorphism is between functors on this entire category; hence it is natural
  in F. There is no constructibility, finite Tor, properness or quasi-compactness
  hypothesis on F or on the complement.
- The degree is `(a : ℤ)`, with no nonnegativity restriction. The degree-a single
  object `(DerivedCategory.singleFunctor (ModuleCat A) a).obj A` is canonically
  A[-a] for the supplied cochain convention. This avoids silently identifying
  propositionally isomorphic objects by definitional equality.
- H^a_Z(X,F)=H^aRΓ_Z(F) is `supportedHomCohomologyFunctor`. It applies the actual
  unbounded supported right derived functor, then degree-a cohomology, then forgets
  the module structure to the underlying additive group, as the existing supported-Hom
  theorem does. On D+ this is the same injective-resolution right-derived construction.
- A morphism `f : A[-a] ⟶ RΓ_Z(F)` represents its class by
  `supportedHomClassOfMorphism`: apply H^a(f) to the image of `(1 : A)` under the
  inverse of `singleFunctorCompHomologyFunctorIso`. This is the inverse of sending a
  cocycle class to the map carrying 1 in degree a to that cocycle. Freeness of A as an
  A-module makes this a bijection for all derived module objects, so quantifying over
  all f is equivalent to quantifying over all x in the node, not a restriction to
  special classes or representatives.
- `SupportedHomEvaluationNormalization` specifies χ on every bounded-below termwise
  injective complex I. It quantifies over every closed f:C_i(A)→I^a and every abstract
  cycle s of Γ_Z(I) whose underlying supported section is its ordinary adjoint
  evaluated at 1. By the dependency's quotient normalization this section is exactly
  f_X(q_i(1)). `supportedHomCycleClass` applies homologyπ to s and transports it through
  `homologyFunctorFactors` and the actual `rightDerivedFunctorUnit`; these are the
  canonical resolution comparisons, not chosen maps.
- In that normalization, χ of this class equals the localization of the complex map
  determined by f using `Cocycle.fromSingleMk`, `Cocycle.equivHomShift`, and
  `ShiftedHom.map`. The `singleFunctorIsoCompQ` and `quotientCompQhIso` factors are the
  canonical comparisons between the single, quotient and Plus.Q presentations. This
  is exactly deriving the inverse of the underived evaluation bijection and then
  applying `lem-sc-p1-rhom-hom-derived-roof`. Specifying it on all injective objects
  and requiring naturality specifies the same map on every F via an injective resolution.
- `supportedHomShiftedTranspose` is the inverse `homEquiv` of the actual derived
  adjunction, followed by shift a. The inverse `mapDerivedCategorySingleFunctor a`
  identifies C_i(A)[-a] with C_i(A[-a]); the inverse `singleFunctors.shiftIso a 0 a`
  identifies C_i(A)[0] with C_i(A)[-a][a]. They are the exact canonical comparisons
  implicit in x^flat[a]. The final equality is therefore χ(x)=x^flat[a], with
  precisely the same source and target and no unmentioned sign.
- The node's equivalent formulation is captured by the normalization conjunct and
  the last equality: the two constructions use the same ordinary evaluation
  bijection. It needs no separate tautological conjunct.

Dependencies read and used (all names below are existing declarations):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Coefficient`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, `.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage` (intrinsic presentation).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `.Qh`, `.singleFunctor`, `.singleFunctors`, `.quotientCompQhIso`.
- `Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct`:
  `AlgebraicGeometry.ProEtale.supportedCoefficients`, `.supportedCoefficientQuotient`,
  `.supportedCoefficientAdjunction`, `.exists_unique_supportedCoefficientAdjunction`,
  `.supportedSectionsDerived`, `.supportedCoefficientDerivedAdjunction`,
  `.fixedRingDerivedTransport`.
- `Sheaf.AlgebraicGeometry.SupportCohomology`:
  `AlgebraicGeometry.ProEtale.supportSections`, `.derivedSupportSections`,
  `CategoryTheory.Sheaf.supportedSectionsFunctor`.
- `Sheaf.Paper.SupportedCohomologyHom`:
  `AlgebraicGeometry.ProEtale.supported_cohomology_hom`. Its natural isomorphism shape
  is used, but its unnormalized Nonempty witness is not chosen as χ.
- `Sheaf.CategoryTheory.Abelian.RHomDerivedRoof`:
  `CategoryTheory.Functor.exists_rhom_hom_derived_roof`, including its cocycle formula.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, used as the named finiteness input to a real instance body.
- The proof-only imports are the recorded
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
  `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`,
  `Sheaf.CategoryTheory.Abelian.RHomDerivedRoof`, and
  `Mathlib.CategoryTheory.Functor.Derived.Adjunction`. The remaining stated proof
  dependencies, `IsGrothendieckAbelian.enoughInjectives` and
  `Functor.rightDerivedFunctorPlus`/its unit, are reexported through the support modules.
  Their full signatures were read. The derived-adjunction counit equation is
  `CategoryTheory.Adjunction.derivedε_fac_app`.

Edge cases checked before and during drafting:

- a=0: the degree-a single is A[0], the ordinary degree-zero evaluation and transpose
  agree, and the canonical shift-zero comparisons are still present.
- Negative and positive a: no inequality is imposed. The normalization uses the
  cochain cocycle-to-shift map, so it includes the (-1)^a boundary homotopy.
- Empty Z: C_i(A) and Γ_Z vanish; both Hom/cohomology functors vanish, all represented
  classes and all components of the formula are zero. Empty X is included as well.
- i=identity: supported sections are all sections and C_i is constant sheaf; the
  formula reduces to the usual constant-sheaf/global-sections adjunction comparison.
- Zero F and shifts of F are included by the arbitrary Plus object. No bound is fixed
  uniformly across F, and no finite-Tor or constructibility case was discarded.
- Non-quasi-compact complements and non-finite-type locally Noetherian X remain allowed.
- The general helper definitions allow the zero finite ring; their formula still
  has the unique element 1=0 and zero module / morphism groups. The main theorem uses
  the positive-level actual coefficient quotient required by the node.
- Arbitrary u is retained: the site object universe is u+1, its arrow universe u,
  and the coefficient module universe u+1, matching the published support framework.

Searches:

1. msearch `leanfinder`, query `The supported cohomology Hom identification equals the
   transpose under the derived adjunction`: 8 hits, including HomComplex cohomology
   equivalences and injective/projective Ext cocycle formulas, no exact support statement.
2. msearch `loogle`, query `CategoryTheory.Adjunction.homEquiv, ModuleCat.homFromFree`:
   no hits; the proposed free-Hom name is unknown. The actual canonical cohomology
   evaluation instead uses `singleFunctorCompHomologyFunctorIso`.
3. msearch `grep`, query `supportedHom|supportedCoefficientAdjunction|sectionsWithSupport`:
   0 Mathlib hits.
4. msearch `leansearch`, query `Cohomology with closed support and morphisms from the
   constant sheaf on a closed subset agree with the derived adjunction`: 8 hits, including
   constantSheafΓAdj, ΓHomEquiv and constantSheafAdj, no closed-support derived comparison.
5. `rg` in the source project's WeilConjectures and side `lean/Sheaf`, query
   `supportedHom|supported.*[Aa]djunction|Supported.*[Aa]djunction|supportedCoefficient|supportedExterior`:
   found the recorded support adjunction and unrelated naturality / tensor material, no
   statement asserting this comparison. The similarly named supported-Hom model in
   SupportedKummerSupportHomNaturality concerns a different etale model comparison.
6. Required `grep -rn lem-pur-supported-hom-adjunction-transpose` in the upstream
   WeilConjectures directory: no hits.
7. `rg` for every distinctive new main name in Mathlib, WeilConjectures,
   lean/Sheaf and dag/lean_names_upstream.json: no existing declaration.
8. Read the actual blueprint Step 5 and the supplied node's six-step normalization proof;
   read the cited local derived.tex locations and the exact Mathlib / project signatures.

Validation: scompile.py compiled the module cleanly, with no errors or warnings. Its
sandbox compile took 10.5 s and the library-path confirmation 19.6 s on the first clean
version. The final import-complete version is checked again by the delivery preflight.
There is one intentional `sorry`, the named main theorem; no definitions contain one.
No STATEMENT-DISPUTED issue or statement correction is needed.

## Second reading by Q15

The dispatcher explicitly forbids starting other agents and assigns the independent
review to the maintainer. This section records the worker's final rereading, not a
claim of an independent second worker review. I reopened the DAG statement and the
Lean module together and checked the clause mapping above. Two elaboration issues
were fixed: type-ascribe 1 as `(1 : A)` after the identity-functor comparison, and
open the existing `CochainComplex.HomComplex` namespace for its cocycle construction.
No mathematical statement was changed. In particular the final reread checked the
orientation of both localization comparisons, all three shift / single comparisons,
the actual normalized adjunction (rather than a freely supplied one), the evaluation
normalization (rather than an arbitrary Nonempty isomorphism), and the quantification
over every morphism representing a class. The only theorem proof remains `sorry`.
