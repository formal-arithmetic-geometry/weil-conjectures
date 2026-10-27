## Worker report

Existing interface attachment; no Lean module is added, no theorem is proved, and no
statement or dependency is changed. The node's source is already the implementation
of this entire native framework. Its category is `AlgebraicGeometry.WeilComplex` in
`WeilConjectures.WeilSheaf.Category`. The recorded public entry module is
`WeilConjectures.WeilSheaf.LowerShriek`, which publicly imports `OpenImmersion`,
`LowerStar`, and ultimately `Category`. Its own declaration
`AlgebraicGeometry.WeilComplex.derivedLowerShriek` is the primary attachment, and
`lean.declarations` lists the category, its defining object property, the coefficient
and constructibility definitions, and all the ambient and restricted operations.
This entry module exposes the full framework through one import. The primary
signature is copied verbatim from LowerShriek.lean, starting at `def` and ending
before `:=`; its field, prime, and scheme variables are bound in that source's
explicit `universe u` and `variable` declarations.

The clause-by-clause comparison against the unmodified node is as follows.

1. Finite field and coefficients. Category.lean binds `(k₀ : Type u) [Field k₀]
   [Finite k₀] (l : ℕ) [Fact l.Prime]`, and `WeilComplex` binds
   `[Fact (ringChar k₀ ≠ l)]`. The chosen closure is `AlgebraicClosure k₀`, used in
   `Scheme.specAlgebraicClosure` and `Scheme.Hom.geometricFiber`. `PadicAlgCl l` is
   `AlgebraicClosure (Padic l)` (Mathlib.NumberTheory.Padics.Complex). Its
   `PadicAlgCl.normedField` is the spectral norm extension, and `norm_extends`
   identifies the norm on the base. On finite subextensions this is the unique
   extended absolute value, the same characterization as
   `Padic.coefficientExtensionAbsoluteValue` in the imported coefficient-extension
   interface. The topology on the coefficient functions is this norm topology.
   `WeilCoefficients.{u} l` uses `ModuleCat.{u+1} (ULift.{u+1} (PadicAlgCl l))`;
   the lift changes size and preserves the field and its module operations.
2. Schemes and Frobenius. The binders are `X : Scheme.{u}` and
   `[X.Over (Spec (CommRingCat.of k₀))]`. Inherited triangulated structure requires
   `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]`, as the node assumes.
   The closure base change is `(X ↘ Spec (CommRingCat.of k₀)).geometricFiber`.
   `Scheme.Hom.geometricGaloisFrobenius` is `pullback.map` of the identity on the
   model and `specGeometricFrobenius k₀` on the closure. GeometricFrobenius.lean
   explicitly defines the latter using the inverse of the power-`#k₀` field
   automorphism. Thus the direction agrees with the node.
3. Site and B. `ProEtale.adicConstantSheaf l X̄` is a sheaf on
   `Scheme.ProEt.topology X̄`. Its sections are, by `adicConstantSheaf_obj_obj`,
   the universe lift of `PadicAlgCl.locallyFiniteFunctions l U.left`.
   The latter's carrier is exactly
   `∀ x, ∃ U ∈ 𝓝 x, FiniteDimensional (Padic l)
     (Submodule.span (Padic l) (f '' U))`
   for `f : C(U.left, PadicAlgCl l)`. Here `U.left` is the whole scheme's
   underlying space. `adicFunctionsPresheaf.map` uses
   `locallyFiniteFunctionsComp`, precomposition by the underlying continuous map.
   Adic/Ring.lean supplies pointwise algebra operations and the commutative
   monoid structure on this sheaf.
4. Module category. Adic/Module.lean defines
   `ProEtale.AdicSheaf l X̄ := Mod (Sheaf (Scheme.ProEt.topology X̄)
   (WeilCoefficients l)) (adicConstantSheaf l X̄)`.
   This is exactly the module-object presentation explicitly requested by the
   node, in sheaves of vector spaces over the discrete coefficient field. The
   topology in B is retained; B is not replaced by a discrete constant sheaf.
   The generic `SheafOfModules` encoding in `ringedSiteModules` and the tensor
   node describe the same module and tensor notions; no transport to that
   encoding or second definition is needed for an existing native attachment.
5. Fixed pairs. `WeilSheaf.frobeniusPullback k₀ l X` is pushforward along the
   inverse geometric Galois Frobenius, with its specified isomorphism to
   Frobenius pullback. `ProEtaleWeilSheaf k₀ l X` is
   `IsoAlgebra (WeilSheaf.frobeniusPullback k₀ l X)`.
   The upstream `IsoAlgebra` is itself the full subcategory of
   `Endofunctor.Algebra` where `IsIso str`, exactly the dependency's Mathlib
   specialization, including its commuting morphisms and forgetful functor.
6. Constructibility. `IsAdicLisseSheaf` quantifies over a pro-etale covering
   sieve and THEN over its members, with `∃ n : ℕ` inside that quantifier, and
   asks for an isomorphism to `⨁ fun _ : Fin n => AdicSheaf.unit l V`.
   `IsAdicStratifiedLisseSheaf` uses a finite index type, immersions with
   `Topology.IsConstructible` images, and unique membership for every point.
   `IsAdicConstructibleSheaf` asks for such a stratification on an open
   neighbourhood of every point. This includes every part of the node's
   local, finite, locally closed, constructible partition with ranks allowed
   to vary between covering members.
7. Derived category and full subcategory. `WeilSheaf.objectProperty` is the
   inverse image of `adicConstructibleSheaf` under `IsoAlgebra.forget`.
   `WeilComplex.objectProperty` is precisely
   `DerivedCategory.TStructure.t.bounded ⊓
     DerivedCategory.homologyProperty (WeilSheaf.objectProperty k₀ l X)`.
   The two bounds mean cohomology vanishes outside a finite interval of
   integers; the second factor imposes constructibility in every degree.
   `WeilComplex` is this property's `FullSubcategory` of the ordinary
   `DerivedCategory (ProEtaleWeilSheaf k₀ l X)`.
8. Shifts and triangles. Category.lean's `HasShift`, `Pretriangulated`, and
   `IsTriangulated` instances are inherited via that full subcategory from
   the ambient derived category; no category of fixed pairs in an already
   derived category is substituted. The locally finite type hypothesis is
   exactly the one required for its triangulated instance.
9. Ordinary images and coefficient maps. For a morphism `φ : X ⟶ Y` the
   binders include `[φ.IsOver (Spec (CommRingCat.of k₀))]` and the sheaf map is
   `Scheme.Hom.geometricFiberMap φ (comp_over φ _)`.
   Adic/Module.lean defines `adicLowerStar` by the monoidal adjunction's
   `modRight (adicConstantSheafToLowerStar l g)`, and `adicUpperStar` by
   `modLeft` for that same coefficient map. The latter's adjoint is the
   canonical `upperStarAdicConstantSheafHom`, proved invertible there, so its
   formula is the specified module inverse image/change of scalars. The
   coefficient map is induced by precomposition of the functions from
   clause 3. Direct image uses its action, not an arbitrary coefficient map.
10. Open extension by zero. `ProEtaleWeilSheaf.extensionByZero` binds
    `[IsOpenImmersion j]` and uses `adicOpenImmersionLowerShriek` on the base
    change. The module functor is the left adjoint of open restriction;
    `adicOpenImmersionLowerShriekComparison` is the canonical isomorphism
    identifying its underlying sheaf with the ordinary pro-etale extension
    by zero. The latter is the sheafified extension-by-zero presheaf (the
    singleton-or-empty map-to-open formula in the node); the ring action is
    the restricted B action. This agrees canonically with the localized
    ringed-site construction: the slice equivalence keeps the same V, so B
    restricts to B on U. The source chooses the left adjoint through its
    universal property, which determines it up to the unique adjunction-
    compatible isomorphism; it does not choose unconstrained module data.
11. Frobenius lifts and derived ordinary images. The three ambient sheaf
    functors are defined by `IsoAlgebra.mapOfNatIso` applied to
    `adicUpperStarGeometricFiberMapCompFrobeniusIso`,
    `adicLowerStarGeometricFiberMapCompFrobeniusIso`, and
    `adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso`.
    `mapOfNatIso_obj_str` is `e.app M.carrier ≪≫ L.mapIso M.str` and
    `mapOfNatIso_map_hom_f` is `L.map u.hom.f`, exactly `G(φ) ∘ c_M` and
    `G(u)`. `WeilComplex.upperStar` restricts the ambient exact functor's
    `mapDerivedCategory`. The ambient direct image's `rightDerivedFunctor`
    is taken in all pro-etale Weil sheaves; `derivedLowerStar` is its
    `liftFullSubcategory`. Its finite-type/qc/qs hypotheses apply to the
    constructible restriction, not to construction of the ambient functor.
12. Compact support and restrictions. For any `c : Compactification f`,
    `ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c` is definitionally
    `(ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory ⋙
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor`.
    The node's separated finite-type hypotheses are `[IsSeparated f]`,
    `[LocallyOfFiniteType f]`, `[QuasiCompact f]`; its qc/qs target is
    `[QuasiCompact (Y ↘ Spec ...)]`, `[QuasiSeparated (Y ↘ Spec ...)]`.
    Target local finite type is inherited from the node's class of schemes.
    `hasCompactification_of_over` supplies Nagata compactifiability, and
    `WeilComplex.derivedLowerShriek` uses exactly
    `HasCompactification.compactification f` with that instance. It restricts
    the displayed ambient composite via `liftFullSubcategory` and the
    separately named preservation theorem. This attachment neither proves
    that theorem nor identifies this category with derived fixed pairs.

Dependency declarations inspected (module paths relative to `lean/`, and Mathlib
paths relative to its source root):

| Dependency | Recorded declaration and module |
| --- | --- |
| def-weil-finite-type-morphism | `LocallyOfFiniteType`, `QuasiCompact`; Mathlib.AlgebraicGeometry.Morphisms.FiniteType / QuasiCompact |
| def-weil-pbc-proetale-site | `Scheme.ProEt`; Mathlib.AlgebraicGeometry.Sites.Proetale |
| def-weil-endofunctor-fixed-pair-category | `Endofunctor.Algebra`, its invertible-str full subcategory; Mathlib.CategoryTheory.Endofunctor.Algebra; implemented upstream as `IsoAlgebra` |
| def-weil-abstract-derived-category | `DerivedCategory`, `HasDerivedCategory`; Mathlib.Algebra.Homology.DerivedCategory.Basic |
| def-weil-triangulated-category | `Pretriangulated`, `IsTriangulated`; Mathlib.CategoryTheory.Triangulated.Pretriangulated / Triangulated |
| def-weil-compactifications-refinements | `Compactification.Refinement`; WeilConjectures.Compactification.RefinementCategory; `Compactification` and `HasCompactification.compactification` in Defs |
| def-weil-proper-morphism | `IsProper`, `IsSeparated`; Mathlib.AlgebraicGeometry.Morphisms.Proper / Separated |
| def-weil-quasi-separated-morphism | `QuasiSeparated`; Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated |
| def-weil-algebraic-closure | `AlgebraicClosure`; Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure |
| def-weil-l-adic-numbers | `Padic`; Mathlib.NumberTheory.Padics.PadicNumbers |
| sk-def-sfb-module-objects | `CategoryTheory.Mod`; Mathlib.CategoryTheory.Monoidal.Mod |
| def-weil-locally-closed-subset | `IsLocallyClosed`; Mathlib.Topology.Defs.Basic |
| def-weil-constructible-subset | `Topology.IsConstructible`; Mathlib.Topology.Constructible |
| def-weil-proetale-inverse-image | `Scheme.proEtaleSheafInverseImage` and coefficient/module maps; Sheaf.AlgebraicGeometry.ProEtaleInverseImage |
| def-pur-sheaf-tensor-product | `SheafOfModules.cochainModulesMonoidal`; Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses |
| def-weil-open-immersion | `IsOpenImmersion`; Mathlib.AlgebraicGeometry.OpenImmersion |
| def-sfb-right-derived-functor | `Functor.rightDerivedFunctorOfQuasiIsoResolutions` and universal pair; Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions |
| def-weil-l-adic-coefficient-extension | `Padic.finite_coefficientExtensionRing`; Sheaf.NumberTheory.Padics.CoefficientExtensionFinite; absolute value construction in its public CoefficientExtension import |
| def-weil-sheaf-of-modules-category | `CategoryTheory.ringedSiteModules`; Sheaf.CategoryTheory.RingedSiteModules |
| def-weil-pbc-constant-sheaf | `CategoryTheory.constantSheaf`; Mathlib.CategoryTheory.Sites.ConstantSheaf |
| lem-weil-proetale-weakly-etale-localization | `Scheme.ProEt.weaklyEtale_localization`, `sliceEquiv`; Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization |
| def-weil-presheaf-modules-sheafification | `PresheafOfModules.sheafification`; Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification |
| def-weil-extension-by-zero-presheaf | `SheafOfModules.extensionByZeroPresheaf`; WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf |

All dependency node statements, their recorded bindings or Mathlib matches, and the
corresponding source signatures/docstrings were read. No wrapper is redefined:
this is an existing upstream attachment, and the native modules use the underlying
Mathlib notions directly. The more general right-derived universal-pair dependency
agrees with the upstream right-derived construction in these Grothendieck abelian
categories, where monomorphic K-injective resolutions exist. No additional
resolution hypothesis is imposed on the node.

Edge cases checked against the definitions: empty schemes and empty strata (the
finite index type may be empty); zero sheaves (rank `n = 0`); different finite
ranks on different cover members; non-quasi-compact locally finite type schemes
(the stratification is local but the cohomological bounds are global); complexes
in a single arbitrary integer degree; identity morphisms and identity open
immersions (the ordinary canonical functors remain the ambient constructions);
non-qc bases (the ambient direct image still exists, without claiming its
constructible restriction preserves global boundedness); and distinct site
object/morphism universes (Scheme.ProEt has object size `u+1`, hom size `u`,
while vector spaces are lifted to `u+1`, as the source explicitly arranges).
No statement fault or STATEMENT-DISPUTED flag remains.

Searches on 2026-10-22:

- `msearch.py ... leanfinder "bounded constructible derived category of pro-etale Weil sheaves with invertible Frobenius action"`: eight generic hits (BDeRham, Witt-vector isocrystals, and condensed modules); no Mathlib match.
- `msearch.py ... loogle "WeilComplex, ProEtaleWeilSheaf"`: zero hits, unknown Mathlib identifier WeilComplex.
- `msearch.py ... grep "WeilComplex|ProEtaleWeilSheaf|adicConstantSheaf"`: zero Mathlib hits.
- `rg -n` in WeilConjectures for `def WeilComplex|abbrev ProEtaleWeilSheaf|def WeilComplex.derivedLowerShriek|def WeilComplex.derivedLowerStar|def WeilComplex.upperStar`: exact definitions in WeilSheaf/Category.lean, LowerStar.lean and LowerShriek.lean. Also distinguished the unrelated WeilObject/Defs.lean encoding.
- `grep -rn "def-sf-native-weil-derived-framework"` in WeilConjectures: no literal blueprint-id hit, but the exact source-named declarations above are present.
- `rg -n "nativeWeil|def WeilComplex|ProEtaleWeilSheaf|adicConstantSheaf"` in Sheaf: consumer uses (WeilFourierTransform and an upstream-extra module); no separate native framework definition.

Validation: the sandbox scratch probe imports the recorded public module and
checks every declaration in `lean.declarations` through `scompile.py`, with
`autoImplicit false`. Delivery dry-run and push also perform the standard server
existing-declaration probe and stage-2 preflight. There are no delivered Lean
files requiring separate compilation.

## Second reading by Q36

No second reading by a worker: the dispatcher brief prohibits starting other
agents and specifies direct worker delivery with the maintainer's independent
review. The clause mapping above is the worker's source comparison, not an
independent review.
