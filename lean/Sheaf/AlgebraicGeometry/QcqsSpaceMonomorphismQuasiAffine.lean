module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable

/-! # Locally finite type monomorphisms between qcqs algebraic spaces are quasi-affine

Source: Stacks Project, Morphisms of Spaces, Tags 073B(1), 0463 and 0ABS;
Tag 03XX and More on Morphisms, Tag 02LR
(blueprint: lem-sfb-space-qcqs-lft-mono-quasiaffine).

The conclusion uses the existing scheme-test representability predicate with the existing
scheme quasi-affine morphism property. Equivalently, all scheme tests are represented by
schemes and every affine scheme test has quasi-affine source.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type monomorphism between quasi-compact quasi-separated algebraic
spaces is quasi-affine. Quasi-compactness uses a quasi-compact surjective étale scheme
atlas. Absolute quasi-separatedness uses the equivalent affine-test criterion of 0AHR.
The monomorphism hypothesis is explicitly injectivity on every scheme of sections.
The conclusion asserts representability with quasi-affine scheme projections: over affine
tests the representing source is a quasi-compact open subscheme of an affine scheme.
Source: Stacks Project, Morphisms of Spaces, Tags 073B(1), 0463 and 0ABS
(blueprint: lem-sfb-space-qcqs-lft-mono-quasiaffine).

Proof:
1. By lem-a1-space-finite-affine-subatlas, the quasi-compact atlas of A gives a
   quasi-compact point space. Apply the same continuous-surjection assertion to the
   affine tests of B's absolute diagonal. Thus B is quasi-separated in the point-space
   convention of lem-sfb-space-qcqs-permanence. That lemma makes u quasi-compact on
   affine tests. By lem-sfb-qc-space-affine-etale-atlas, those point-space tests admit
   affine surjective étale atlases. The two quasi-compactness conventions therefore
   agree here. Together with local finite type, u is finite type in the convention
   of lem-sfb-stack-finite-type-calculus. A's quasi-separatedness and B's
   quasi-compactness are allowed but not needed for this step.
2. For every scheme T mapping to B, form E = A ×_B h_T using
   lem-trf-space-fibre-products-etale-covers. The projection v : E → h_T is finite
   type by arbitrary base-change stability in lem-sfb-stack-finite-type-calculus.
   It is a monomorphism: two matching pairs with the same T-component have equal
   A-components by the injectivity hypothesis on u.
3. Apply lem-sfb-space-lft-monomorphism-separated-lqf to v. Its relative diagonal
   is represented by closed immersions, and v is chartwise locally quasi-finite.
   Apply lem-a1-separated-locally-qf-space-representable to obtain a representing
   T-scheme Z_T. Since T was arbitrary, u is representable by schemes.
4. When T is affine, Z_T → T is locally finite type and locally quasi-finite by
   taking identity charts in step 3. It is separated by the diagonal assertion, and
   quasi-compact by steps 1 and 2. Apply
   lemma-nagata-quasi-affine-morphism-of-quasi-finite (the scheme theorem 02LR).
   By def-nagata-quasi-affine-morphism, Z_T is a quasi-affine scheme. This is the
   asserted affine-test condition. For arbitrary T, apply this conclusion on each
   affine open of T; scheme pullbacks identify its inverse image with the affine
   test just considered. Hence every representing projection is IsQuasiAffineHom,
   exactly the representability-with-property conclusion. -/
theorem isRepresentableWith_quasiAffine_of_mono_locallyOfFiniteType
    {S : Scheme.{u}} (A B : AlgebraicSpace S) (f : A ⟶ B)
    (hAqc : IsQuasiCompact A.obj) (hAqs : IsAbsolutelyQuasiSeparated A)
    (hBqc : IsQuasiCompact B.obj) (hBqs : IsAbsolutelyQuasiSeparated B)
    (hft : MapIsLocally (@LocallyOfFiniteType) f)
    (hm : ∀ T : Over S, Function.Injective (f.hom.hom.app (op T))) :
    IsRepresentableWith (fun _ _ p ↦ IsQuasiAffineHom p.left) f.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
