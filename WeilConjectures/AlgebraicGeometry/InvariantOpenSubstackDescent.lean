/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.AlgebraicModuliStack
public import WeilConjectures.AlgebraicGeometry.OpenModuliSubstack
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import WeilConjectures.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Invariant atlas opens descend to open substacks

Source: Stacks Project, stacks-properties.tex, Tag 0507 (lemma-substacks-presentation),
open case and factorization criterion; algebraic.tex, definition-algebraic-stack
(blueprint: lem-sfb-invariant-open-substack-descent).

The self-relation condition is tested on every scheme-valued arrow: two maps into
an atlas with 2-isomorphic composites have equal inverse-image open subschemes.
The correspondence is identified with the actual 2-fibre-product projection.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- The open subscheme of an atlas with its structural map to the original base.
Source: Stacks Project, Tag 0507, open case
(blueprint: lem-sfb-invariant-open-substack-descent). -/
def openAtlasScheme {S : Scheme.{u}} (P : Over S) (V : P.left.Opens) : Over S :=
  Over.mk (V.ι ≫ P.hom)

/-- The canonical inclusion of the atlas open, as a morphism over the base.
Source: Stacks Project, Tag 0507, open case
(blueprint: lem-sfb-invariant-open-substack-descent). -/
def openAtlasSchemeι {S : Scheme.{u}} (P : Over S) (V : P.left.Opens) :
    openAtlasScheme P V ⟶ P :=
  Over.homMk V.ι

/-- Pullback to a smooth surjective atlas bijects open substacks with invariant
open subschemes, preserves and reflects inclusion, and detects factorization for
arbitrary morphisms of algebraic stacks.
Source: Stacks Project, Tag 0507 (lemma-substacks-presentation), open case;
Tags 04YM and 03BZ (blueprint: lem-sfb-invariant-open-substack-descent).

Proof:
1. Pull an open substack back to P. Strict fullness makes its two inverse images
on R = P ×_F P equal, and pullback preserves inclusion
(def-sfb-stable-pointed-moduli-groupoids, def-weil-open-immersion).
2. For an invariant open V and x : T → F, put Q_x = T ×_F P and
E_x = Q_x ×_P V. The space fibre-product theorem
(lem-trf-space-fibre-products-etale-covers) supplies these spaces. The atlas map
q_x : Q_x → T is smooth surjective. The chartwise calculus
(lem-sfb-stack-chartwise-smooth-etale-calculus) gives surjectivity on field-point
classes and flatness and local finite presentation. Hence q_x is open by
lem-sfb-flat-lfp-space-universally-open, so U_x = q_x(E_x) is an open subscheme
of T. Use only the open-subspace correspondence of lem-a1-space-etale-open-image.
3. For T' → T, compatible field representatives acquire a common extension.
They give points of T' ×_T E_x, proving U_(x|T') = U_x ×_T T'. An isomorphism
x ≅ y similarly identifies Q_x, E_x with Q_y, E_y, hence U_x = U_y.
4. Invariance proves q_x⁻¹(U_x) = E_x: compare a point above U_x with a point
of E_x having the same image, pass to a common extension and use their comparison
isomorphisms to obtain an R-point. Equality of the two R-inverse images forces
both atlas components into V. For x = p, surjectivity of R → P then gives U_p = V.
5. Select the full subcategory W on x with U_x = T. Step 3 makes membership
pullback-stable and invariant under isomorphism; it is local for étale covers.
Isomorphism sheaves are inherited from F, and effective descent in F descends
objects into W by this locality. The scheme test at x is U_x: a test map g lifts
exactly when g⁻¹(U_x) is the whole source, equivalently when g factors through
U_x. Full faithfulness makes its lift groupoid contractible whenever nonempty.
6. The diagonal of W is represented by that of F. Step 4 gives its atlas V:
for x in W the base change of V → W is E_x = Q_x, smooth and surjective over T.
Thus W is algebraic and has precisely the required atlas pullback.
7. Any open W' with atlas pullback V has scheme test T' with
q_x⁻¹(T') = E_x. Surjectivity of q_x gives T' = U_x, so strict fullness identifies
W' with W. This proves the bijection. Inclusions of atlas opens give inclusions
of E_x and U_x, so the inverse also preserves inclusion.
8. A factorization through W pulls back to one through V. Conversely, if the
atlas pullback of f factors through V, every y : T → G has E_(fy) = Q_(fy).
Surjectivity gives U_(fy) = T, so f sends every object into W. Fullness restricts
its arrow assignment and yields the required functor into W, over the base.
No representability hypothesis on f is used. -/
theorem invariantOpenSubstackDescent {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (hF : IsAlgebraicModuliStack F)
    (P : Over S) (p : BasedFunctor (discreteModuli (yoneda.obj P)) F)
    (hp : IsSmoothModuliAtlas F P p) :
    ∃ e : OpenModuliSubstack F ≃
        {V : P.left.Opens // ∀ (T : Over S) (a b : T ⟶ P),
          Nonempty (ModuliTwoIso ((discreteModuliMap (yoneda.map a)).comp p)
            ((discreteModuliMap (yoneda.map b)).comp p)) →
              a.left ⁻¹ᵁ V = b.left ⁻¹ᵁ V},
      (∀ W Z : OpenModuliSubstack F,
        W.IsContainedIn Z ↔ (e W).val ≤ (e Z).val) ∧
      (∀ W : OpenModuliSubstack F,
        ∃ c : BasedFunctor (discreteModuli (yoneda.obj (openAtlasScheme P (e W).val)))
            (moduliTwoFiberProduct p (fullModuliInclusion F W.property)),
          c.toFunctor.IsEquivalence ∧
            Nonempty (ModuliTwoIso
              (c.comp (moduliTwoFiberFst p (fullModuliInclusion F W.property)))
              (discreteModuliMap (yoneda.map (openAtlasSchemeι P (e W).val))))) ∧
      ∀ (G : BasedCategory.{v₂, w₂} (Over S)), IsAlgebraicModuliStack G →
        ∀ (f : BasedFunctor G F) (W : OpenModuliSubstack F),
          (∃ g : BasedFunctor G W.category,
            Nonempty (ModuliTwoIso (g.comp (fullModuliInclusion F W.property)) f)) ↔
          ∃ g : BasedFunctor (moduliTwoFiberProduct p f)
              (discreteModuli (yoneda.obj (openAtlasScheme P (e W).val))),
            Nonempty (ModuliTwoIso
              (g.comp (discreteModuliMap (yoneda.map (openAtlasSchemeι P (e W).val))))
              (moduliTwoFiberFst p f)) := by
  sorry

end CategoryTheory
