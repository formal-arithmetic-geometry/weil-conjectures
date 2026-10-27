module

public import Sheaf.AlgebraicGeometry.SpaceRelativeDifferentials
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # Square-zero infinitesimal points of an arbitrary group algebraic space

Source: Stacks Project, Tags 0618, 0619 and 04D0, and the linearity and unit
argument of Tag 0BF5 (blueprint: lem-sfb-group-space-square-zero-kernel-module).

The difference normalization is an equation on regular functions on etale charts.
It fixes the sign and the actual map, rather than asserting an unspecified equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- The represented morphism associated to a point of the group-valued functor.
Source: Stacks 025Y and 0618
(blueprint: lem-sfb-group-space-square-zero-kernel-module). -/
def groupPointMap (G : AlgebraicSpace S) (F : (Over S)ᵒᵖ ⥤ GrpCat.{u})
    (e : F ⋙ forget GrpCat ≅ G.obj.obj) (T : Over S) (x : F.obj (op T)) :
    schemeSpace T ⟶ G :=
  ObjectProperty.homMk ⟨yonedaEquiv.symm (e.hom.app (op T) x)⟩

/-- A chart map with its commuting triangle, as used by the existing tensor section.
Source: Stacks 03G8 and 0619
(blueprint: lem-sfb-group-space-square-zero-kernel-module). -/
def differenceChart {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : X.EtaleSite) (V : Y.EtaleSite) (g : U.obj.left ⟶ V.obj.left)
    (h : yoneda.map g ≫ V.obj.hom = U.obj.hom ≫ f.hom.hom) : ModuleChart f V :=
  CostructuredArrow.mk (Y := U) (CostructuredArrow.homMk g h)

/-- The defining ideal as a module on the original etale site, with its kernel inclusion.
Source: Stacks 04EX and 0618
(blueprint: lem-sfb-group-space-square-zero-kernel-module). -/
def differenceIdeal {T₀ T : Over S} (j : T₀ ⟶ T) : (schemeSpace T).Modules :=
  kernel (moduleStructureMap (groupSchemeMap j))

/-- The ideal on the reduction is its tensor conormal module I/I², hence I in square zero.
Source: Stacks 04EX and 0619
(blueprint: lem-sfb-group-space-square-zero-kernel-module). -/
def differenceIdealOnReduction {T₀ T : Over S} (j : T₀ ⟶ T) :
    (schemeSpace T₀).Modules :=
  (moduleTensorPullback (groupSchemeMap j)).obj (differenceIdeal j)

/-- The Hom group appearing in the square-zero difference formula.
Source: Stacks 0619 (blueprint: lem-sfb-group-space-square-zero-kernel-module). -/
abbrev differenceHom {T₀ T : Over S} (j : T₀ ⟶ T) {G : AlgebraicSpace S}
    (a : schemeSpace T ⟶ G) :=
  (moduleTensorPullback (groupSchemeMap j ≫ a)).obj (relativeOmega G) ⟶
    differenceIdealOnReduction j

/-- The normalized difference b-sharp minus a-sharp, tested on affine etale target charts.
The source reduction chart is the entire cartesian reduction of U. The two maps
to a target chart have equal reduction. The witness s is their difference
in the kernel ideal; tensoring its class to the reduction is the value on dx.
Source: Stacks 0618, 0619 and 04D0
(blueprint: lem-sfb-group-space-square-zero-kernel-module). -/
def IsSquareZeroDifference {T₀ T : Over S} (j : T₀ ⟶ T) {G : AlgebraicSpace S}
    (a b : schemeSpace T ⟶ G) (φ : differenceHom j a) : Prop :=
  ∀ (V : G.SmallEtaleModel) (U : (schemeSpace T).EtaleSite)
    (U₀ : (schemeSpace T₀).EtaleSite)
    (l : U₀.obj.left ⟶ U.obj.left)
    (_hcart : IsPullback l (yoneda.preimage U₀.obj.hom)
      (yoneda.preimage U.obj.hom) j)
    (hj : yoneda.map l ≫ U.obj.hom = U₀.obj.hom ≫ (groupSchemeMap j).hom.hom)
    (α β : U.obj.left ⟶ (G.smallEtaleInclusion.obj V).obj.left)
    (_ha : yoneda.map α ≫ (G.smallEtaleInclusion.obj V).obj.hom =
      U.obj.hom ≫ a.hom.hom)
    (_hb : yoneda.map β ≫ (G.smallEtaleInclusion.obj V).obj.hom =
      U.obj.hom ≫ b.hom.hom)
    (_hred : l ≫ α = l ≫ β)
    (h₀ : yoneda.map (l ≫ α) ≫ (G.smallEtaleInclusion.obj V).obj.hom =
      U₀.obj.hom ≫ (groupSchemeMap j ≫ a).hom.hom)
    (x : G.smallStructureSheaf.obj.obj (op V)),
    ∃ s : (differenceIdeal j).val.obj (op U),
      (kernel.ι (moduleStructureMap (groupSchemeMap j))).val.app (op U) s =
        β.left.appTop x - α.left.appTop x ∧
      φ.val.app (op U₀)
        (moduleTensorSection (groupSchemeMap j ≫ a) (relativeOmega G)
          (G.smallEtaleInclusion.obj V)
          (differenceChart _ U₀ _ (l ≫ α) h₀) 1 (relativeOmegaSection G V x)) =
        moduleTensorSection (groupSchemeMap j) (differenceIdeal j) U
          (differenceChart _ U₀ U l hj) 1 s

/-- Spec(A/I) with its prescribed map to S.
Source: Stacks 04EX (blueprint: lem-sfb-group-space-square-zero-kernel-module). -/
def quotientTest {A : Type u} [CommRing A] (s : Spec (.of A) ⟶ S) (I : Ideal A) :
    Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s)

/-- The canonical closed immersion Spec(A/I) to Spec(A), as a map over S.
Source: Stacks 04EX (blueprint: lem-sfb-group-space-square-zero-kernel-module). -/
def quotientTestArrow {A : Type u} [CommRing A] (s : Spec (.of A) ⟶ S) (I : Ideal A) :
    quotientTest s I ⟶ Over.mk s :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) rfl

/-- The original group kernel, before transporting any additive or module structure.
Source: Stacks 0618 and 0BF5
(blueprint: lem-sfb-group-space-square-zero-kernel-module). -/
abbrev squareZeroPointKernel {A : Type u} [CommRing A]
    (F : (Over S)ᵒᵖ ⥤ GrpCat.{u}) (s : Spec (.of A) ⟶ S) (I : Ideal A) :=
  (F.map (quotientTestArrow s I).op).hom.ker

/-- Pullback of a scalar in A/I to the regular functions on an etale test of Spec(A/I).
Source: Stacks 03G7 and 0619
(blueprint: lem-sfb-group-space-square-zero-kernel-module). -/
def quotientChartScalar {A : Type u} [CommRing A]
    (s : Spec (.of A) ⟶ S) (I : Ideal A)
    (U : (schemeSpace (quotientTest s I)).EtaleSite) (c : A ⧸ I) :
    (schemeSpace (quotientTest s I)).structureSheaf.obj.obj (op U) :=
  (yoneda.preimage U.obj.hom).left.appTop ((Scheme.ΓSpecIso (.of (A ⧸ I))).inv c)

/-- The canonical additive identification and quotient-module structure, without
commutativity or smoothness of the group space.
Source: Stacks 0618, 0619, 04D0 and the linearity-and-unit argument of 0BF5
(blueprint: lem-sfb-group-space-square-zero-kernel-module).

Proof:
1. Since I²=0, scalar multiplication on I factors through A/I. Apply
   lem-sfb-space-square-zero-lift-linearization to the identity lift. Its lift set
   is exactly the group kernel, and its canonical difference map is the formula
   IsSquareZeroDifference above. It is a bijection sending the identity to zero.
2. Apply the same linearization to G times G. Projection identifies its difference
   module linearly with the product of the two modules, since pairing maps gives
   the inverse bijection on lifts. Postcomposition by multiplication is linear.
3. The two unit laws say that this linear map fixes (v,0) and (0,w). Decomposing
   (v,w) as their sum proves that multiplication goes to addition. This is the
   argument of 0BF5 and uses no commutativity of G and no finite presentation.
4. Transport the A/I-module action through the normalized difference bijection.
   Its zero and addition are the original identity and multiplication; its scalar
   action is the displayed componentwise scalar action on module homomorphisms.
   Induction on r gives x^r = r times x, including r=0. The difference formula
   determines the bijection uniquely because local differentials generate Omega
   and etale charts cover; hence this module structure is canonical. -/
theorem groupSpace_squareZero_kernel_module
    {A : Type u} [CommRing A] (G : AlgebraicSpace S)
    (F : (Over S)ᵒᵖ ⥤ GrpCat.{u}) (e : F ⋙ forget GrpCat ≅ G.obj.obj)
    (s : Spec (.of A) ⟶ S) (I : Ideal A)
    (_hj : IsFirstOrderThickening (quotientTestArrow s I).left) :
    ∃! δ : squareZeroPointKernel F s I ≃
        differenceHom (quotientTestArrow s I) (groupPointMap G F e (Over.mk s) 1),
      (∀ x : squareZeroPointKernel F s I,
        IsSquareZeroDifference (quotientTestArrow s I)
          (groupPointMap G F e (Over.mk s) 1)
          (groupPointMap G F e (Over.mk s) x.val) (δ x)) ∧
      δ 1 = 0 ∧
      (∀ x y : squareZeroPointKernel F s I, δ (x * y) = δ x + δ y) ∧
      ∃ (C : AddCommGroup (squareZeroPointKernel F s I))
        (M : @Module (A ⧸ I) (squareZeroPointKernel F s I) _ C.toAddCommMonoid),
        C.zero = 1 ∧
        (∀ x y : squareZeroPointKernel F s I, C.add x y = x * y) ∧
        (∀ (c : A ⧸ I) (x : squareZeroPointKernel F s I)
          (U : (schemeSpace (quotientTest s I)).EtaleSite)
          (v : ((moduleTensorPullback (groupSchemeMap (quotientTestArrow s I) ≫
            groupPointMap G F e (Over.mk s) 1)).obj (relativeOmega G)).val.obj (op U)),
          (δ (@SMul.smul _ _ M.toSMul c x)).val.app (op U) v =
            quotientChartScalar s I U c • (δ x).val.app (op U) v) ∧
        (∀ (r : ℕ) (x : squareZeroPointKernel F s I),
          @SMul.smul _ _ M.toSMul (r : A ⧸ I) x = x ^ r) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
