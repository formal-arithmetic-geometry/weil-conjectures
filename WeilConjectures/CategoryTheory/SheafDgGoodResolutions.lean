/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GradedSheafModule
public import WeilConjectures.CategoryTheory.SheafDgGeometricScalarExtension
public import WeilConjectures.CategoryTheory.RingedSiteDgModules
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import WeilConjectures.FromJoel.CategoryTheory.GradedObject.Colimits

/-! # Good resolutions of sheaf dg modules

Source: Stacks Project, sdga.tex, section-P-resolutions, Tags 0FSH, 0FSC and 0FSI,
and section-localize-dg (blueprint: lem-sfb-sheaf-dg-good-resolutions).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalOpposite

namespace CategoryTheory.SheafDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C} {S : Sheaf J CommRingCat.{u}}

/-- Forget differentials, retaining every homogeneous sheaf and map.
Source: Stacks sdga, section-P-resolutions
(blueprint: lem-sfb-sheaf-dg-good-resolutions). -/
abbrev forgetGrading (S : Sheaf J CommRingCat.{u}) : Complex S ⥤ Graded S :=
  HomologicalComplex.forget (ringedSiteModules.{u} (rings S)) (.up ℤ)

/-- The first graded balancing arrow, induced by the right action.
Source: Stacks sdga, tensor products (blueprint: lem-sfb-sheaf-dg-good-resolutions). -/
def gradedBalance₁ (A : Algebra S) (P : RightModule A) :
    Mod.forget (underlyingGradedAlgebra A).X ⋙
        tensorLeft ((forgetGrading S).obj ((rightUnderlying A).obj P) ⊗
          (underlyingGradedAlgebra A).X) ⟶
      Mod.forget (underlyingGradedAlgebra A).X ⋙
        tensorLeft ((forgetGrading S).obj ((rightUnderlying A).obj P)) where
  app N := (Functor.LaxMonoidal.μ (forgetGrading S)
    ((rightUnderlying A).obj P) A.X ≫ (forgetGrading S).map (rightAction A P)) ▷ N.X
  naturality _ _ f :=
    whisker_exchange (Functor.LaxMonoidal.μ (forgetGrading S)
      ((rightUnderlying A).obj P) A.X ≫ (forgetGrading S).map (rightAction A P)) f.hom

/-- The second graded balancing arrow, induced by the left action.
Source: Stacks sdga, tensor products (blueprint: lem-sfb-sheaf-dg-good-resolutions). -/
def gradedBalance₂ (A : Algebra S) (P : RightModule A) :
    Mod.forget (underlyingGradedAlgebra A).X ⋙
        tensorLeft ((forgetGrading S).obj ((rightUnderlying A).obj P) ⊗
          (underlyingGradedAlgebra A).X) ⟶
      Mod.forget (underlyingGradedAlgebra A).X ⋙
        tensorLeft ((forgetGrading S).obj ((rightUnderlying A).obj P)) where
  app N := (α_ _ _ _).hom ≫
    ((forgetGrading S).obj ((rightUnderlying A).obj P) ◁
      ModObj.smul (M := (underlyingGradedAlgebra A).X) (X := N.X))
  naturality _ _ f := by
    dsimp
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp]
    erw [← Mod.act_hom f]
    simp only [whiskerLeft_comp, Category.assoc]
    rfl

/-- Balanced graded tensor with the differential forgotten; the coequalizer is formed
in the functor category and hence degreewise in sheaves. Its tensor uses direct sums.
Source: Stacks sdga, section-P-resolutions, condition (1)
(blueprint: lem-sfb-sheaf-dg-good-resolutions). -/
def gradedTensor (A : Algebra S) (P : RightModule A) :
    GradedLeftModule (underlyingGradedAlgebra A) ⥤ Graded S :=
  coequalizer (gradedBalance₁ A P) (gradedBalance₂ A P)

/-- Conditions (1) and (2) of goodness: exact graded tensor and acyclic dg tensor.
Source: Stacks sdga, section-P-resolutions
(blueprint: lem-sfb-sheaf-dg-good-resolutions). -/
def TensorGood (A : Algebra S) (P : RightModule A) : Prop :=
  (PreservesFiniteLimits (gradedTensor A P) ∧ PreservesFiniteColimits (gradedTensor A P)) ∧
    ∀ N : LeftModule A, N.X.Acyclic → (rightTensor A P N).Acyclic

/-- Compatibility with the structural coefficient map on every generalized element.
Source: Stacks sdga, condition (3), a map of dg f⁻¹O-algebras
(blueprint: lem-sfb-sheaf-dg-good-resolutions). -/
def OverCoefficientMap {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (T : Sheaf K CommRingCat.{u}) (f : RingedToposMorphismOnSites
      (C := D) (D := C) (J := K) (K := J) (rings T) (rings S))
    (A : Algebra S) (B : Algebra T) (φ : PulledAlgebraMap (S := S) (T := T) f.inverse A B) : Prop :=
  ∀ (n : ℤ) (Z : Sheaf J (Type u))
    (a : Z ⟶ (sheafCompose J (CategoryTheory.forget RingCat.{u})).obj (rings S))
    (x z : Z ⟶ (SheafOfModules.toSheaf (rings S) ⋙
      sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (A.X.X n)),
    (∀ (V : Cᵒᵖ) (t : Z.obj.obj V),
      z.hom.app V t =
        @SMul.smul ((rings S).obj.obj V) ((A.X.X n).val.obj V) inferInstance
          (a.hom.app V t) (x.hom.app V t)) →
    ∀ (V : Dᵒᵖ) (t : (f.inverse.obj Z).obj.obj V),
      ((f.inverse.map z) ≫ φ.map n).hom.app V t =
        @SMul.smul ((rings T).obj.obj V) ((B.X.X n).val.obj V) inferInstance
          (((f.inverse.map a) ≫ f.ringMap).hom.app V t)
          (((f.inverse.map x) ≫ φ.map n).hom.app V t)

/-- Universally good right modules: the two tensor conditions hold before and after
all ringed-topos inverse images and dg scalar extensions. Quantification over every
universal presentation makes this independent of the choice of balanced tensor.
Source: Stacks sdga, section-P-resolutions, conditions (1)--(3)
(blueprint: lem-sfb-sheaf-dg-good-resolutions). -/
def Good (A : Algebra S) (P : RightModule A) : Prop :=
  TensorGood A P ∧
    ∀ {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
      (T : Sheaf K CommRingCat.{u}) (f : RingedToposMorphismOnSites
      (C := D) (D := C) (J := K) (K := J) (rings T) (rings S))
      (B : Algebra T) (φ : PulledAlgebraMap (S := S) (T := T) f.inverse A B)
      (Q : RightModule B)
      (a : PulledFamily (S := S) (T := T) f.inverse
        ((rightUnderlying A).obj P) ((rightUnderlying B).obj Q)),
      OverCoefficientMap T f A B φ →
        IsGeometricScalarExtension (S := S) (T := T) φ P Q a → TensorGood B Q

/-- The signed opposite already defined by the ringed-site dg framework.
Source: Stacks sdga, left-module convention
(blueprint: lem-sfb-sheaf-dg-good-resolutions). -/
abbrev signedOpposite (A : Algebra S) : Algebra S :=
  RingedSiteDg.opposite (C := C) (J := J) (O := S) A

/-- Convert a left module to a right module over the signed opposite. The monoidal
comparison is the Koszul braiding, so m*a=(-1)^(degree m * degree a) a*m.
Source: Stacks sdga, left-module convention
(blueprint: lem-sfb-sheaf-dg-good-resolutions). -/
def leftAsRight (A : Algebra S) : LeftModule A ⥤ RightModule (signedOpposite A) :=
  (mopFunctor (Complex S)).mapMod A.X

/-- Left goodness is right goodness after the signed-opposite equivalence.
Source: Stacks sdga, section-P-resolutions, left-module convention
(blueprint: lem-sfb-sheaf-dg-good-resolutions). -/
def LeftGood (A : Algebra S) (M : LeftModule A) : Prop :=
  Good (signedOpposite A) ((leftAsRight A).obj M)

/-- A right restriction functor with its actual restricted action, pinned on sections.
For an open site the slice site is the open subspace site.
Source: Stacks sdga, section-localize-dg
(blueprint: lem-sfb-sheaf-dg-good-resolutions). -/
structure RightOpenModel (A : Algebra S) (U : C) where
  module : RightModule A ⥤ RightModule (restrictAlgebra A U)
  underlying : module ⋙ rightUnderlying (restrictAlgebra A U) ≅
    rightUnderlying A ⋙ restrictionComplex S U
  action (P : RightModule A) (p q : ℤ) (V : (Over U)ᵒᵖ)
      (x : (((rightUnderlying (restrictAlgebra A U)).obj (module.obj P)).X p).val.obj V)
      (a : ((restrictAlgebra A U).X.X q).val.obj V) :
    (((underlying.hom.app P).f (p + q)).val.app V)
        (rightActionSection (restrictAlgebra A U) (module.obj P) p q V x a) =
      rightActionSection A P p q (Opposite.op V.unop.left)
        ((((underlying.hom.app P).f p).val.app V) x) a

/-- The homogeneous pure tensor in the actual balanced dg tensor sheaf.
Source: Stacks sdga, section-tensor-product-dg
(blueprint: lem-sfb-sheaf-dg-good-resolutions). -/
def balancedTensorSection (A : Algebra S) (P : RightModule A) (N : LeftModule A)
    (p q : ℤ) (V : Cᵒᵖ)
    (x : (((rightUnderlying A).obj P).X p).val.obj V) (y : (N.X.X q).val.obj V) :
    ((rightTensor A P N).X (p + q)).val.obj V :=
  ((HomologicalComplex.ιTensorObj ((rightUnderlying A).obj P) N.X p q (p + q) rfl ≫
    (rightTensorπ A P N).f (p + q)).val.app V)
      (tensorSection (((rightUnderlying A).obj P).X p) (N.X.X q) V x y)

/-- Good resolutions, closure under shifts and cones, and tensor annihilation.
Source: Stacks sdga, 0FSH, 0FSC, 0FSI (1)
(blueprint: lem-sfb-sheaf-dg-good-resolutions).

Proof:
1. Graded-split extensions of good modules remain good: tensor preserves the splitting,
   and the long exact cohomology sequence proves acyclicity. Splittings survive base change.
   Shifts reindex the signed tensor; cones are extensions of the target by the source shift.
2. Tensor and geometric inverse image commute with filtered colimits by their universal
   properties. Exact filtered colimits of module sheaves commute with cohomology, so
   filtered colimits of good modules remain good, also after any base change.
3. Form the free module on the cycle sheaves of M. Map each closed generator to its cycle.
   This is good by 0FSG and maps epimorphically onto every cohomology sheaf.
4. At step i adjoin degree-n generators for pairs (p,m), with p a degree-(n+1) cycle
   and u_i(p)=dm. Set de=p and u(e)=m. The Leibniz signs cancel in d²(ea), so these
   formulas define a dg module and chain map. The quotient is free on closed generators;
   the graded splitting and step 1 preserve goodness.
5. The sequential colimit is good by step 2. Each cohomology kernel is killed at the next
   step, locally on the site; exact colimits therefore make its augmentation a quasi-iso.
6. Apply the same construction to the signed opposite for left good resolutions. If P
   is acyclic and good, take a good left resolution Q→N with acyclic cone T. Both P⊗Q
   and P⊗T are acyclic by goodness. Tensor the graded-split cone sequence; its long
   exact sequence forces P⊗N acyclic, without any flatness assumption on N. -/
theorem good_resolutions (A : Algebra S) :
    (∀ M : RightModule A, ∃ (P : RightModule A) (e : P ⟶ M),
      Good A P ∧ QuasiIso ((rightUnderlying A).map e)) ∧
    (∀ (P Q : RightModule A) (k : ℤ), Good A P →
      RingedSiteDg.ShiftComparison (C := C) (J := J) (O := S) A k P Q → Good A Q) ∧
    (∀ (P Q : RightModule A) (f : P ⟶ Q), Good A P → Good A Q →
      ∀ (K R : RightModule A) (s : RingedSiteDg.ShiftComparison
          (C := C) (J := J) (O := S) A 1 P R)
        (g : Q ⟶ K) (h : K ⟶ R),
        RingedSiteDg.ConeComparison (C := C) (J := J) (O := S) A f K R s g h → Good A K) ∧
    ∀ P : RightModule A, Good A P → ((rightUnderlying A).obj P).Acyclic →
      ∀ N : LeftModule A, (rightTensor A P N).Acyclic := by
  sorry

/-- The left-module assertions, with the tensor factors reversed.
Source: Stacks sdga, 0FSH, 0FSC, 0FSI, left-module convention
(blueprint: lem-sfb-sheaf-dg-good-resolutions).

Proof: use the signed opposite algebra a*b=(-1)^(|a||b|)ba and convert an action
by m*a=(-1)^(|m||a|)am. Substitution verifies both Leibniz identities. Swapping
balanced tensor factors by m⊗n↦(-1)^(|m||n|)n⊗m commutes with the differentials.
These equivalences preserve cohomology, graded exactness and geometric scalar change.
Apply the six steps of good_resolutions to this opposite algebra. The signed left
shift and cone actions are precisely the actions transported by this equivalence.
For tensor annihilation take a good right resolution and tensor its graded-split
cone sequence, exactly as in step 6 above. -/
theorem left_good_resolutions (A : Algebra S) :
    (∀ M : LeftModule A, ∃ (P : LeftModule A) (e : P ⟶ M),
      LeftGood A P ∧ QuasiIso e.hom) ∧
    (∀ (P : LeftModule A) (k : ℤ), LeftGood A P → LeftGood A (shift A k P)) ∧
    (∀ (P Q : LeftModule A) (f : P ⟶ Q),
      LeftGood A P → LeftGood A Q → LeftGood A (cone A f)) ∧
    ∀ N : LeftModule A, LeftGood A N → N.X.Acyclic →
      ∀ P : RightModule A, (rightTensor A P N).Acyclic := by
  sorry

/-- Open restriction preserves goodness, quasi-isomorphisms and balanced tensor,
for right and left modules. A right restriction model exists, and the assertions hold
for every such model, so they do not depend on its choice. The displayed tensor
comparison is normalized on all homogeneous pure tensors, including its differential,
rather than an arbitrary iso.
Source: Stacks sdga, section-localize-dg and section-P-resolutions (3)
(blueprint: lem-sfb-sheaf-dg-good-resolutions).

Proof:
1. On the open site, restriction evaluates the same sheaf on the opens of U. Restrict
   multiplication, unit and the right action sectionwise. Their identities and naturality
   restrict, so this gives RightOpenModel. The left restriction is the existing one.
   Any model R is identified with this one by its underlying isomorphism, which preserves
   the actions because tensor sections generate locally; all assertions below are
   invariant under such module isomorphisms, so it suffices to treat one model.
2. The open inverse image is exact, so it commutes with cycles, boundaries and cohomology;
   consequently it preserves quasi-isomorphisms on either module category.
3. Restriction preserves the graded direct sums and the balancing coequalizer. Sheafification
   uses exactly the same covers on every open inside U. The identity on homogeneous pure
   tensors therefore induces the displayed complex isomorphism, natural in both modules.
4. Restriction is geometric scalar extension along the identity restricted algebra map,
   so goodness gives its two tensor conditions. To check its universal condition, compose
   any geometric morphism into the open topos with the open inclusion and use associativity
   of the balanced tensor. This proves right goodness on U.
5. The signed-opposite conversion commutes with sectionwise restriction. Step 4 gives left
   goodness, and steps 2--3 give the corresponding left quasi-isomorphism and tensor clauses.
   Empty opens and the empty space use the same sectionwise formulas. -/
theorem good_open_restriction {X : TopCat.{c}}
    (S : TopCat.Sheaf CommRingCat.{u} X)
    [EssentiallySmall.{u} (TopologicalSpace.Opens X)] (A : Algebra S)
    (U : TopologicalSpace.Opens X) :
    Nonempty (RightOpenModel A U) ∧ ∀ R : RightOpenModel A U,
      (∀ P : RightModule A, Good A P → Good (restrictAlgebra A U) (R.module.obj P)) ∧
      (∀ (P Q : RightModule A) (e : P ⟶ Q), QuasiIso ((rightUnderlying A).map e) →
        QuasiIso ((rightUnderlying (restrictAlgebra A U)).map (R.module.map e))) ∧
      (∀ N : LeftModule A, LeftGood A N →
        LeftGood (restrictAlgebra A U) (restrictModule A U N)) ∧
      (∀ (M N : LeftModule A) (e : M ⟶ N), QuasiIso e.hom →
        QuasiIso (((restriction A U).map e).hom)) ∧
      ∀ (P : RightModule A) (N : LeftModule A),
        ∃ e : rightTensor (restrictAlgebra A U) (R.module.obj P) (restrictModule A U N) ≅
          (restrictionComplex S U).obj (rightTensor A P N),
          ∀ (p q : ℤ) (V : (Over U)ᵒᵖ)
            (x : (((rightUnderlying (restrictAlgebra A U)).obj (R.module.obj P)).X p).val.obj V)
            (y : ((restrictModule A U N).X.X q).val.obj V),
            ((e.hom.f (p + q)).val.app V)
                (balancedTensorSection (restrictAlgebra A U) (R.module.obj P)
                  (restrictModule A U N) p q V x y) =
              balancedTensorSection A P N p q (Opposite.op V.unop.left)
                ((((R.underlying.hom.app P).f p).val.app V) x) y := by
  sorry

end CategoryTheory.SheafDg
