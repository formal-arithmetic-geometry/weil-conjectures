/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

/-! # Balanced scalar-extension comparison on unbounded tensor complexes

Source: Stacks Project, Modules on Sites, Tags 03EK, 03CY and 0GMW;
Homology, Tag 012Z and the cochain homotopy equation preceding Tag 0113.
(blueprint: lem-trf-site-balanced-tensor-chain)

The functor E is the sheafified scalar extension, specified on both objects and maps.
The tensor is the existing signed direct-sum total, including for unbounded complexes.
Local formulas always pass through module sheafification units.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u v r

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings

namespace SheafOfModules
namespace BalancedTensorChain

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R S : Sheaf J CommRingCat.{r}}
  (φ : R ⟶ S)

variable
  (E : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤ ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) [E.Additive]
  (hobj : ∀ M, E.obj M = changeOfRings φ M)

/-- The source total complex, with the restricted module in degree zero.
Source: Stacks 03EK and Homology 012Z
(blueprint: lem-trf-site-balanced-tensor-chain). -/
def source (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (N : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) :=
  HomologicalComplex.tensorObj P (((restrictScalars ((sheafCompose J (forget₂ CommRingCat
    RingCat)).map φ)).mapHomologicalComplex (.up ℤ)).obj ((HomologicalComplex.single _ (.up ℤ)
      0).obj N))

/-- The target total complex, restricted back to R.
Source: Stacks 03EK and Homology 012Z
(blueprint: lem-trf-site-balanced-tensor-chain). -/
def target (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (N : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) :=
  ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
    (.up ℤ)).obj (HomologicalComplex.tensorObj ((E.mapHomologicalComplex (.up ℤ)).obj P)
      ((HomologicalComplex.single _ (.up ℤ) 0).obj N))

/-- The sheafification-unit image of x tensor n in the source's (i,0) summand.
Source: Stacks 03EK and Homology 012Z
(blueprint: lem-trf-site-balanced-tensor-chain). -/
def sourceSection (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (N : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    (i : ℤ) (V : Cᵒᵖ) (x : (P.X i).val.obj V) (n : N.val.obj V) :
    ((source φ P N).X (i + 0)).val.obj V :=
  ((HomologicalComplex.ιTensorObj P (((restrictScalars ((sheafCompose J (forget₂ CommRingCat
    RingCat)).map φ)).mapHomologicalComplex (.up ℤ)).obj ((HomologicalComplex.single _ (.up ℤ)
      0).obj N)) i 0 (i + 0) rfl).val.app V
          ((tensorObjIsoSheafification (R := R) (P.X i) ((((restrictScalars ((sheafCompose J
            (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex (.up ℤ)).obj
              ((HomologicalComplex.single _ (.up ℤ) 0).obj N)).X 0)).inv.val.app V
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
                ((P.X i).val ⊗ ((((restrictScalars ((sheafCompose J (forget₂ CommRingCat
                  RingCat)).map φ)).mapHomologicalComplex (.up ℤ)).obj ((HomologicalComplex.single
                    _ (.up ℤ) 0).obj N)).X 0).val)).app V
                  (x ⊗ₜ[R.obj.obj V] (((restrictScalars ((sheafCompose J (forget₂ CommRingCat
                    RingCat)).map φ)).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv).val.app V n)))))

/-- The two sheafification-unit images of (x tensor s) tensor n in the target.
Source: Stacks 03EK and Homology 012Z
(blueprint: lem-trf-site-balanced-tensor-chain). -/
def targetSection (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (N : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    (i : ℤ) (V : Cᵒᵖ) (x : (P.X i).val.obj V) (s : S.obj.obj V) (n : N.val.obj V) :
    ((target φ E P N).X (i + 0)).val.obj V :=
  ((HomologicalComplex.ιTensorObj ((E.mapHomologicalComplex (.up ℤ)).obj P)
    ((HomologicalComplex.single _ (.up ℤ) 0).obj N) i 0 (i + 0) rfl).val.app V
          ((tensorObjIsoSheafification (R := S) (((E.mapHomologicalComplex (.up ℤ)).obj P).X i)
            (((HomologicalComplex.single _ (.up ℤ) 0).obj N).X 0)).inv.val.app V
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
                ((((E.mapHomologicalComplex (.up ℤ)).obj P).X i).val ⊗
                  (((HomologicalComplex.single _ (.up ℤ) 0).obj N).X 0).val)).app V
                  (((eqToHom (hobj (P.X i)).symm).val.app V
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
              (changeOfRingsPresheaf φ (P.X i))).app V
                (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x))) ⊗ₜ[S.obj.obj V]
                  ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv.val.app V n)))))

/-- Both generator formulas with the sheafification units and summand inclusions.
Scalar extension uses s tensor x for the paper's x tensor s.
Source: Stacks 03EK and 03CY (blueprint: lem-trf-site-balanced-tensor-chain). -/
def Normalized (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (N : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    (a : source φ P N ≅ target φ E P N) : Prop :=
  (∀ (i : ℤ) (V : Cᵒᵖ) (x : (P.X i).val.obj V) (n : N.val.obj V),
    (a.hom.f (i + 0)).val.app V (sourceSection φ P N i V x n) =
      targetSection φ E hobj P N i V x 1 n) ∧
  (∀ (i : ℤ) (V : Cᵒᵖ) (x : (P.X i).val.obj V) (s : S.obj.obj V) (n : N.val.obj V),
    (a.inv.f (i + 0)).val.app V (targetSection φ E hobj P N i V x s n) =
      sourceSection φ P N i V x (s • n))

/-- The unique balanced chain comparison, simultaneously natural in chain maps
and module maps, compatible with the actual tensor homotopies, with scalar action through N.

Source: Stacks 03EK, 03CY, 0GMW; Homology 012Z and the equation preceding 0113.
(blueprint: lem-trf-site-balanced-tensor-chain)

Proof plan:
1. Give the presheaf P(i) tensor UN the S-action through N. Balancing uses
commutativity of S; restrictions respect that action. Module sheafification extends it
uniquely (def-weil-presheaf-modules-sheafification), retaining the actual R tensor.
2. The forward presheaf pairing sends x tensor n to eta(x tensor 1) tensor n.
It is balanced, S-linear and restriction compatible, so sheafifies to a sheaf morphism.
3. The inverse pairing sends (x tensor s, n) to eta(x tensor sn). It extends through
scalar-extension sheafification by lem-pc-sites-module-sheafification-bilinear-extension,
then through the tensor by lem-pc-sites-sheaf-tensor-bilinear-universal.
4. Both composites are identities on the original pure tensors. Tensor generation,
bilinear-extension uniqueness and module-sheafification uniqueness extend the identities
and show that the displayed normalization determines the comparison uniquely.
5. For arbitrary module maps u and v, both naturality composites send x tensor n to
eta(u(x) tensor 1) tensor v(n). The same uniqueness proves their equality.
6. With N in degree zero the total has only the (i,0) nonzero summand in degree i.
All other summands vanish, by the tensor universal property with a zero factor.
Thus its differential is d_P tensor 1; the second signed differential is zero.
Apply step 5 to d_P to obtain a chain isomorphism, and to chain-map components for
simultaneous naturality. No boundedness is needed for this single nonzero summand.
7. Apply step 5 also to h(i): P(i) -> P'(i-1), and v: N -> N'. Additivity transports
the equation f-g=d h+h d to both tensor totals. These are precisely Mathlib's induced
tensor homotopies; the displayed equality intertwines them. Hence the same family
descends to the homotopy category. No step uses flatness or K-flatness. -/
theorem existsUnique_balancedTensorChain
    (hmap : ∀ {M M' : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)} (f : M ⟶ M'),
      E.map f = eqToHom (hobj M) ≫ changeOfRingsHom φ M f ≫ eqToHom (hobj M').symm) :
    ∃ a : ∀ (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (N : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)),
      source φ P N ≅ target φ E P N,
      (∀ P N, Normalized φ E hobj P N (a P N)) ∧
      (∀ (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (N : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
        (b : source φ P N ≅ target φ E P N),
        Normalized φ E hobj P N b → b = a P N) ∧
      (∀ (P P' : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
          (N N' : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) (f : P ⟶ P') (g : N ⟶ N'),
        HomologicalComplex.tensorHom f
            (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map
              φ)).mapHomologicalComplex (.up ℤ)).map ((HomologicalComplex.single _ (.up ℤ) 0).map
                g)) ≫ (a P' N').hom =
          (a P N).hom ≫ ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map
            φ)).mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.tensorHom ((E.mapHomologicalComplex (.up ℤ)).map f)
              ((HomologicalComplex.single _ (.up ℤ) 0).map g))) ∧
      (∀ (P P' : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
          (N N' : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) (f f' : P ⟶ P') (h :
        Homotopy f f') (g : N ⟶ N')
          (i j : ℤ),
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h
          (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map
            φ)).mapHomologicalComplex (.up ℤ)).map ((HomologicalComplex.single _ (.up ℤ) 0).map g))
          (curriedTensor _) (.up ℤ)).hom i j ≫ (a P' N').hom.f j =
        (a P N).hom.f i ≫
          ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomotopy
            (HomologicalComplex.mapBifunctorMapHomotopy₁ (E.mapHomotopy h)
              ((HomologicalComplex.single _ (.up ℤ) 0).map g) (curriedTensor _) (.up ℤ))).hom i j) ∧
      (∀ (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (N : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) (i : ℤ),
        ∃ (H : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
          (c : (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj H ≅
            (source φ P N).X (i + 0))
          (d : H ≅ (HomologicalComplex.tensorObj ((E.mapHomologicalComplex (.up ℤ)).obj P)
            ((HomologicalComplex.single _ (.up ℤ) 0).obj N)).X (i + 0)),
          c.hom ≫ (a P N).hom.f (i + 0) = (restrictScalars ((sheafCompose J (forget₂ CommRingCat
            RingCat)).map φ)).map d.hom ∧
          ∀ (V : Cᵒᵖ) (s : S.obj.obj V) (x : (P.X i).val.obj V) (n : N.val.obj V),
            c.hom.val.app V (s • @id (H.val.obj V)
              (c.inv.val.app V (sourceSection φ P N i V x n))) =
              sourceSection φ P N i V x (s • n)) := by
  sorry

end BalancedTensorChain
end SheafOfModules
