/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Closed algebraic subspaces, quotient modules and arbitrary pullback

Source: Stacks Project, Morphisms of Spaces, Tag 03MB, lemma-closed-immersion-ideals,
and the paragraph following definition-inverse-image-closed-subspace; Modules on Sites,
Tag 03D7; Categories, Tag 0038
(blueprint: lem-sfb-space-closed-ideal-correspondence).

The quotient is specified by the cokernel universal property of the ideal inclusion.
All comparisons are normalized by their quotient maps. The identity and composition
comparisons for the specified tensor pullbacks are normalized on chart tensors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Closed subspaces correspond to quasi-coherent ideals. Their structure modules are the
quotients, and arbitrary tensor pullback gives the quotient by the image ideal, preserving
units, identity pullback and successive pullbacks.
Source: Stacks Project, Tag 03MB and the inverse-image paragraph following it; Tags 03D7
and 0038 (blueprint: lem-sfb-space-closed-ideal-correspondence).

Proof:
1. Apply lem-sfb-space-ideal-closed-subspace-correspondence. It supplies the bijection,
the kernel and surjectivity of each structure map, and the image-ideal description of
any base-changed closed subspace. A surjection with this kernel induces the unique
isomorphism from the cokernel of the ideal inclusion carrying its projection to the
structure map. Locally, a class of a function maps to its image; different lifts differ
by the kernel, so this is well-defined and invertible.
2. Regard the quotient as the coequalizer of the ideal inclusion and zero. The adjunction
of def-trf-space-etale-module-functors and lem-weil-pbc-left-adjoint-preserves-colimits
show that tensor pullback preserves this coequalizer. By
lem-trf-space-chart-adjunction-tensor-realization and def-pur-sheaf-tensor-product,
pullback of the structure module is the structure module, with b tensor a sent to
b times p-sharp(a). Thus the pulled-back coequalizer is the quotient by the image of
the pulled-back ideal. This uses right exactness, without asserting that pullback
preserves the ideal injection. The two quotient descriptions give the unique beta
carrying the pulled-back quotient map to the structure quotient map.
3. The local tensor formula sends b tensor the image of 1 to the image of b, so preserves
the algebra units. The tensor-composition comparison sends a tensor (b tensor m) to
a times r-sharp(b) tensor m, and identity pullback sends b tensor m to bm with the
appropriate restriction. These are the unit-normalized comparisons of
lem-trf-space-chart-adjunction-tensor-realization. The successive beta maps and the
single beta map therefore agree on local lifted tensors. Equivalently, their composites
with the epimorphic twice-pulled-back quotient map agree, hence they agree. The same
argument gives identity compatibility and uniqueness of beta. -/
theorem closed_ideal_correspondence (S : Scheme.{u}) :
    ∃ (corr : ∀ X : AlgebraicSpace S, ClosedSubspace X ≃ QuasiCoherentIdeal X)
      (unitIso : ∀ (X Y : AlgebraicSpace S) (p : Y ⟶ X),
        (moduleTensorPullback p).obj (SheafOfModules.unit X.structureSheaf) ≅
          SheafOfModules.unit Y.structureSheaf)
      (idIso : ∀ X : AlgebraicSpace S, moduleTensorPullback (𝟙 X) ≅ 𝟭 X.Modules)
      (compIso : ∀ (X Y W : AlgebraicSpace S) (p : Y ⟶ X) (r : W ⟶ Y),
        moduleTensorPullback p ⋙ moduleTensorPullback r ≅ moduleTensorPullback (r ≫ p))
      (beta : ∀ (X Y : AlgebraicSpace S) (p : Y ⟶ X)
        (C : ClosedSubspace X) (D : ClosedSubspace Y)
        (a : (D.val : AlgebraicSpace S) ⟶ (C.val : AlgebraicSpace S))
        (_ : IsPullback a D.val.arrow C.val.arrow p),
          (moduleTensorPullback p).obj
              ((moduleDirectImage C.val.arrow).obj
                (SheafOfModules.unit (C.val : AlgebraicSpace S).structureSheaf)) ≅
            (moduleDirectImage D.val.arrow).obj
              (SheafOfModules.unit (D.val : AlgebraicSpace S).structureSheaf)),
      (∀ (X : AlgebraicSpace S) (C : ClosedSubspace X),
        (corr X C).val = kernelSubobject (moduleStructureMap C.val.arrow) ∧
          ∃ (Q : X.Modules) (q : SheafOfModules.unit X.structureSheaf ⟶ Q)
            (w : (corr X C).val.arrow ≫ q = 0),
            Nonempty (IsColimit (CokernelCofork.ofπ q w)) ∧
              ∃! e : Q ≅ (moduleDirectImage C.val.arrow).obj
                  (SheafOfModules.unit (C.val : AlgebraicSpace S).structureSheaf),
                q ≫ e.hom = moduleStructureMap C.val.arrow) ∧
      (∀ (X Y : AlgebraicSpace S) (p : Y ⟶ X),
        (unitIso X Y p).hom = ((moduleTensorAdjunction p).homEquiv _ _).symm
          (moduleStructureMap p)) ∧
      (∀ (X : AlgebraicSpace S) (M : X.Modules) (V : X.EtaleSite)
          (q : ModuleChart (𝟙 X) V) (a : q.left ⟶ V),
        a.hom.left = q.hom.left →
          ∀ (b : X.structureSheaf.obj.obj (op q.left)) (m : M.val.obj (op V)),
            ((idIso X).hom.app M).val.app (op q.left)
                (moduleTensorSection (𝟙 X) M V q b m) = b • M.val.map a.op m) ∧
      (∀ (X Y W : AlgebraicSpace S) (p : Y ⟶ X) (r : W ⟶ Y)
          (M : X.Modules) (V : X.EtaleSite) (q : ModuleChart p V)
          (t : ModuleChart r q.left)
          (c : (moduleChartTarget (r ≫ p)).obj t.left ⟶ V.obj),
        c.left = t.hom.left ≫ q.hom.left →
          ∀ (a : W.structureSheaf.obj.obj (op t.left))
            (b : Y.structureSheaf.obj.obj (op q.left)) (m : M.val.obj (op V)),
            ((compIso X Y W p r).hom.app M).val.app (op t.left)
                (moduleTensorSection r ((moduleTensorPullback p).obj M) q.left t a
                  (moduleTensorSection p M V q b m)) =
              moduleTensorSection (r ≫ p) M V (CostructuredArrow.mk c)
                (a * moduleChartScalar r q.left t b) m) ∧
      (∀ (X Y : AlgebraicSpace S) (p : Y ⟶ X) (C : ClosedSubspace X),
        ∃ (D : ClosedSubspace Y)
          (a : (D.val : AlgebraicSpace S) ⟶ (C.val : AlgebraicSpace S)),
          IsPullback a D.val.arrow C.val.arrow p) ∧
      (∀ (X Y : AlgebraicSpace S) (p : Y ⟶ X)
          (C : ClosedSubspace X) (D : ClosedSubspace Y)
          (a : (D.val : AlgebraicSpace S) ⟶ (C.val : AlgebraicSpace S))
          (h : IsPullback a D.val.arrow C.val.arrow p),
        (∃ q : (moduleTensorPullback p).obj ((corr X C).val : X.Modules) ⟶
            ((corr Y D).val : Y.Modules),
          Epi q ∧ q ≫ (corr Y D).val.arrow = idealTensorMap p (corr X C)) ∧
          (moduleTensorPullback p).map (moduleStructureMap C.val.arrow) ≫
              (beta X Y p C D a h).hom =
            (unitIso X Y p).hom ≫ moduleStructureMap D.val.arrow ∧
          (∀ e : (moduleTensorPullback p).obj
                ((moduleDirectImage C.val.arrow).obj
                  (SheafOfModules.unit (C.val : AlgebraicSpace S).structureSheaf)) ≅
              (moduleDirectImage D.val.arrow).obj
                (SheafOfModules.unit (D.val : AlgebraicSpace S).structureSheaf),
            (moduleTensorPullback p).map (moduleStructureMap C.val.arrow) ≫ e.hom =
                (unitIso X Y p).hom ≫ moduleStructureMap D.val.arrow →
              e = beta X Y p C D a h) ∧
          ∀ (V : X.EtaleSite) (q : ModuleChart p V)
            (b : Y.structureSheaf.obj.obj (op q.left)),
            (beta X Y p C D a h).hom.val.app (op q.left)
                (moduleTensorSection p
                  ((moduleDirectImage C.val.arrow).obj
                    (SheafOfModules.unit (C.val : AlgebraicSpace S).structureSheaf)) V q b
                  ((moduleStructureMap C.val.arrow).val.app (op V)
                    (1 : X.structureSheaf.obj.obj (op V)))) =
              (moduleStructureMap D.val.arrow).val.app (op q.left) b) ∧
      (∀ (X : AlgebraicSpace S) (C : ClosedSubspace X),
        beta X X (𝟙 X) C C (𝟙 _) (IsPullback.id_horiz C.val.arrow) =
          (idIso X).app ((moduleDirectImage C.val.arrow).obj
            (SheafOfModules.unit (C.val : AlgebraicSpace S).structureSheaf))) ∧
      (∀ (X Y W : AlgebraicSpace S) (p : Y ⟶ X) (r : W ⟶ Y)
          (C : ClosedSubspace X) (D : ClosedSubspace Y) (E : ClosedSubspace W)
          (a : (D.val : AlgebraicSpace S) ⟶ (C.val : AlgebraicSpace S))
          (b : (E.val : AlgebraicSpace S) ⟶ (D.val : AlgebraicSpace S))
          (h : IsPullback a D.val.arrow C.val.arrow p)
          (k : IsPullback b E.val.arrow D.val.arrow r),
        (moduleTensorPullback r).map (beta X Y p C D a h).hom ≫
            (beta Y W r D E b k).hom =
          ((compIso X Y W p r).hom.app
              ((moduleDirectImage C.val.arrow).obj
                (SheafOfModules.unit (C.val : AlgebraicSpace S).structureSheaf))) ≫
            (beta X W (r ≫ p) C E (b ≫ a) (k.paste_horiz h)).hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
