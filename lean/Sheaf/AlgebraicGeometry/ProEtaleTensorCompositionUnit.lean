/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-!
# The explicit pro-etale tensor comparison and its adjunction units

Source: Stacks Project, Modules on Sites, Tag 03D3, lemma-adjoint-push-pull-modules;
Sites, Tag 03CB, lemma-composition-morphisms-sites; Categories, Tag 0B65
(blueprint: lem-sf-proetale-tensor-composition-unit).

The generator formulas use the coprojections of the inverse-image colimits, followed by
sheafification. All test objects and all indexing arrows are quantified. Thus the formulas
specify the tensor maps before using the adjunction-unit equation to characterize them.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The local tensor generator `m ⊗ r`, indexed by `p : T ⟶ B_f U`.
The specified module adjunction sends `m` to the sheafification of `m ⊗ 1`;
restriction along `p`, followed by multiplication by `r`, is the general generator.
This uses the uniquely tensor-normalized adjunction, not an arbitrary adjunction.
Source: Stacks, Tag 03D3 and the inverse-image colimit of Sites, Tag 00VC
(blueprint: lem-sf-proetale-tensor-composition-unit). -/
def proEtalePullbackTensorGenerator {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R) (U : Y.ProEt) (T : X.ProEt)
    (p : T ⟶ (proEtaleBaseChange f).obj U)
    (m : M.val.obj (op U)) (r : S.obj.obj (op T)) :
    ((proEtaleRingModulePullback f R S c).obj M).val.obj (op T) :=
  r • (((proEtaleRingModulePullback f R S c).obj M).val.map p.op
    (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (op U) m))

/-- The image of a local scalar in the source coefficient sheaf: apply the ring map
adjoint to `c`, then restrict along the inverse-image index arrow. Under the canonical
inverse-image identifications this is `c(a)`.
Source: Stacks, Tag 03D3 and Sites, Tag 00VC
(blueprint: lem-sf-proetale-tensor-composition-unit). -/
def proEtalePullbackTensorScalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (U : Y.ProEt) (T : X.ProEt) (p : T ⟶ (proEtaleBaseChange f).obj U)
    (a : R.obj.obj (op U)) : S.obj.obj (op T) :=
  (S.obj.map p.op).hom
    (((proEtaleRingDirectImageMap f R S c).hom.app (op U)).hom a)

/-- The tensor formulas define inverse natural module maps, preserving the specified
composite adjunction unit, and uniquely characterized by that unit equation.
Source: Stacks, Tags 03D3, 03CB and 0B65; the explicit tensor calculation is the agent
deduction recorded in the DAG (blueprint: lem-sf-proetale-tensor-composition-unit).

The equality `hc_hk` only names the prescribed composite coefficient identification.
`Over.pullbackComp.hom` goes from composite base change to iterated base change;
its inverse is the paper's `q`. The two generator clauses are respectively
`(m ⊗ a) ⊗ b ↦ m ⊗ c_h(a)b` and `m ⊗ b ↦ (m ⊗ 1) ⊗ b`.
The colimit and sheafification universal properties make these clauses equivalent to
those formulas for arbitrary local inverse-image sections: one can check maps on every
indexing coprojection, and pure tensors generate the sectionwise tensor products.

Proof:
1. Fibre-product universality gives `q` and its inverse, with naturality by uniqueness.
Apply siteMorphism_composition on the compatible small models and transport along `q`.
Its adjunction-compatible inverse-image comparison gives the sheaf-unit identity.
2. By siteInverseImage_tensor and its coherence, inverse image preserves tensors and
colimits, hence their relative-tensor coequalizers. With A = h⁻¹k⁻¹R_V, B = h⁻¹R_W,
C = R_Z, alpha = h⁻¹c_k and beta = c_h, the iterated pullback is
(N tensor_A B) tensor_B C. Send (m tensor a) tensor b to m tensor beta(a)b.
A-balancing follows from beta(alpha(r)a) = beta(alpha(r))beta(a); B-balancing follows
from multiplicativity of beta. The inverse inserts 1 in B. Its A-balancing follows
by moving alpha(r) across the outer tensor. Both composites are identities by balancing.
The formulas commute with restrictions and maps of M, so sheafification gives t and
its inverse with the two stated generator formulas.
3. The module-operation definition fixes rho_f and the tensor-normalized adjunction.
Apply the sheaf-unit identity to R_V and use naturality with c_k, then c_h, and hc_hk.
It gives d rho_hk = k_*(rho_h) rho_k, so restriction along q and q⁻¹ is linear and
natural, giving d. Adjunction.comp gives the successive-unit composite displayed below.
4. On every test section m, the successive units insert 1 twice. The forward tensor
formula multiplies c_h(1) by 1, so the sheaf-unit identity proves the displayed equation.
Finally unit_conjugateEquiv_symm and the bijective adjunction Hom correspondence give
uniqueness among all natural transformations, not just among isomorphisms. -/
theorem proEtale_tensor_composition_unit
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (R_V : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (R_W : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (R_Z : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c_k : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj R_V ≅ R_W)
    (c_h : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R_W ≅ R_Z)
    (c_hk : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj R_V ≅ R_Z)
    (hc_hk : c_hk = (proEtaleRingInverseImageComp h k).app R_V ≪≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso c_k ≪≫ c_h) :
    ∃ (d : proEtaleRingModuleDirectImage (h ≫ k) R_V R_Z c_hk ≅
          proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
            proEtaleRingModuleDirectImage k R_V R_W c_k)
      (t : proEtaleRingModulePullback k R_V R_W c_k ⋙
          proEtaleRingModulePullback h R_W R_Z c_h ≅
            proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk),
      (∀ (N : proEtaleRingModules Z R_Z) (U : V.ProEt)
        (m : ((proEtaleRingModuleDirectImage (h ≫ k) R_V R_Z c_hk).obj N).val.obj
          (op U)),
        (d.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackComp h k).inv.app U).op m) ∧
      (∀ (M : proEtaleRingModules V R_V) (U : V.ProEt) (T : W.ProEt) (P : Z.ProEt)
        (p : T ⟶ (proEtaleBaseChange k).obj U)
        (q : P ⟶ (proEtaleBaseChange h).obj T)
        (m : M.val.obj (op U)) (a : R_W.obj.obj (op T)) (b : R_Z.obj.obj (op P)),
        (t.hom.app M).val.app (op P)
          (proEtalePullbackTensorGenerator h R_W R_Z c_h
            ((proEtaleRingModulePullback k R_V R_W c_k).obj M) T P q
            (proEtalePullbackTensorGenerator k R_V R_W c_k M U T p m a) b) =
          proEtalePullbackTensorGenerator (h ≫ k) R_V R_Z c_hk M U P
            (q ≫ (proEtaleBaseChange h).map p ≫
              (MorphismProperty.Over.pullbackComp h k).inv.app U) m
            (proEtalePullbackTensorScalar h R_W R_Z c_h T P q a * b)) ∧
      (∀ (M : proEtaleRingModules V R_V) (U : V.ProEt) (P : Z.ProEt)
        (p : P ⟶ (proEtaleBaseChange (h ≫ k)).obj U)
        (m : M.val.obj (op U)) (b : R_Z.obj.obj (op P)),
        (t.inv.app M).val.app (op P)
          (proEtalePullbackTensorGenerator (h ≫ k) R_V R_Z c_hk M U P p m b) =
          proEtalePullbackTensorGenerator h R_W R_Z c_h
            ((proEtaleRingModulePullback k R_V R_W c_k).obj M)
            ((proEtaleBaseChange k).obj U) P
            (p ≫ (MorphismProperty.Over.pullbackComp h k).hom.app U)
            (proEtalePullbackTensorGenerator k R_V R_W c_k M U
              ((proEtaleBaseChange k).obj U) (𝟙 _) m 1) b) ∧
      (∀ M : proEtaleRingModules V R_V,
        (proEtaleRingModuleAdjunction k R_V R_W c_k).unit.app M ≫
          (proEtaleRingModuleDirectImage k R_V R_W c_k).map
            ((proEtaleRingModuleAdjunction h R_W R_Z c_h).unit.app
              ((proEtaleRingModulePullback k R_V R_W c_k).obj M)) ≫
          (proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
            proEtaleRingModuleDirectImage k R_V R_W c_k).map (t.hom.app M) =
        (proEtaleRingModuleAdjunction (h ≫ k) R_V R_Z c_hk).unit.app M ≫
          d.hom.app ((proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk).obj M)) ∧
      (∀ t' : proEtaleRingModulePullback k R_V R_W c_k ⋙
          proEtaleRingModulePullback h R_W R_Z c_h ⟶
            proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk,
        (∀ M : proEtaleRingModules V R_V,
          ((proEtaleRingModuleAdjunction k R_V R_W c_k).comp
            (proEtaleRingModuleAdjunction h R_W R_Z c_h)).unit.app M ≫
            (proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
              proEtaleRingModuleDirectImage k R_V R_W c_k).map (t'.app M) =
          (proEtaleRingModuleAdjunction (h ≫ k) R_V R_Z c_hk).unit.app M ≫
            d.hom.app ((proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk).obj M)) →
        t' = t.hom) := by
  sorry

end AlgebraicGeometry.Scheme
