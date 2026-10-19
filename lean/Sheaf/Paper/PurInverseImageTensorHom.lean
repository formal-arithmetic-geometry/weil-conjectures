module



public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Iso
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage

/-!
# Inverse image, tensor products, and internal Hom on the small pro-etale site

Source: Stacks Project, `sites-modules.tex`, Lemma 18.26.2 (Tag 03EL),
Remark 0GMX, and Lemma 0GN2 (blueprint: lem-pur-isomorphism-inverse-image-tensor-hom).

The statement records the canonical tensor, internal-Hom, positive tensor-power,
coefficient-extension, and inverse-limit comparisons for the explicitly constructed
pro-etale module inverse image.
-/


@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- Extension of scalars after inverse image, for the coefficient-extension clause. Source:
Stacks Tag 03EK (blueprint: lem-pur-isomorphism-inverse-image-tensor-hom). -/
noncomputable abbrev inverseImageScalarExtension
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (O O' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (α : O ⟶ O')
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)) :
    SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O')) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (J := ProEt.topology X)
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map α)
    ((proEtaleModuleInverseImage g O).obj F)

/-- Positive tensor powers in the mixed-universe module category, using the sectionwise tensor
product followed by sheafification.
Source: Stacks Tag 03EK (blueprint: lem-pur-isomorphism-inverse-image-tensor-hom). -/
noncomputable def positiveTensorPowerMixed {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    (n : ℕ) → 0 < n → SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  | 0, h => False.elim (Nat.not_lt_zero 0 h)
  | 1, _ => M
  | n + 2, _ =>
      (show SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) from
        (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} M).obj
          (positiveTensorPowerMixed R M (n + 1) (Nat.succ_pos n)))

/-- A pure tensor followed by module sheafification. Source: Stacks Tag 03EK
(blueprint: lem-pur-isomorphism-inverse-image-tensor-hom). -/
noncomputable def purTensorSection {X : AlgebraicGeometry.Scheme.{u}}
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    (V : X.ProEt) (s : F.val.obj (op V)) (t : G.val.obj (op V)) :
    ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} G).obj F).val.obj
      (op V) :=
  (CategoryTheory.toSheafify (ProEt.topology X)
    (SheafOfModules.siteTensorPresheaf F.val G.val).presheaf).app (op V)
      (s ⊗ₜ[O.obj.obj (op V)] t)

/-- The actual module inverse-image unit on sections, using the recorded small model.
Source: Stacks Tags 03D2 and 09A5
(blueprint: lem-pur-isomorphism-inverse-image-tensor-hom). -/
noncomputable def purInverseImageSection {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    (V : Y.ProEt) (s : F.val.obj (op V)) :
    ((proEtaleModuleInverseImage g O).obj F).val.obj
      (op ((proEtaleBaseChange g).obj V)) :=
  (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit g O)).unit.app
    ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)).obj F)).val.app
        (op (AsSmall.up.obj V))) s

/-- Pure scalar-extension sections, in the recorded mixed-universe construction.
Source: Stacks Tag 03EK (blueprint: lem-pur-isomorphism-inverse-image-tensor-hom). -/
noncomputable def purScalarSection {X : AlgebraicGeometry.Scheme.{u}}
    (O O' : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (α : O ⟶ O')
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    (V : X.ProEt) (b : O'.obj.obj (op V)) (s : F.val.obj (op V)) :
    (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α F).val.obj
      (op V) :=
  (CategoryTheory.toSheafify (ProEt.topology X)
    (SheafOfModules.changeOfRingsPresheafOfUniverses α F).presheaf).app (op V)
      (b ⊗ₜ[O.obj.obj (op V), (α.hom.app (op V)).hom] s)

/-- Inverse image along a scheme isomorphism preserves tensor products and internal Hom,
with the normalized functoriality, tensor-power, scalar-extension, and inverse-limit
comparisons stated in the blueprint. Source: Stacks Project, Tags 03EL, 0GMX, and 0GN2
(blueprint: lem-pur-isomorphism-inverse-image-tensor-hom).

Proof steps: (1) use the pro-etale site equivalence for an isomorphism and reindex module
sheaves; (2) transport module sheafification across this equivalence; (3) compare the
sectionwise tensor and sheafify; (4) compare internal Hom on equivalent slice sites;
(5) check naturality on pure tensors and slice components; (6) check associativity,
symmetry, units, and iterate the tensor comparison; (7) specialize to scalar extension;
(8) identify inverse limits sectionwise and verify the projections.
The two local normalization equations characterize the comparisons. In particular the
associativity, symmetry and unit diagrams commute: on nested pure tensors their paths
are respectively `s ⊗ (t ⊗ h)`, `t ⊗ s`, and scalar multiplication. Nested pure tensors
locally generate by `lem-weil-pbc-site-sheafification-iso-locally-bijective`, as in
step 3 of the node. Thus these normalization equations encode all the tensor coherence
clauses without choosing additional associators. The scalar comparison is likewise
normalized on every pure scalar tensor. -/
theorem inverseImage_tensor_hom_iso
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    ∃ σ : ∀ (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)),
      (proEtaleModuleInverseImage g O).obj
          ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} G).obj F) ≅
        (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
          ((proEtaleModuleInverseImage g O).obj G)).obj
          ((proEtaleModuleInverseImage g O).obj F),
      ∃ η : ∀ (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)),
        (proEtaleModuleInverseImage g O).obj
            (SheafOfModules.homObj (R := O) F G) ≅
          SheafOfModules.homObj
            (R := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O)
            ((proEtaleModuleInverseImage g O).obj F)
            ((proEtaleModuleInverseImage g O).obj G),
        (∀ (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
            (V : Y.ProEt) (s : F.val.obj (op V)) (t : G.val.obj (op V)),
          (σ F G).hom.val.app (op ((proEtaleBaseChange g).obj V))
            (purInverseImageSection g O _ V (purTensorSection O F G V s t)) =
          purTensorSection ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O)
            ((proEtaleModuleInverseImage g O).obj F)
            ((proEtaleModuleInverseImage g O).obj G) ((proEtaleBaseChange g).obj V)
            (purInverseImageSection g O F V s) (purInverseImageSection g O G V t)) ∧
        (∀ (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
            (V W : Y.ProEt) (a : W ⟶ V)
            (φ : (SheafOfModules.homObj (R := O) F G).val.obj (op V))
            (s : F.val.obj (op W)),
          ((η F G).hom.val.app (op ((proEtaleBaseChange g).obj V))
            (purInverseImageSection g O _ V φ)).app
              (op (Over.mk ((proEtaleBaseChange g).map a)))
                (purInverseImageSection g O F W s) =
          purInverseImageSection g O G W (φ.app (op (Over.mk a)) s)) ∧
        (∀ (F G F' : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
            (a : F ⟶ F'),
            (proEtaleModuleInverseImage g O).map
                ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} G).map a) ≫
              (σ F' G).hom =
            (σ F G).hom ≫
              (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
                ((proEtaleModuleInverseImage g O).obj G)).map
                ((proEtaleModuleInverseImage g O).map a)) ∧
        (∀ (F G G' : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
            (b : G ⟶ G') (V : Y.ProEt) (s : F.val.obj (op V)) (t : G.val.obj (op V)),
          (σ F G').hom.val.app (op ((proEtaleBaseChange g).obj V))
            (purInverseImageSection g O _ V
              (purTensorSection O F G' V s (b.val.app (op V) t))) =
          purTensorSection ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O)
            ((proEtaleModuleInverseImage g O).obj F)
            ((proEtaleModuleInverseImage g O).obj G') ((proEtaleBaseChange g).obj V)
            (purInverseImageSection g O F V s)
            (purInverseImageSection g O G' V (b.val.app (op V) t))) ∧
        (∀ (F F' G G' : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
            (a : F' ⟶ F) (b : G ⟶ G'),
            (proEtaleModuleInverseImage g O).map
                (SheafOfModules.homObjMap (R := O) a b) ≫
              (η F' G').hom =
            (η F G).hom ≫
              SheafOfModules.homObjMap
                (R := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O)
                ((proEtaleModuleInverseImage g O).map a)
                ((proEtaleModuleInverseImage g O).map b)) ∧
        (∀ (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
            (m : ℕ) (hm : 0 < m),
          Nonempty ((proEtaleModuleInverseImage g O).obj
              (positiveTensorPowerMixed O F m hm) ≅
            positiveTensorPowerMixed
              ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O)
              ((proEtaleModuleInverseImage g O).obj F) m hm)) ∧
        (∀ (O' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
            (α : O ⟶ O')
            (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)),
          ∃ e : (proEtaleModuleInverseImage g O').obj
              (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α F) ≅
            inverseImageScalarExtension g O O' α F,
            ∀ (V : Y.ProEt) (b : O'.obj.obj (op V)) (s : F.val.obj (op V)),
              e.hom.val.app (op ((proEtaleBaseChange g).obj V))
                (purInverseImageSection g O' _ V (purScalarSection O O' α F V b s)) =
              purScalarSection
                ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O)
                ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O')
                ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map α)
                ((proEtaleModuleInverseImage g O).obj F) ((proEtaleBaseChange g).obj V)
                (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O').hom.app
                  (op V) b) (purInverseImageSection g O F V s)) ∧
        (∀ (D : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)),
          ∃ e :
              (proEtaleModuleInverseImage g O).obj (limit D) ≅
                limit (D ⋙ proEtaleModuleInverseImage g O),
            ∀ (n : ℕᵒᵖ),
              e.hom ≫ (limit.π (D ⋙ proEtaleModuleInverseImage g O) n) =
                (proEtaleModuleInverseImage g O).map (limit.π D n)) := by
  sorry

end AlgebraicGeometry.Scheme
