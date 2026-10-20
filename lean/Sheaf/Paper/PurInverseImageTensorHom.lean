module

public import Sheaf.Paper.PurInverseImageTensorHomDefinitions
import Sheaf.Paper.PurInverseImageTensorComparison
import Sheaf.Paper.PurInverseImageHomComparison
import Sheaf.Paper.PurInverseImageScalarComparison
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.CategoryTheory.Limits.HasLimits

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
attribute [local irreducible] AlgebraicGeometry.Scheme.proEtaleModuleInverseImage
  Functor.sheafPullbackConstruction.sheafPullback
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

namespace AlgebraicGeometry.Scheme

private instance commRingSheafify (Z : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology Z) CommRingCat.{u + 1} := inferInstance
private instance abelianSheafify (Z : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology Z) AddCommGrpCat.{u + 1} := inferInstance

private theorem positiveTensorPowerMixed_comparison
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (σ : ∀ (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)),
      (proEtaleModuleInverseImage g O).obj
          ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} G).obj F) ≅
        (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
          ((proEtaleModuleInverseImage g O).obj G)).obj
          ((proEtaleModuleInverseImage g O).obj F))
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)) :
    ∀ (m : ℕ) (hm : 0 < m),
      Nonempty ((proEtaleModuleInverseImage g O).obj
          (positiveTensorPowerMixed O F m hm) ≅
        positiveTensorPowerMixed
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O)
          ((proEtaleModuleInverseImage g O).obj F) m hm) := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero => intro hm; exact False.elim (Nat.not_lt_zero 0 hm)
  | one => intro _; exact ⟨Iso.refl _⟩
  | more n _ ih =>
    intro hm
    obtain ⟨e⟩ := ih (Nat.succ_pos n)
    exact ⟨σ (positiveTensorPowerMixed O F (n + 1) (Nat.succ_pos n)) F ≪≫
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        ((proEtaleModuleInverseImage g O).obj F)).mapIso e⟩

private theorem inverseImage_preservesTowers
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    PreservesLimitsOfShape ℕᵒᵖ (proEtaleModuleInverseImage g O) := by
  obtain ⟨_, _, _, h, _⟩ := (proEtale_immersion_inverseImage_preservesLimits g).2.2 O
  let : PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleModuleInverseImage g O) := h
  have : PreservesLimitsOfSize.{0, 0} (proEtaleModuleInverseImage g O) :=
    preservesSmallestLimits_of_preservesLimits (proEtaleModuleInverseImage g O)
  infer_instance

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
  exact ⟨Classical.choose (purInverseImageTensorComparison g O),
    Classical.choose (purInverseImageHomComparison g O),
    (Classical.choose_spec (purInverseImageTensorComparison g O)).1,
    (Classical.choose_spec (purInverseImageHomComparison g O)).1,
    (Classical.choose_spec (purInverseImageTensorComparison g O)).2,
    (fun F G G' b V s t =>
      (Classical.choose_spec (purInverseImageTensorComparison g O)).1 F G' V s
        (b.val.app (op V) t)),
    (Classical.choose_spec (purInverseImageHomComparison g O)).2,
    positiveTensorPowerMixed_comparison g O
      (Classical.choose (purInverseImageTensorComparison g O)),
    purInverseImageScalarComparison g O,
    by
      let : PreservesLimitsOfShape ℕᵒᵖ (proEtaleModuleInverseImage g O) :=
        inverseImage_preservesTowers g O
      intro D
      exact ⟨preservesLimitIso (proEtaleModuleInverseImage g O) D,
        fun n => preservesLimitIso_hom_π (proEtaleModuleInverseImage g O) D n⟩⟩

end AlgebraicGeometry.Scheme
