# SheafOfModules.StrictRingSystem and the SystemLevelLeftExtension interface

## Reason

Prove `systemLevelLeftExtensionTheory` without a circular import: ordinary and derived
construction modules need the strict-system category and the existing theory interface,
whereas the final existence proof needs those construction modules. Move the unchanged
interface to `SystemLevelLeftExtensionBasic`, and the coefficient-only interface to
`SystemScalarModel`. The original module publicly imports the foundation, which publicly
reexports the scalar interface. This is a logical separation of definitions from the
proof that constructs their instances; it does not split a file to evade a compile limit.

All 50 old named public declaration signatures, including every structure field, are
identical after whitespace normalization. No target, hypothesis, universe or conclusion
changes. The strict system, scalar restriction, selected-index and derived-extension data
remain their original constructions. The componentwise colimit proof is generalized from
finite diagrams to arbitrary diagrams with the required coefficient colimits, giving
public colimit and evaluation-preservation theorems. New componentwise detection lemmas
expose that existing category. An explicit canonical `systemTensorCoherence` constructor
fixes adjoint-uniqueness units and associators for the final coherence calculations.
No file under `WeilConjectures` is changed, deleted, or replaced with a hole.

## Old

The old module's public imports were:

```lean
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Order.Category.Preord
public import Mathlib.Order.WellFounded
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
```

Verbatim original public signatures and complete structure records (their module-variable
context remains the original one):

```lean
abbrev systemLevel (n : ℕ)

abbrev systemRestriction {m n : ℕ} (h : m ≤ n) : systemLevel B m ⥤ systemLevel B n

structure StrictRingSystem where
  level : ∀ n : ℕ, systemLevel B n
  transition : ∀ {m n : ℕ} (h : m ≤ n), level n ⟶ (systemRestriction B h).obj (level m)
  identity : ∀ (n : ℕ) (U : Cᵒᵖ) (x : (level n).val.obj U),
    (transition (Nat.le_refl n)).val.app U x = x
  compose : ∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) (U : Cᵒᵖ)
    (x : (level n).val.obj U),
    (transition (h.trans k)).val.app U x =
      (transition h).val.app U ((transition k).val.app U x)

structure StrictRingSystem.Hom (M N : StrictRingSystem B) where
  app : ∀ n : ℕ, M.level n ⟶ N.level n
  comm : ∀ {m n : ℕ} (h : m ≤ n),
    app n ≫ N.transition h = M.transition h ≫ (systemRestriction B h).map (app m)

theorem strictRingSystem_id_comm (M : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) :
    𝟙 (M.level n) ≫ M.transition h =
      M.transition h ≫ (systemRestriction B h).map (𝟙 (M.level m))

theorem strictRingSystem_comp_comm {M N P : StrictRingSystem B}
    (f : M.Hom N) (g : N.Hom P) {m n : ℕ} (h : m ≤ n) :
    (f.app n ≫ g.app n) ≫ P.transition h =
      M.transition h ≫ (systemRestriction B h).map (f.app m ≫ g.app m)

def StrictRingSystem.id (M : StrictRingSystem B) : M.Hom M

def StrictRingSystem.Hom.comp {M N P : StrictRingSystem B} (f : M.Hom N) (g : N.Hom P) :
    M.Hom P

theorem strictRingSystem_category_laws :
    (∀ (M N : StrictRingSystem B) (f : M.Hom N),
      M.id.comp f = f ∧ f.comp N.id = f) ∧
    (∀ (M N P Q : StrictRingSystem B) (f : M.Hom N) (g : N.Hom P) (h : P.Hom Q),
      (f.comp g).comp h = f.comp (g.comp h))

instance strictRingSystemCategory : Category (StrictRingSystem B)

def systemEvaluation (n : ℕ) : StrictRingSystem B ⥤ systemLevel B n

def StrictRingSystem.AbelianNormalized (a : Abelian (StrictRingSystem B)) : Prop

theorem systemScalarRestriction_exact {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    PreservesFiniteLimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) ∧
    PreservesFiniteColimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ))

instance systemScalarRestrictionLimits {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    PreservesFiniteLimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ))

instance systemScalarRestrictionColimits {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    PreservesFiniteColimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ))

theorem strictRingSystem_abelian_exists :
    ∃! a : Abelian (StrictRingSystem B), StrictRingSystem.AbelianNormalized B a

instance strictRingSystemAbelian : Abelian (StrictRingSystem B)

theorem systemEvaluation_exact (n : ℕ) :
    (systemEvaluation B n).Additive ∧ PreservesFiniteLimits (systemEvaluation B n) ∧
      PreservesFiniteColimits (systemEvaluation B n)

instance systemEvaluationAdditive (n : ℕ) : (systemEvaluation B n).Additive

instance systemEvaluationLimits (n : ℕ) : PreservesFiniteLimits (systemEvaluation B n)

instance systemEvaluationColimits (n : ℕ) : PreservesFiniteColimits (systemEvaluation B n)

instance systemRingHasDerived (R : Sheaf J CommRingCat.{w}) :
    HasDerivedCategory (ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))

instance strictRingSystemHasDerived : HasDerivedCategory (StrictRingSystem B)

abbrev derivedSystemEvaluation (n : ℕ)

def selectedSystemRings (r : ℕ ↪o ℕ) : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}

def systemSubsequence (r : ℕ ↪o ℕ) : StrictRingSystem B ⥤
    StrictRingSystem (selectedSystemRings B r)

theorem systemSubsequence_exact (r : ℕ ↪o ℕ) :
    (systemSubsequence B r).Additive ∧ PreservesFiniteLimits (systemSubsequence B r) ∧
      PreservesFiniteColimits (systemSubsequence B r)

instance systemSubsequenceAdditive (r : ℕ ↪o ℕ) : (systemSubsequence B r).Additive

instance systemSubsequenceLimits (r : ℕ ↪o ℕ) : PreservesFiniteLimits (systemSubsequence B r)

instance systemSubsequenceColimits (r : ℕ ↪o ℕ) : PreservesFiniteColimits (systemSubsequence B r)

abbrev derivedSystemSubsequence (r : ℕ ↪o ℕ)

def systemNextSelected (r : ℕ ↪o ℕ) (m : ℕ) : ℕ

theorem systemNextSelected_spec (r : ℕ ↪o ℕ) (m : ℕ) :
    m ≤ r (systemNextSelected r m) ∧
      ∀ i : ℕ, m ≤ r i → systemNextSelected r m ≤ i

theorem systemNextSelected_mono (r : ℕ ↪o ℕ) (m : ℕ) :
    systemNextSelected r m ≤ systemNextSelected r (m + 1)

theorem systemNextSelected_trans (r s : ℕ ↪o ℕ) (m : ℕ) :
    systemNextSelected (s.trans r) m = systemNextSelected s (systemNextSelected r m)

def strictSystemTransition {m n : ℕ} (h : m ≤ n) :
    systemEvaluation B n ⟶ systemEvaluation B m ⋙ systemRestriction B h

structure SystemDerivedLeftExtension where
  ordinary : A ⥤ D
  [additive : ordinary.Additive]
  ordinaryAdj : ordinary ⊣ R
  derived : DerivedCategory A ⥤ DerivedCategory D
  comparison : DerivedCategory.Q ⋙ derived ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : derived.IsLeftDerivedFunctor comparison (HomologicalComplex.quasiIso A (.up ℤ))
  pointwise : Functor.HasPointwiseLeftDerivedFunctor
    (ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso A (.up ℤ))
  computes : ∀ P, resolving P → IsIso (comparison.app P)
  [shift : derived.CommShift ℤ]
  triangulated : derived.IsTriangulated
  adjunction : derived ⊣ R.mapDerivedCategory
  transpose : ∀ (P : CochainComplex A ℤ) (K : CochainComplex D ℤ)
    (f : (ordinary.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      (comparison.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((ordinaryAdj.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
          R.mapDerivedCategoryFactors.inv.app K

def systemModelTmul {R S : Sheaf J CommRingCat.{w}} {φ : R ⟶ S}
    (D : DerivedChangeOfRingsCochainModel φ)
    (P : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (c : S.obj.obj U) (x : P.val.obj U) : (D.E.obj P).val.obj U

structure SystemScalarModel {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) where
  model : DerivedChangeOfRingsCochainModel φ
  ordinaryAdj : model.E ⊣ restrictScalars.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
  unit_normalized : ∀ P U (x : P.val.obj U),
    (ordinaryAdj.unit.app P).val.app U x = systemModelTmul model P U 1 x
  adjunction : model.T ⊣ (restrictScalars.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).mapDerivedCategory
  transpose : ∀ P K (f : (model.E.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      (model.ε.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((ordinaryAdj.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
        (restrictScalars.{w} ((sheafCompose J
          (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).mapDerivedCategoryFactors.inv.app K

abbrev systemLevelKFlat (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ)
    (P : CochainComplex (systemLevel B n) ℤ) : Prop

def systemComponentwiseKFlat (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (P : CochainComplex (StrictRingSystem B) ℤ) : Prop

abbrev SystemScalarAssignment

abbrev systemTensor (S : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n)

abbrev systemDerivedTensor (S : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n)

abbrev systemTensorAdj (S : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n)

abbrev systemDerivedTensorAdj (S : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n)

structure SystemTensorCoherence (S : SystemScalarAssignment (J := J)) where
  ordinaryUnit : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ),
    systemTensor S B (Nat.le_refl n) ≅ 𝟭 (systemLevel B n)
  unit_normalized : ∀ B n P U c x,
    ((ordinaryUnit B n).hom.app P).val.app U
      (systemModelTmul (S (B.map (homOfLE (Nat.le_refl n)).op)).model P U c x) = c • x
  ordinaryAssoc : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {l m n : ℕ}
    (h : l ≤ m) (k : m ≤ n),
    systemTensor S B k ⋙ systemTensor S B h ≅ systemTensor S B (h.trans k)
  assoc_normalized : ∀ B {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) P U c d x,
    ((ordinaryAssoc B h k).hom.app P).val.app U
      (systemModelTmul (S (B.map (homOfLE h).op)).model ((systemTensor S B k).obj P) U c
        (systemModelTmul (S (B.map (homOfLE k).op)).model P U d x)) =
      systemModelTmul (S (B.map (homOfLE (h.trans k)).op)).model P U
        (c * (B.map (homOfLE h).op).hom.app U d) x
  derivedUnit : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ),
    systemDerivedTensor S B (Nat.le_refl n) ≅ 𝟭 (DerivedCategory (systemLevel B n))
  derivedUnit_rep : ∀ B n P, systemLevelKFlat B n P →
    (derivedUnit B n).hom.app (DerivedCategory.Q.obj P) =
      (S (B.map (homOfLE (Nat.le_refl n)).op)).model.ε.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (ordinaryUnit B n) (.up ℤ)).hom.app P)
  derivedAssoc : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {l m n : ℕ}
    (h : l ≤ m) (k : m ≤ n),
    systemDerivedTensor S B k ⋙ systemDerivedTensor S B h ≅
      systemDerivedTensor S B (h.trans k)
  derivedAssoc_rep : ∀ B {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) P,
    systemLevelKFlat B n P →
    (derivedAssoc B h k).hom.app (DerivedCategory.Q.obj P) ≫
      (S (B.map (homOfLE (h.trans k)).op)).model.ε.app P =
    (systemDerivedTensor S B h).map ((S (B.map (homOfLE k).op)).model.ε.app P) ≫
      (S (B.map (homOfLE h).op)).model.ε.app
        (((systemTensor S B k).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (ordinaryAssoc B h k) (.up ℤ)).hom.app P)

theorem systemSelectedTensor_trans (S : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r s : ℕ ↪o ℕ) (m : ℕ)
    (P : DerivedCategory (StrictRingSystem (selectedSystemRings B (s.trans r)))) :
    (systemDerivedTensor S B (systemNextSelected_spec (s.trans r) m).1).obj
        ((derivedSystemEvaluation (selectedSystemRings B (s.trans r))
          (systemNextSelected (s.trans r) m)).obj P) =
      (systemDerivedTensor S B ((systemNextSelected_spec r m).1.trans
          (r.monotone (systemNextSelected_spec s (systemNextSelected r m)).1))).obj
        ((derivedSystemEvaluation (selectedSystemRings B (s.trans r))
          (systemNextSelected s (systemNextSelected r m))).obj P)

structure SystemLevelLeftExtensionTheory where
  scalar : SystemScalarAssignment (J := J)
  tensor : SystemTensorCoherence scalar
  grothendieck : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}),
    IsGrothendieckAbelian.{w} (StrictRingSystem B)
  [coproducts : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}),
    HasCoproducts.{w} (StrictRingSystem B)]
  [derivedCoproducts : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}),
    HasCoproducts.{w} (DerivedCategory (StrictRingSystem B))]
  [levelDerivedCoproducts : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ),
    HasCoproducts.{w} (DerivedCategory (systemLevel B n))]
  evaluationCoproducts : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) n (I : Type w),
    PreservesColimitsOfShape (Discrete I) (systemEvaluation B n)
  derivedEvaluationCoproducts : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) n (I : Type w),
    PreservesColimitsOfShape (Discrete I) (derivedSystemEvaluation B n)
  cohomology : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) n (q : ℤ),
    DerivedCategory.homologyFunctor (StrictRingSystem B) q ⋙ systemEvaluation B n ≅
      derivedSystemEvaluation B n ⋙ DerivedCategory.homologyFunctor (systemLevel B n) q
  detectsIso : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    {M N : DerivedCategory (StrictRingSystem B)} (f : M ⟶ N),
    IsIso f ↔ ∀ n : ℕ, IsIso ((derivedSystemEvaluation B n).map f)
  detectsBounds : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (M : DerivedCategory (StrictRingSystem B)) (q : ℤ),
    (M.IsGE q ↔ ∀ n : ℕ, ((derivedSystemEvaluation B n).obj M).IsGE q) ∧
    (M.IsLE q ↔ ∀ n : ℕ, ((derivedSystemEvaluation B n).obj M).IsLE q)
  single : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ),
    SystemDerivedLeftExtension (systemEvaluation B n) (systemLevelKFlat B n)
  singleBelow : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n),
    (single B n).ordinary ⋙ systemEvaluation B m ≅ systemTensor scalar B h
  singleAbove : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) m n, n < m → ∀ P,
    IsZero ((systemEvaluation B m).obj ((single B n).ordinary.obj P))
  singleTranspose : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n) P M
    (f : (single B n).ordinary.obj P ⟶ M),
    (systemTensorAdj scalar B h).homEquiv P (M.level m)
      ((singleBelow B h).inv.app P ≫ (systemEvaluation B m).map f) =
      (single B n).ordinaryAdj.homEquiv P M f ≫ M.transition h
  singleDerivedBelow : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n),
    (single B n).derived ⋙ derivedSystemEvaluation B m ≅ systemDerivedTensor scalar B h
  singleDerivedAbove : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) m n, n < m → ∀ P,
    IsZero ((derivedSystemEvaluation B m).obj ((single B n).derived.obj P))
  transition : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n),
    derivedSystemEvaluation B n ⟶
      derivedSystemEvaluation B m ⋙ (systemRestriction B h).mapDerivedCategory
  transition_rep : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n) K,
    (transition B h).app (DerivedCategory.Q.obj K) ≫
      (systemRestriction B h).mapDerivedCategory.map
        ((systemEvaluation B m).mapDerivedCategoryFactors.hom.app K) ≫
      (systemRestriction B h).mapDerivedCategoryFactors.hom.app
        (((systemEvaluation B m).mapHomologicalComplex (.up ℤ)).obj K) =
      (systemEvaluation B n).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((strictSystemTransition B h).mapHomologicalComplex (.up ℤ) |>.app K)
  transition_identity : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) n M,
    ((systemDerivedTensorAdj scalar B (Nat.le_refl n)).homEquiv _ _).symm
      ((transition B (Nat.le_refl n)).app M) =
        (tensor.derivedUnit B n).hom.app ((derivedSystemEvaluation B n).obj M)
  singleDerivedTranspose : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n) P M
    (f : (single B n).derived.obj P ⟶ M),
    (systemDerivedTensorAdj scalar B h).homEquiv P ((derivedSystemEvaluation B m).obj M)
      ((singleDerivedBelow B h).inv.app P ≫ (derivedSystemEvaluation B m).map f) =
      (single B n).adjunction.homEquiv P M f ≫ (transition B h).app M
  selected : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r : ℕ ↪o ℕ),
    SystemDerivedLeftExtension (systemSubsequence B r)
      (systemComponentwiseKFlat (selectedSystemRings B r))
  selectedEvaluation : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r n,
    derivedSystemSubsequence B r ⋙ derivedSystemEvaluation (selectedSystemRings B r) n ≅
      derivedSystemEvaluation B (r n)
  selectedEvaluation_rep : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r n K,
    (selectedEvaluation B r n).hom.app (DerivedCategory.Q.obj K) ≫
      (systemEvaluation B (r n)).mapDerivedCategoryFactors.hom.app K =
    (derivedSystemEvaluation (selectedSystemRings B r) n).map
      ((systemSubsequence B r).mapDerivedCategoryFactors.hom.app K) ≫
    (systemEvaluation (selectedSystemRings B r) n).mapDerivedCategoryFactors.hom.app
      (((systemSubsequence B r).mapHomologicalComplex (.up ℤ)).obj K)
  selectedBelow : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r m,
    (selected B r).ordinary ⋙ systemEvaluation B m ≅
      systemEvaluation (selectedSystemRings B r) (systemNextSelected r m) ⋙
        systemTensor scalar B (systemNextSelected_spec r m).1
  selectedTranspose : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r m P M
    (f : (selected B r).ordinary.obj P ⟶ M),
    (systemTensorAdj scalar B (systemNextSelected_spec r m).1).homEquiv
      (P.level (systemNextSelected r m)) (M.level m)
      ((selectedBelow B r m).inv.app P ≫ (systemEvaluation B m).map f) =
    (systemEvaluation (selectedSystemRings B r) (systemNextSelected r m)).map
      ((selected B r).ordinaryAdj.homEquiv P M f) ≫
        M.transition (systemNextSelected_spec r m).1
  selectedDerivedBelow : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r m,
    (selected B r).derived ⋙ derivedSystemEvaluation B m ≅
      derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r m) ⋙
        systemDerivedTensor scalar B (systemNextSelected_spec r m).1
  selectedDerivedTranspose : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r m P M
    (f : (selected B r).derived.obj P ⟶ M),
    (systemDerivedTensorAdj scalar B (systemNextSelected_spec r m).1).homEquiv
      ((derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r m)).obj P)
      ((derivedSystemEvaluation B m).obj M)
      ((selectedDerivedBelow B r m).inv.app P ≫ (derivedSystemEvaluation B m).map f) =
    (derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r m)).map
      ((selected B r).adjunction.homEquiv P M f) ≫
    (selectedEvaluation B r (systemNextSelected r m)).hom.app M ≫
      (transition B (systemNextSelected_spec r m).1).app M
  selectedTransition : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r m N,
    ((systemDerivedTensorAdj scalar B (Nat.le_succ m)).homEquiv _ _).symm
      ((transition B (Nat.le_succ m)).app ((selected B r).derived.obj N)) =
    (systemDerivedTensor scalar B (Nat.le_succ m)).map
      ((selectedDerivedBelow B r (m + 1)).hom.app N) ≫
    (tensor.derivedAssoc B (Nat.le_succ m) (systemNextSelected_spec r (m + 1)).1).hom.app
      ((derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r (m + 1))).obj N) ≫
    (tensor.derivedAssoc B (systemNextSelected_spec r m).1
      (r.monotone (systemNextSelected_mono r m))).inv.app
      ((derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r (m + 1))).obj N) ≫
    (systemDerivedTensor scalar B (systemNextSelected_spec r m).1).map
      (((systemDerivedTensorAdj scalar (selectedSystemRings B r)
          (systemNextSelected_mono r m)).homEquiv _ _).symm
        ((transition (selectedSystemRings B r) (systemNextSelected_mono r m)).app N)) ≫
    (selectedDerivedBelow B r m).inv.app N
  restrictionComposition : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r s,
    derivedSystemSubsequence B r ⋙ derivedSystemSubsequence (selectedSystemRings B r) s ≅
      derivedSystemSubsequence B (s.trans r)
  restrictionComposition_rep : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r s K,
    (restrictionComposition B r s).hom.app (DerivedCategory.Q.obj K) ≫
      (systemSubsequence B (s.trans r)).mapDerivedCategoryFactors.hom.app K =
    (derivedSystemSubsequence (selectedSystemRings B r) s).map
      ((systemSubsequence B r).mapDerivedCategoryFactors.hom.app K) ≫
    (systemSubsequence (selectedSystemRings B r) s).mapDerivedCategoryFactors.hom.app
      (((systemSubsequence B r).mapHomologicalComplex (.up ℤ)).obj K)
  extensionComposition : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r s,
    (selected (selectedSystemRings B r) s).derived ⋙ (selected B r).derived ≅
      (selected B (s.trans r)).derived
  composition_mate : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r s P M
    (f : (selected B r).derived.obj ((selected (selectedSystemRings B r) s).derived.obj P) ⟶ M),
    (selected B (s.trans r)).adjunction.homEquiv P M
      ((extensionComposition B r s).inv.app P ≫ f) =
    (selected (selectedSystemRings B r) s).adjunction.homEquiv P
      ((derivedSystemSubsequence B r).obj M)
      ((selected B r).adjunction.homEquiv _ M f) ≫
        (restrictionComposition B r s).hom.app M
  extensionComposition_eval : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r s m P,
    (derivedSystemEvaluation B m).map ((extensionComposition B r s).hom.app P) ≫
      (selectedDerivedBelow B (s.trans r) m).hom.app P ≫
        eqToHom (systemSelectedTensor_trans scalar B r s m P) =
    (selectedDerivedBelow B r m).hom.app ((selected (selectedSystemRings B r) s).derived.obj P) ≫
      (systemDerivedTensor scalar B (systemNextSelected_spec r m).1).map
        ((selectedDerivedBelow (selectedSystemRings B r) s (systemNextSelected r m)).hom.app P) ≫
      (tensor.derivedAssoc B (systemNextSelected_spec r m).1
        (r.monotone (systemNextSelected_spec s (systemNextSelected r m)).1)).hom.app
        ((derivedSystemEvaluation (selectedSystemRings B (s.trans r))
          (systemNextSelected s (systemNextSelected r m))).obj P)

theorem systemLevelLeftExtensionTheory : Nonempty (SystemLevelLeftExtensionTheory (J := J))

```

## New

The original 50 public signatures and structure records above are retained verbatim apart
from whitespace. Forty-nine declarations now live in the two publicly reexported foundation
modules; the existence theorem remains in the original module. The public entry point is:

```lean
public import Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic
```

The added canonical constructor, used instead of an arbitrary coherence witness, is:

```lean
def systemTensorCoherence (S : SystemScalarAssignment (J := J)) :
    SystemTensorCoherence S := by
  let hu (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ) :
      B.map (homOfLE (Nat.le_refl n)).op = 𝟙 (B.obj (op n)) := by
    exact B.map_id (op n)
  let hc (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {l m n : ℕ}
      (h : l ≤ m) (k : m ≤ n) :
      B.map (homOfLE (h.trans k)).op =
        B.map (homOfLE k).op ≫ B.map (homOfLE h).op := by
    rw [← B.map_comp]
    rfl
  refine {
    ordinaryUnit := fun B n ↦ systemScalarModelUnit (hu B n) (S _)
    unit_normalized := fun B n ↦ systemScalarModelUnit_tmul (hu B n) (S _)
    ordinaryAssoc := fun B {l m n} h k ↦ systemScalarModelComposition (hc B h k) (S _) (S _) (S _)
    assoc_normalized := fun B {l m n} h k ↦
      systemScalarModelComposition_tmul (hc B h k) (S _) (S _) (S _)
    derivedUnit := fun B n ↦ systemScalarModelDerivedUnit (hu B n) (S _)
    derivedUnit_rep := fun B n P _ ↦ systemScalarModelDerivedUnit_rep (hu B n) (S _) P
    derivedAssoc := fun B {l m n} h k ↦
      systemScalarModelDerivedComposition (hc B h k) (S _) (S _) (S _)
    derivedAssoc_rep := fun B {l m n} h k P _ ↦
      systemScalarModelDerivedComposition_rep (hc B h k) (S _) (S _) (S _) P }
```

All other new declarations are proved constructions or theorems; there are no axioms or
new holes. Their modules and exact statements are attached to the 40 new DAG nodes.

## Users

`tools/downstream.py Sheaf.CategoryTheory.SystemLevelLeftExtension --uses <all 50 names>`
found the following 32 downstream modules, plus the item itself (refreshed after the
concurrent coefficient-image delivery). The interfaces and public
import visibility are preserved for each one. No consumer source adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.SystemLevelLeftExtension` | R7 | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientEvaluationDerivedAbove` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientEvaluationDerivedBelow` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientEvaluationDerivedCore` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientEvaluationDerivedExtension` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientEvaluationDerivedTransition` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientEvaluationModels` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientEvaluationOrdinaryCoherence` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientEvaluationStrictSigma` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientLevelOrdinaryImages` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientScalarDerivedAdjunction` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientSystemDerivedComparison` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientSystemImageData` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientSystemOrdinaryImages` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientSystemUnboundedComparison` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientTensorDerivedUnit` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.CoefficientTensorOrdinaryCoherence` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityCompactProjectionBaseChange` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityCompactProjectionData` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityCompactProjectionFinitePresentation` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityCompactProjectionTensorSquare` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityCompactProjectionTowerOperations` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityCompactProjectionTowerPresentation` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityLevelPullbackExact` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityNormalizedTowers` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityTowerEvaluationAdjoint` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityTowerInjectiveComponents` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityTowerLevels` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityTowerPushRightExtension` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityTowerRightExtension` | unclaimed | Same signatures and records through the original public entry point; no source edit. |
| `Sheaf.Paper.SmoothPurityTowerRightExtensionFiniteColimits` | unclaimed | Same signatures and records through the original public entry point; no source edit. |

The 39 new construction modules are owned by this R7 packet. The affected target meanings
are unchanged, so this is an interface relocation and proved API extension rather than a
change of any mathematical definition used by a target.

## Status

landed 20261021T020134-L-2590046 2026-10-21 (merge of deliver/R7/Sheaf.CategoryTheory.SystemLevelLeftExtension)
