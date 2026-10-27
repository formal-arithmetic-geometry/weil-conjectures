/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.CategoryTheory.SheafTensor
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.CategoryTheory.CondensedInternalBarResolution
public import Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Free profinite internal Hom on arbitrary injective resolutions

Source: blueprint direct-image stability, paragraph (3); Stacks Project, Tags 03EO,
07A5, 070J, 070K and 070Y
(blueprint: lem-sfb-profinite-free-hom-resolution-evaluation).

The free object is the existing freeParameter. Internal Hom is the recorded equalizer,
with its actual evaluation. The specification retains natural isomorphisms of complexes,
the generator normalization, and the unit of the ordinary unbounded derived functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct

namespace CategoryTheory.CondensedBar.ProfiniteHom

variable (A : Ring.{u})

/-- Specialize the recorded equalizer internal Hom to the existing free parameter.
Source: Stacks 03EO; blueprint paragraph (3)
(blueprint: lem-sfb-profinite-free-hom-resolution-evaluation). -/
abbrev hom (P : Profinite.{u}) : Modules A ⥤ Modules A :=
  Mod.ihom' A.X (freeParameter A P)

/-- Evaluate the underlying abelian sheaf at a profinite test object.
Source: the section evaluation in blueprint paragraph (3)
(blueprint: lem-sfb-profinite-free-hom-resolution-evaluation). -/
abbrev eval (S : Profinite.{u}) : Modules A ⥤ AddCommGrpCat.{u + 1} :=
  Mod.forget A.X ⋙ sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation Profinite.{u}ᵒᵖ AddCommGrpCat.{u + 1}).obj (op S)

/-- Evaluation of the equalizer Hom on two generalized sections, using its actual counit.
Source: Stacks 03EO, tensor/Hom evaluation
(blueprint: lem-sfb-profinite-free-hom-resolution-evaluation). -/
def value (K N : Modules A) (S : Profinite.{u})
    (x : sections A ((Mod.ihom' A.X K).obj N) S) (y : sections A K S) : sections A N S :=
  ((Mod.ihomDesc (𝟙 ((Mod.ihom' A.X K).obj N))).hom.hom.app (op S))
    (((Functor.LaxMonoidal.μ
      (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
      ((Mod.ihom' A.X K).obj N).X K.X).app (op S)) (x ⊗ₜ[ℤ] y))

/-- The unit generator in the existing free module; this abbreviates the free adjunction.
Source: blueprint paragraph (3), generator [f]
(blueprint: lem-sfb-profinite-free-hom-resolution-evaluation). -/
abbrev generator (P T : Profinite.{u}) (f : T ⟶ P) : sections A (freeParameter A P) T :=
  (((Profinite.CondensedAction.InternalBar.freeAdjunction A.toMon).unit.app
    ((GrothendieckTopology.uliftYoneda.{u + 1} (coherentTopology Profinite.{u})).obj P)).hom.app
      (op T)) (ULift.up f)

/-- Precomposition by the actual covariant free-module map, as the adjunction mate.
Source: blueprint paragraph (3), restriction along a profinite parameter map
(blueprint: lem-sfb-profinite-free-hom-resolution-evaluation). -/
def pre {P P' : Profinite.{u}} (v : P' ⟶ P) : hom A P ⟶ hom A P' :=
  conjugateEquiv (Mod.ihom'Adjunction A.X (freeParameter A P))
    (Mod.ihom'Adjunction A.X (freeParameter A P'))
    (Mod.tensorLeftMap
      ((Profinite.CondensedAction.InternalBar.free A.toMon).map
        ((GrothendieckTopology.uliftYoneda.{u + 1} (coherentTopology Profinite.{u})).map v)))

/-- Internal Hom from a free parameter is additive and left exact.
Source: Stacks 03EO; blueprint proof steps 2 and 5
(blueprint: lem-sfb-profinite-free-hom-resolution-evaluation).
Proof: the recorded equalizer adjunction makes this a right adjoint. It preserves limits;
in the abelian module category finite products are biproducts, so it preserves addition.
-/
theorem hom_additive_leftExact (P : Profinite.{u}) :
    (hom A P).Additive ∧ PreservesFiniteLimits (hom A P) := by
  let adj := Mod.ihom'Adjunction A.X (freeParameter A P)
  let : PreservesLimits (hom A P) := adj.rightAdjoint_preservesLimits
  exact ⟨Functor.additive_of_preserves_binary_products (hom A P), inferInstance⟩

/-- The additive structure supplied by the preceding clause.
Source: blueprint proof step 5
(blueprint: lem-sfb-profinite-free-hom-resolution-evaluation). -/
instance homAdditive (P : Profinite.{u}) : (hom A P).Additive :=
  (hom_additive_leftExact A P).1

/-- The published functorial K-injective replacement gives the resolution hypothesis.
Source: Stacks 070K and blueprint proof step 5
(blueprint: lem-sfb-profinite-free-hom-resolution-evaluation). -/
abbrev enough : ∀ K : CochainComplex (Modules A) ℤ,
    ∃ (I : CochainComplex (Modules A) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s :=
  fun K ↦ ⟨(CochainComplex.kInjectiveResolutionFunctor (Modules A)).obj K,
    (CochainComplex.toKInjectiveResolution (Modules A)).app K, inferInstance,
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app (Modules A) K).2⟩

variable [HasDerivedCategory.{u + 2} (Modules A)]

/-- The recorded ordinary unbounded right-derived functor, derived only in its target.
Source: Stacks 070K, 070Y and blueprint proof step 5
(blueprint: lem-sfb-profinite-free-hom-resolution-evaluation). -/
abbrev derived (P : Profinite.{u}) : DerivedCategory (Modules A) ⥤ DerivedCategory (Modules A) :=
  (hom A P).rightDerivedFunctorOfQuasiIsoResolutions (enough A)

/-- Its canonical unit on a complex, using the quotient/localization identification.
Source: Stacks 070Y and blueprint proof step 5
(blueprint: lem-sfb-profinite-free-hom-resolution-evaluation). -/
abbrev unit (P : Profinite.{u}) (K : CochainComplex (Modules A) ℤ) :
    DerivedCategory.Q.obj (((hom A P).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (derived A P).obj (DerivedCategory.Q.obj K) :=
  ((hom A P).rightDerivedFunctorOfQuasiIsoResolutionsUnit (enough A)).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj K)

/-- All evaluations, transport identifications, and arbitrary resolution comparisons.
Source: blueprint paragraph (3) and Stacks 03EO, 07A5, 070J, 070K, 070Y
(blueprint: lem-sfb-profinite-free-hom-resolution-evaluation). -/
structure Evaluation where
  /-- Internal modules are Grothendieck abelian in the coefficient size. -/
  grothendieck : IsGrothendieckAbelian.{u + 1} (Modules A)
  /-- Every module admits a nonnegative injective resolution. -/
  resolutions : ∀ M : Modules A, Nonempty (InjectiveResolution M)
  /-- The specified internal-to-sectionwise equivalence is exact. -/
  exact : exactFunctor _ _
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (coherentTopology Profinite.{u}) A.X).functor
  /-- It preserves injective objects. -/
  injectives : ∀ M : Modules A, Injective M → Injective
    ((InternalAbelianSheafModule.sectionModuleEquivalence
      (coherentTopology Profinite.{u}) A.X).functor.obj M)
  /-- Its tensor comparison is the existing pure-tensor normalized comparison. -/
  tensor : ∀ K N : Modules A,
    (sectionsFunctor A).obj (K ⊗ N) ≅ (sectionsFunctor A).obj K ⊗ (sectionsFunctor A).obj N
  /-- The tensor identification is the identity on local pure tensors. -/
  tensor_value : ∀ (K N : Modules A) (S : Profinite.{u})
      (x : sections A K S) (y : sections A N S),
    (tensor K N).hom.val.app (op S)
        (InternalAbelianSheafModule.comparison_internalTmul
          (coherentTopology Profinite.{u}) A.X K N (op S) x y) =
      InternalAbelianSheafModule.comparison_sectionTmul
        (coherentTopology Profinite.{u}) A.X
        ((sectionsFunctor A).obj K) ((sectionsFunctor A).obj N) (op S) x y
  /-- Internal Hom agrees with the actual slice sheaf Hom. -/
  homIso : ∀ K N : Modules A,
    (sectionsFunctor A).obj ((Mod.ihom' A.X K).obj N) ≅
      SheafOfModules.homObj.{u + 1, u, u + 1, u + 1}
        (R := InternalAbelianSheafModule.sectionRingSheaf
          (coherentTopology Profinite.{u}) A.X)
        ((sectionsFunctor A).obj K) ((sectionsFunctor A).obj N)
  /-- This agreement preserves evaluation, fixing its normalization on all local sections. -/
  hom_value : ∀ (K N : Modules A) (S T : Profinite.{u}) (f : T ⟶ S)
      (x : sections A ((Mod.ihom' A.X K).obj N) S) (y : sections A K T),
    (((homIso K N).hom.val.app (op S) x).app (op (Over.mk f))) y =
      value A K N T (((Mod.ihom' A.X K).obj N).X.obj.map f.op x) y
  /-- Product evaluation is an additive natural isomorphism in the module. -/
  evaluate : ∀ P S : Profinite.{u}, hom A P ⋙ eval A S ≅ eval A (Limits.prod S P)
  /-- It is evaluation on the tautological generator over S times P. -/
  tautological : ∀ (P S : Profinite.{u}) (N : Modules A)
      (x : sections A ((hom A P).obj N) S),
    (evaluate P S).hom.app N x =
      value A (freeParameter A P) N (Limits.prod S P)
        (((hom A P).obj N).X.obj.map (Limits.prod.fst : Limits.prod S P ⟶ S).op x)
        (generator A P (Limits.prod S P) Limits.prod.snd)
  /-- Scalars act through restriction along the first projection. -/
  scalar : ∀ (P S : Profinite.{u}) (N : Modules A) (a : sectionRing A S)
      (x : sections A ((hom A P).obj N) S),
    (evaluate P S).hom.app N (a • x) =
      (InternalAbelianSheafModule.sectionRingSheaf
        (coherentTopology Profinite.{u}) A.X).obj.map (Limits.prod.fst : Limits.prod S P ⟶ S).op a •
        (@id (sections A N (Limits.prod S P)) ((evaluate P S).hom.app N x))
  /-- Restriction in the test object is the product restriction. -/
  restriction : ∀ (P S S' : Profinite.{u}) (v : S' ⟶ S) (N : Modules A)
      (x : sections A ((hom A P).obj N) S),
    (evaluate P S').hom.app N (((hom A P).obj N).X.obj.map v.op x) =
      N.X.obj.map (Limits.prod.map v (𝟙 P)).op ((evaluate P S).hom.app N x)
  /-- Precomposition by A[v] is restriction by the second product map. -/
  parameter : ∀ (P P' S : Profinite.{u}) (v : P' ⟶ P) (N : Modules A)
      (x : sections A ((hom A P).obj N) S),
    (evaluate P' S).hom.app N (((pre A v).app N).hom.hom.app (op S) x) =
      N.X.obj.map (Limits.prod.map (𝟙 S) v).op ((evaluate P S).hom.app N x)
  /-- Evaluation identifies entire complexes, including their differentials. -/
  complexIso : ∀ (P S : Profinite.{u}) (I : CochainComplex (Modules A) ℤ),
    (((hom A P ⋙ eval A S).mapHomologicalComplex (.up ℤ)).obj I) ≅
      (((eval A (Limits.prod S P)).mapHomologicalComplex (.up ℤ)).obj I)
  /-- The complex comparison is precisely the displayed evaluation in each degree. -/
  complex_component : ∀ (P S : Profinite.{u}) (I : CochainComplex (Modules A) ℤ) (n : ℤ),
    (complexIso P S I).hom.f n = (evaluate P S).hom.app (I.X n)
  /-- All maps of complexes, in particular augmentations and maps of resolutions, commute. -/
  complex_natural : ∀ (P S : Profinite.{u}) (I I' : CochainComplex (Modules A) ℤ) (b : I ⟶ I'),
    ((hom A P ⋙ eval A S).mapHomologicalComplex (.up ℤ)).map b ≫
        (complexIso P S I').hom =
      (complexIso P S I).hom ≫ ((eval A (Limits.prod S P)).mapHomologicalComplex (.up ℤ)).map b
  /-- Every nonnegative injective resolution gives the ordinary derived computation. -/
  computation : ∀ (P : Profinite.{u}) (M : Modules A) (I : CochainComplex (Modules A) ℤ)
      (s : (HomologicalComplex.single (Modules A) (.up ℤ) 0).obj M ⟶ I),
    (∀ n : ℤ, n < 0 → IsZero (I.X n)) →
    (∀ n : ℤ, Injective (I.X n)) → QuasiIso s →
    ((derived A P).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single (Modules A) (.up ℤ) 0).obj M)) ≅
      DerivedCategory.Q.obj (((hom A P).mapHomologicalComplex (.up ℤ)).obj I))
  /-- The comparison is the canonical computation comparison, fixed by the unit at I. -/
  computation_unit : ∀ (P : Profinite.{u}) (M : Modules A) (I : CochainComplex (Modules A) ℤ)
      (s : (HomologicalComplex.single (Modules A) (.up ℤ) 0).obj M ⟶ I)
      (h₀ : ∀ n : ℤ, n < 0 → IsZero (I.X n)) (hI : ∀ n : ℤ, Injective (I.X n))
      (hs : QuasiIso s),
    (computation P M I s h₀ hI hs).hom ≫ unit A P I =
      (derived A P).map (DerivedCategory.Q.map s)
  /-- Its augmentation is application of H_P to the specified resolution map. -/
  augmentation : ∀ (P : Profinite.{u}) (M : Modules A) (I : CochainComplex (Modules A) ℤ)
      (s : (HomologicalComplex.single (Modules A) (.up ℤ) 0).obj M ⟶ I)
      (h₀ : ∀ n : ℤ, n < 0 → IsZero (I.X n)) (hI : ∀ n : ℤ, Injective (I.X n))
      (hs : QuasiIso s),
    unit A P ((HomologicalComplex.single (Modules A) (.up ℤ) 0).obj M) ≫
        (computation P M I s h₀ hI hs).hom =
      DerivedCategory.Q.map (((hom A P).mapHomologicalComplex (.up ℤ)).map s)

/-- The free-generator evaluation and arbitrary-resolution comparison exist with all
normalizations and compatibilities above.
Source: blueprint direct-image stability paragraph (3); Stacks 03EO, 07A5, 070J, 070K, 070Y
(blueprint: lem-sfb-profinite-free-hom-resolution-evaluation).

Proof:
1. Finite jointly surjective covers of profinite spaces are effective for continuous maps:
the finite coproduct map is a compact-Hausdorff quotient. This includes the empty cover
of the empty object. Representables are sheaves and their products are representable.
The ringed-site Grothendieck theorem and the internal/section equivalence transport a
generator, colimits and exact filtered colimits to internal modules. Enough injectives
and successive cokernels give nonnegative resolutions.
2. The exact equivalence preserves injectives by transporting lifting problems. Its
pure-tensor comparison identifies tensor and its Hom right adjoint with section tensor
and slice sheaf Hom. Uniqueness of adjoints preserves the evaluation counits.
3. Free adjunction, Yoneda, tensor/Hom adjunction and free linearization on products give
H_P(N)(S) = N(S times P). The inverse sends m to the map [s] tensor [p] to N((s,p))(m).
The forward map restricts to S times P and evaluates on [pr_P]. These formulas are inverse,
additive and linear with scalars restricted by pr_S.
4. Substitute a test map, a parameter map or a module map into the generator formula.
This gives precisely the three naturality squares and their mixed compositions.
5. H_P is additive and left exact by its adjunction. Grothendieck K-injective resolutions
supply its ordinary total right derived functor. Every nonnegative complex of injectives
is K-injective (070J); its comparison with the derived functor respects the defining unit.
6. Apply the additive natural evaluation in every degree and to every differential.
It gives the specified complex isomorphism. Naturality for every chain map includes the
given augmentation and arbitrary maps of resolutions, and the test and parameter squares
hold componentwise. No acyclicity of values or projectivity of the free parameter is used.
-/
theorem exists_evaluation : Nonempty (Evaluation A) := by
  sorry

end CategoryTheory.CondensedBar.ProfiniteHom
