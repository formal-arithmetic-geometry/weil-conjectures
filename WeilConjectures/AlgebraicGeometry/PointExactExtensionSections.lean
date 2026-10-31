/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointDerivedHomModels
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Homology.Homotopy

import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.IntegralPointCoefficientAdjunction
-- Reuse the proved tensor construction at independent site/coefficient universes.
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits

/-! # Exact completed extension and sections at a point

Source: Stacks Project, Modules on Sites, Tags 03EI and 093M; blueprint
main-20261015, lem-pod-point-dualizing-complex, proof, second sentence
(blueprint: lem-pod-point-exact-extension-sections).

The extension objects, their maps, local tensor generators and scalar-restricted
sections are the published PointDerivedHom constructions. Both the finite and integral
cases use arbitrary modules and sheaves. Cochain complexes may be unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings

private def componentHomotopyEquiv
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {S : D ⥤ C} [L.Additive] [S.Additive] (adj : L ⊣ S)
    (P : CochainComplex C ℤ) (F : CochainComplex D ℤ)
    (f g : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ F) :
    Homotopy f g ≃
      Homotopy ((adj.mapHomologicalComplex (.up ℤ)).homEquiv P F f)
        ((adj.mapHomologicalComplex (.up ℤ)).homEquiv P F g) where
  toFun H :=
    { hom := fun i j ↦ adj.homEquiv (P.X i) (F.X j) (H.hom i j)
      zero := by
        intro i j h
        rw [H.zero i j h, adj.homAddEquiv_zero]
      comm := by
        intro i
        change adj.homEquiv _ _ (f.f i) =
          P.d i _ ≫ adj.homEquiv _ _ (H.hom _ i) +
            adj.homEquiv _ _ (H.hom i _) ≫ S.map (F.d _ i) +
              adj.homEquiv _ _ (g.f i)
        have h := congrArg (adj.homEquiv (P.X i) (F.X i)) (H.comm i)
        change adj.homEquiv _ _ (f.f i) = adj.homEquiv _ _
          ((L.map (P.d i _) ≫
            (show L.obj (P.X _) ⟶ F.X i from H.hom _ i)) +
            ((show L.obj (P.X i) ⟶ F.X _ from H.hom i _) ≫ F.d _ i) +
            (show L.obj (P.X i) ⟶ F.X i from g.f i)) at h
        simp only [Adjunction.homAddEquiv_add] at h ⊢
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right] at h
        exact h }
  invFun H :=
    { hom := fun i j ↦ (adj.homEquiv (P.X i) (F.X j)).symm (H.hom i j)
      zero := by
        intro i j h
        rw [H.zero i j h, adj.homAddEquiv_symm_zero]
      comm := by
        intro i
        apply (adj.homEquiv (P.X i) (F.X i)).injective
        change adj.homEquiv _ _ (f.f i) = adj.homEquiv _ _
          ((L.map (P.d i _) ≫ (adj.homEquiv _ _).symm (H.hom _ i)) +
            ((adj.homEquiv _ _).symm (H.hom i _) ≫ F.d _ i) +
              (show L.obj (P.X i) ⟶ F.X i from g.f i))
        have h := H.comm i
        change adj.homEquiv _ _ (f.f i) =
          P.d i _ ≫ (show P.X _ ⟶ S.obj (F.X i) from H.hom _ i) +
            (show P.X i ⟶ S.obj (F.X _) from H.hom i _) ≫ S.map (F.d _ i) +
            adj.homEquiv _ _ (g.f i) at h
        simp only [Adjunction.homAddEquiv_add]
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
        simpa only [Equiv.apply_symm_apply] using h }
  left_inv H := by ext i j; exact (adj.homEquiv _ _).symm_apply_apply _
  right_inv H := by ext i j; exact (adj.homEquiv _ _).apply_symm_apply _

namespace WeilConjectures.PointDerivedHom

attribute [local instance 3000] abSheafify abLocallyBijective

variable (k : Type t) [Field k] {R : CommRingCat.{max u (t + 1)}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
  (α : constantRing.{t, u} k R ⟶ B)

private def constantPresheafHomEquiv
    (M : ModuleCat.{max u (t + 1)} R)
    (Q : PresheafOfModules.{max u (t + 1)}
      ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj (RingCat.of R))) :
    ((constantPresheaf.{t, u} k R).obj M ⟶ Q) ≃
      (M ⟶ Q.obj (op (finalObject k))) where
  toFun f := f.app (op (finalObject k))
  invFun f :=
    { app := fun U ↦ ModuleCat.ofHom
        ((Q.map (toFinal k U.unop).op).hom.comp f.hom)
      naturality := by
        intro U V i
        ext x
        change Q.map (toFinal k V.unop).op (f.hom x) =
          Q.map i (Q.map (toFinal k U.unop).op (f.hom x))
        rw [← Q.map_comp_apply]
        have h : (toFinal k V.unop).op = (toFinal k U.unop).op ≫ i := by
          apply Quiver.Hom.unop_inj
          apply MorphismProperty.Over.Hom.ext
          exact (MorphismProperty.Over.w i.unop).symm
        rw [h] }
  left_inv f := by
    ext U x
    exact (PresheafOfModules.naturality_apply f (toFinal k U.unop).op x).symm
  right_inv f := by
    ext x
    change Q.map (toFinal k (finalObject k)).op (f.hom x) = f.hom x
    have h : toFinal k (finalObject k) = 𝟙 _ := by
      apply MorphismProperty.Over.Hom.ext
      rfl
    rw [h, op_id, Q.map_id]
    rfl

private def constantHomEquiv
    (M : ModuleCat.{max u (t + 1)} R)
    (F : Modules.{t, u} k (constantRing.{t, u} k R)) :
    ((constantModules.{t, u} k R).obj M ⟶ F) ≃
      (M ⟶ (sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _)).obj F) :=
  (PresheafOfModules.sheafificationHomEquiv.{max u (t + 1), t, max u (t + 1), t + 1}
    (constantUnit.{t, u} k R)).trans
    (constantPresheafHomEquiv.{t, u} k M
      ((PresheafOfModules.restrictScalars (constantUnit.{t, u} k R)).obj F.val))

private theorem constantHomEquiv_naturality_left
    {M N : ModuleCat.{max u (t + 1)} R} (f : M ⟶ N)
    (F : Modules.{t, u} k (constantRing.{t, u} k R))
    (g : (constantModules.{t, u} k R).obj N ⟶ F) :
    constantHomEquiv.{t, u} k M F ((constantModules.{t, u} k R).map f ≫ g) =
      f ≫ constantHomEquiv.{t, u} k N F g := by
  change constantPresheafHomEquiv.{t, u} k _ _
    ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t,
      max u (t + 1), t + 1} (constantUnit.{t, u} k R)).homEquiv _ _
        ((PresheafOfModules.sheafification.{max u (t + 1), t, max u (t + 1), t + 1}
            (constantUnit.{t, u} k R)).map
          ((constantPresheaf.{t, u} k R).map f) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left]
  rfl

private theorem constantHomEquiv_naturality_right
    (M : ModuleCat.{max u (t + 1)} R)
    {F G : Modules.{t, u} k (constantRing.{t, u} k R)}
    (f : (constantModules.{t, u} k R).obj M ⟶ F) (g : F ⟶ G) :
    constantHomEquiv.{t, u} k M G (f ≫ g) =
      constantHomEquiv.{t, u} k M F f ≫
        (sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _)).map g := by
  change constantPresheafHomEquiv.{t, u} k _ _
    ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t,
      max u (t + 1), t + 1} (constantUnit.{t, u} k R)).homEquiv _ _ (f ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private def constantAdjunction :
    constantModules.{t, u} k R ⊣
      sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantHomEquiv.{t, u} k
      homEquiv_naturality_left_symm := by
        intro M N F f g
        apply (constantHomEquiv.{t, u} k M F).injective
        rw [Equiv.apply_symm_apply, constantHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f g ↦ constantHomEquiv_naturality_right k _ f g }

open SheafOfModules.CoefficientOrdinaryProof

private def extensionFunctor : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B :=
  constantModules.{t, u} k R ⋙ tensorFunctor.{max u (t + 1), t + 1, t} α

private def extensionSectionsIso :
    restriction.{max u (t + 1), t + 1, t} α ⋙ sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _) ≅
      sections.{t, u} k B α :=
  NatIso.ofComponents (fun F ↦
    (show ((restriction.{max u (t + 1), t + 1, t} α ⋙
      sections.{t, u} k (constantRing.{t, u} k R) (𝟙 _)).obj F) ≃ₗ[R]
      (sections.{t, u} k B α).obj F from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }).toModuleIso) (by intros; rfl)

private def extensionAdjunction : extensionFunctor.{t, u} k B α ⊣ sections.{t, u} k B α :=
  ((constantAdjunction.{t, u} k).comp (tensorAdjunction.{max u (t + 1), t + 1, t} α)).ofNatIsoRight
    (extensionSectionsIso.{t, u} k B α)

private theorem extensionAdjunction_formula
    (M : ModuleCat.{max u (t + 1)} R) (F : Modules.{t, u} k B)
    (h : (extensionFunctor.{t, u} k B α).obj M ⟶ F) (x : M) :
    ((extensionAdjunction.{t, u} k B α).homEquiv M F h).hom x =
      h.val.app (op (finalObject k)) (extensionElement.{t, u} k B α M
        (op (finalObject k)) 1 x) := by
  rfl

private theorem extensionAdjunction_explicit :
    ExplicitAdjunction.{t, u} k B α (extensionFunctor.{t, u} k B α)
      (fun _ ↦ rfl) (extensionAdjunction.{t, u} k B α) := by
  constructor
  · exact extensionAdjunction_formula.{t, u} k B α
  · intro M F f U b x
    let h := ((extensionAdjunction.{t, u} k B α).homEquiv M F).symm f
    let q := (tensorAdjunction.{max u (t + 1), t + 1, t} α).homEquiv
      ((constantModules.{t, u} k R).obj M) F h
    let p := PresheafOfModules.sheafificationHomEquiv.{max u (t + 1), t,
      max u (t + 1), t + 1} (constantUnit.{t, u} k R) q
    have hp := PresheafOfModules.naturality_apply p (toFinal k U.unop).op x
    have hp' : h.val.app U (extensionElement.{t, u} k B α M U 1 x) =
        F.val.map (toFinal k U.unop).op (f.hom x) := by
      have hf := congrArg (fun g ↦ g.hom x)
        (((extensionAdjunction.{t, u} k B α).homEquiv M F).apply_symm_apply f)
      change h.val.app (op (finalObject k))
        (extensionElement.{t, u} k B α M (op (finalObject k)) 1 x) = f.hom x at hf
      change h.val.app U (extensionElement.{t, u} k B α M U 1 x) =
        F.val.map (toFinal k U.unop).op
          (h.val.app (op (finalObject k))
            (extensionElement.{t, u} k B α M (op (finalObject k)) 1 x)) at hp
      rw [hf] at hp
      exact hp
    change h.val.app U (extensionElement.{t, u} k B α M U b x) = _
    rw [← hp']
    let η := (PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t,
      max u (t + 1), t + 1} (𝟙 (ring.{t, u} k B).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} α
          ((constantModules.{t, u} k R).obj M))
    let H := η.app U ≫ h.val.app U
    change H.hom (b ⊗ₜ[(constantRing.{t, u} k R).obj.obj U, (α.hom.app U).hom]
      constantElement.{t, u} k R M U x) =
        b • H.hom ((1 : B.obj.obj U) ⊗ₜ[(constantRing.{t, u} k R).obj.obj U, (α.hom.app U).hom]
          constantElement.{t, u} k R M U x)
    rw [← H.hom.map_smul]
    congr 1
    change _ = (b * 1) ⊗ₜ[(constantRing.{t, u} k R).obj.obj U, (α.hom.app U).hom]
      constantElement.{t, u} k R M U x
    simp only [mul_one]

private theorem constant_exact :
    PreservesFiniteLimits (constantModules.{t, u} k R) ∧
      PreservesFiniteColimits (constantModules.{t, u} k R) := by
  let P := constantPresheaf.{t, u} k R
  have : PreservesFiniteLimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  exact ⟨comp_preservesFiniteLimits P (PresheafOfModules.sheafification
    (constantUnit.{t, u} k R)),
    comp_preservesFiniteColimits P (PresheafOfModules.sheafification
      (constantUnit.{t, u} k R))⟩

private def restrictionIdentityIso
    (A : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)}) :
    restriction.{max u (t + 1), t + 1, t} (𝟙 A) ≅ 𝟭 (Modules.{t, u} k A) :=
  NatIso.ofComponents (fun F ↦
    { hom := { val := { app := fun U ↦ ModuleCat.ofHom (LinearMap.id) } }
      inv := { val := { app := fun U ↦ ModuleCat.ofHom (LinearMap.id) } } })
    (by intros; rfl)

private theorem finite_extension_exact :
    PreservesFiniteLimits (extensionFunctor.{t, u} k (constantRing.{t, u} k R) (𝟙 _)) ∧
      PreservesFiniteColimits (extensionFunctor.{t, u} k (constantRing.{t, u} k R) (𝟙 _)) := by
  let T := tensorFunctor.{max u (t + 1), t + 1, t} (𝟙 (constantRing.{t, u} k R))
  let a := (tensorAdjunction.{max u (t + 1), t + 1, t} (𝟙 (constantRing.{t, u} k R))).ofNatIsoRight
    (restrictionIdentityIso.{t, u} k _)
  let e : T ≅ 𝟭 _ := a.leftAdjointUniq (Adjunction.id)
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso e.symm
  have := (constant_exact.{t, u} k (R := R)).1
  have := (constant_exact.{t, u} k (R := R)).2
  exact ⟨comp_preservesFiniteLimits _ T, comp_preservesFiniteColimits _ T⟩

/-- Exactness and the normalized extension/sections adjunction, with its termwise rules.
`L` has precisely the published tensor-extension objects and morphisms. The equivalence
on chain maps applies the ordinary adjunction in each degree; the equivalence on actual
homotopies applies it to every component, so it retains homotopy witnesses as well.
Source: Stacks 03EI, 093M, 03CY, 03EK; blueprint point-duality proof, second sentence
(blueprint: lem-pod-point-exact-extension-sections). -/
def ExactExtensionSections : Prop :=
  ∃ (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
    (hobj : ∀ M : ModuleCat.{max u (t + 1)} R,
      L.obj M = extensionObject.{t, u} k B α M),
    (∀ {M N : ModuleCat.{max u (t + 1)} R} (f : M ⟶ N),
      L.map f = eqToHom (hobj M) ≫ extensionMorphism.{t, u} k B α f ≫
        eqToHom (hobj N).symm) ∧
    PreservesFiniteLimits L ∧ PreservesFiniteColimits L ∧
    PreservesFiniteLimits (sections.{t, u} k B α) ∧
    PreservesFiniteColimits (sections.{t, u} k B α) ∧
    Function.Bijective (scalar.{t, u} k B α (op (finalObject k))) ∧
    ∃ adj : L ⊣ sections.{t, u} k B α,
      ExplicitAdjunction.{t, u} k B α L hobj adj ∧
      ∀ (P : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)
        (F : CochainComplex (Modules.{t, u} k B) ℤ),
        ∃ e : (((extensionComplex.{t, u} k B α L adj).obj P) ⟶ F) ≃
            (P ⟶ (sectionComplex.{t, u} k B α).obj F),
          (∀ (f : ((extensionComplex.{t, u} k B α L adj).obj P) ⟶ F) (i : ℤ),
            (e f).f i = adj.homEquiv (P.X i) (F.X i) (f.f i)) ∧
          ∀ (f g : ((extensionComplex.{t, u} k B α L adj).obj P) ⟶ F),
            ∃ eH : Homotopy f g ≃ Homotopy (e f) (e g),
              ∀ (H : Homotopy f g) (i j : ℤ),
                (eH H).hom i j = adj.homEquiv (P.X i) (F.X j) (H.hom i j)

private theorem exactExtensionSections_of_adjunction
    (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
    (hobj : ∀ M, L.obj M = extensionObject.{t, u} k B α M)
    (hmap : ∀ {M N : ModuleCat.{max u (t + 1)} R} (f : M ⟶ N),
      L.map f = eqToHom (hobj M) ≫ extensionMorphism.{t, u} k B α f ≫
        eqToHom (hobj N).symm)
    (hL : PreservesFiniteLimits L ∧ PreservesFiniteColimits L)
    (hS : PreservesFiniteLimits (sections.{t, u} k B α) ∧
      PreservesFiniteColimits (sections.{t, u} k B α))
    (hb : Function.Bijective (scalar.{t, u} k B α (op (finalObject k))))
    (adj : L ⊣ sections.{t, u} k B α)
    (hex : ExplicitAdjunction.{t, u} k B α L hobj adj) :
    ExactExtensionSections.{t, u} k B α := by
  refine ⟨L, hobj, hmap, hL.1, hL.2, hS.1, hS.2, hb, adj, hex, ?_⟩
  have := adj.left_adjoint_additive
  intro P F
  refine ⟨(adj.mapHomologicalComplex (.up ℤ)).homEquiv P F, ?_, ?_⟩
  · intro f i
    rfl
  · intro f g
    exact ⟨componentHomotopyEquiv adj P F f g, fun H i j ↦ rfl⟩

private theorem sections_exact [IsAlgClosed k] :
    PreservesFiniteLimits (sections.{t, u} k B α) ∧
      PreservesFiniteColimits (sections.{t, u} k B α) := by
  have hs := (ProEtale.point_proEtale_sections_exact_of_universes.{t, u,
    max u (t + 1), max u (t + 1)} k).2 B
  have := hs.1
  have := hs.2.1
  let S := ProEtale.pointModuleSectionsOfUniverses.{t, u} k B
  let A := ModuleCat.restrictScalars (scalar.{t, u} k B α (op (finalObject k)))
  exact ⟨comp_preservesFiniteLimits S A, comp_preservesFiniteColimits S A⟩

/-- Extension of arbitrary modules to either finite constant or completed integral point
coefficients is exact and left adjoint to exact final-object sections. The constant-value
ring map is bijective. The adjunction has the two prescribed pure-tensor formulas and
identifies chain maps and chain homotopies componentwise, without boundedness assumptions.
The index `n ≥ 1` is the actual quotient exponent, and `integral = true` uses completion.

Source: Stacks 03EI (lemma-sheafification-exact), 093M (lemma-completion-flat), 03CY,
03EK; blueprint main-20261015, point-duality proof, second sentence
(blueprint: lem-pod-point-exact-extension-sections).

Proof:
1. The existing integral point coefficient adjunction supplies exact integral extension,
   exact integral sections, the normalized ordinary adjunction, and the constant-value
   bijections at integral and finite levels. Its finite index m is exponent m+1; use
   n ≥ 1 to write n = m+1.
2. For finite coefficients, compose the constant-module sheafification adjunction with
   the sheafified tensor/restriction adjunction. The constant-module Hom equivalence
   evaluates at the final object; its inverse restricts along each map to that object.
   The tensor adjunction then gives the required local pure-tensor formulas.
3. Constant module presheaves preserve finite limits and colimits objectwise, and
   module sheafification is exact. Tensoring along the identity ring map is naturally
   isomorphic to the identity: restriction is the identity and left adjoints are unique.
   This proves exactness of finite extension. Exact point sections followed by exact
   scalar restriction give exact finite sections.
4. Apply the additive adjunction to complexes using mapHomologicalComplex. Its Hom
   equivalence is the ordinary equivalence in each degree. Apply the ordinary
   equivalence to every component of a homotopy as well. Additivity and naturality
   transport its defining equation in both directions; the componentwise inverse
   proves that this is an equivalence of actual homotopy witnesses.
No step uses finite generation of M or constructibility of F. -/
theorem point_exact_extension_sections
    (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (_hn : 1 ≤ n) (integral : Bool) :
    ExactExtensionSections.{t, u} D.k
      (coefficientSheaf.{t, u} D.k l E n integral)
      (coefficientMap.{t, u} D.k l E n integral) := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  obtain ⟨_, _, hfinite, _, hintegral, _, hsections, L, hobj, hmap, hL,
    adj, hex, _⟩ :=
    IntegralPointCoefficientAdjunction.integral_point_coefficient_adjunction l E D _hl
  cases integral with
  | true =>
    exact exactExtensionSections_of_adjunction.{t, u} D.k _ _ L hobj
      (fun f ↦ hmap _ _ f) hL hsections hintegral adj hex
  | false =>
    have hb : Function.Bijective (scalar.{t, u} D.k
        (coefficientSheaf.{t, u} D.k l E n false)
        (coefficientMap.{t, u} D.k l E n false) (op (finalObject D.k))) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
      exact hfinite m
    let R := coefficientRing.{t, u} l E n false
    let B := constantRing.{t, u} D.k R
    apply exactExtensionSections_of_adjunction.{t, u} D.k B (𝟙 B)
      (extensionFunctor.{t, u} D.k B (𝟙 B)) (fun _ ↦ rfl)
    · intro M N f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    · exact finite_extension_exact.{t, u} D.k
    · exact sections_exact.{t, u} D.k B (𝟙 B)
    · exact hb
    · exact extensionAdjunction_explicit.{t, u} D.k B (𝟙 B)

end WeilConjectures.PointDerivedHom
