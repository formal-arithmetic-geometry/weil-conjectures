/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Additive maps between coherent cohomology theories

Source: Stacks Project, Tags 03P2, 03FD, 010S and 010T.
(blueprint: lem-pbc-coherent-etale-comparison-morphism)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules.CoherentEtale
noncomputable section
set_option autoImplicit false

attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The standard large Ext presentation of Zariski abelian cohomology. -/
def sourceGroup (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf)
    (q : ℕ) : AddCommGrpCat.{u + 1} :=
  @Sheaf.functorH.{u + 1, u, u, u} _ _ (Opens.grothendieckTopology X) inferInstance
    (HasExt.standard _) q |>.obj ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F)

/-- The carrier of Zariski abelian cohomology. -/
abbrev Source (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) :=
  sourceGroup X F q

/-- Tensor sections with lifted additive coefficients. -/
def Coeff {X : Scheme.{u}} (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    (etaleTensorSectionsSheaf F)

/-- The cohomology of the lifted tensor-section sheaf. -/
def targetGroup (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] (q : ℕ) :
    AddCommGrpCat.{u + 1} :=
  @Sheaf.functorH.{u + 1, u + 1, u, u + 1} _ _ X.smallEtaleTopology
    inferInstance inferInstance q |>.obj (Coeff F)

/-- The carrier of etale cohomology. -/
abbrev Target (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] (q : ℕ) :=
  targetGroup X F q

/-- A family of coefficient maps on quasi-coherent modules. -/
abbrev Maps (X : Scheme.{u}) :=
  ∀ (F G : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] [G.IsQuasicoherent],
    (F ⟶ G) → (Coeff F ⟶ Coeff G)

/-- A family of additive cohomology maps, before proving invertibility. -/
abbrev Family (X : Scheme.{u}) :=
  ∀ (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (q : ℕ),
    Source X F q →+ Target X F q

/-- The map of large Zariski cohomology induced by a module morphism. -/
def sourceMap (X : Scheme.{u}) {F G : SheafOfModules.{u} X.ringCatSheaf}
    (φ : F ⟶ G) (q : ℕ) : Source X F q →+ Source X G q :=
  @Sheaf.H.map _ _ _ inferInstance (HasExt.standard _) _ _
    ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ) q

/-- The map of etale cohomology induced by a specified coefficient map. -/
def targetMap (X : Scheme.{u}) (m : Maps X)
    {F G : SheafOfModules.{u} X.ringCatSheaf} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) (q : ℕ) : Target X F q →+ Target X G q :=
  @Sheaf.H.map.{u + 1, u + 1, u, u + 1} _ _ _ inferInstance inferInstance _ _
    (m F G φ) q

/-- Evaluation of degree zero Zariski cohomology on the terminal open. -/
def sourceZero (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf) :
    Source X F 0 ≃+ Γ(F, ⊤) :=
  @Sheaf.H.equiv₀ _ _ _ inferInstance (HasExt.standard _)
    ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F) _ isTerminalTop

/-- Evaluation of degree zero etale cohomology on the terminal etale object. -/
def targetZero (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] : Target X F 0 ≃+
      ULift.{u + 1} Γ((tensorPullback (⊤_ X.Etale).hom).obj F, ⊤) :=
  @Sheaf.H.equiv₀.{u + 1, u + 1, u, u + 1} _ _ _ inferInstance inferInstance
    (Coeff F) _ terminalIsTerminal

/-- The Zariski connecting map, with its Ext instance fixed once. -/
def sourceBoundary {X : Scheme.{u}}
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    (ha : (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).ShortExact) (q : ℕ) :
    Source X S.X₃ q →+ Source X S.X₁ (q + 1) :=
  @Sheaf.H.δSucc _ _ _ inferInstance (HasExt.standard _) _ ha q

/-- The etale connecting map, with its coefficient objects fixed once. -/
def targetBoundary {X : Scheme.{u}} (m : Maps X)
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hz : m S.X₁ S.X₂ S.f ≫ m S.X₂ S.X₃ S.g = 0)
    (he : (ShortComplex.mk (m S.X₁ S.X₂ S.f) (m S.X₂ S.X₃ S.g) hz).ShortExact)
    (q : ℕ) : Target X S.X₃ q →+ Target X S.X₁ (q + 1) :=
  @Sheaf.H.δSucc _ _ _ inferInstance inferInstance _ he q

/-- Naturality, identity on sections, and compatibility with all connecting maps. -/
def IsNormalized (X : Scheme.{u}) (m : Maps X) (c : Family X) : Prop :=
  (∀ (F G : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (q : ℕ) (x : Source X F q),
    c G q (sourceMap X φ q x) = targetMap X m φ q (c F q x)) ∧
  (∀ (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (x : Source X F 0),
    targetZero X F (c F 0 x) =
      ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F (sourceZero X F x))) ∧
  ∀ (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
      [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
      (_hS : S.ShortExact)
      (hz : m S.X₁ S.X₂ S.f ≫ m S.X₂ S.X₃ S.g = 0)
      (ha : (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).ShortExact)
      (he : (ShortComplex.mk (m S.X₁ S.X₂ S.f) (m S.X₂ S.X₃ S.g) hz).ShortExact)
      (q : ℕ) (x : Source X S.X₃ q),
    c S.X₁ (q + 1) (sourceBoundary S ha q x) =
      targetBoundary m S hz he q (c S.X₃ q x)

/-- Exactness at the quotient term of the Zariski long exact sequence. -/
theorem source_exact {X : Scheme.{u}}
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    (ha : (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).ShortExact) (q : ℕ) :
    Function.Exact (sourceMap X S.g q) (sourceBoundary S ha q) :=
  @Sheaf.H.exact_map_δSucc _ _ _ inferInstance (HasExt.standard _) _ ha q

/-- Acyclicity of the middle term makes the Zariski boundary surjective. -/
theorem source_surjective {X : Scheme.{u}}
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    (ha : (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).ShortExact) (q : ℕ)
    (h : Subsingleton (Source X S.X₂ (q + 1))) :
    Function.Surjective (sourceBoundary S ha q) :=
  @Sheaf.H.δSucc_surjective _ _ _ inferInstance (HasExt.standard _) _ ha q h

/-- Exactness at the quotient term of the etale long exact sequence. -/
theorem target_exact {X : Scheme.{u}} (m : Maps X)
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hz : m S.X₁ S.X₂ S.f ≫ m S.X₂ S.X₃ S.g = 0)
    (he : (ShortComplex.mk (m S.X₁ S.X₂ S.f) (m S.X₂ S.X₃ S.g) hz).ShortExact)
    (q : ℕ) : Function.Exact (targetMap X m S.g q) (targetBoundary m S hz he q) :=
  @Sheaf.H.exact_map_δSucc _ _ _ inferInstance inferInstance _ he q

/-- Acyclicity of the middle term makes the etale boundary surjective. -/
theorem target_surjective {X : Scheme.{u}} (m : Maps X)
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hz : m S.X₁ S.X₂ S.f ≫ m S.X₂ S.X₃ S.g = 0)
    (he : (ShortComplex.mk (m S.X₁ S.X₂ S.f) (m S.X₂ S.X₃ S.g) hz).ShortExact)
    (q : ℕ) (h : Subsingleton (Target X S.X₂ (q + 1))) :
    Function.Surjective (targetBoundary m S hz he q) :=
  @Sheaf.H.δSucc_surjective _ _ _ inferInstance inferInstance _ he q h

/-- Acyclic short exact sequences for simultaneous dimension shifting. -/
def Effaces (X : Scheme.{u}) (m : Maps X) : Prop :=
  ∀ (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (n : ℕ),
      ∃ (G Q : SheafOfModules.{u} X.ringCatSheaf)
        (_hG : G.IsQuasicoherent) (_hQ : Q.IsQuasicoherent)
        (i : F ⟶ G) (p : G ⟶ Q) (h : i ≫ p = 0),
        let S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) := ShortComplex.mk i p h
        S.ShortExact ∧
        (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).ShortExact ∧
        ∃ hz : m F G i ≫ m G Q p = 0,
          (ShortComplex.mk (m F G i) (m G Q p) hz).ShortExact ∧
          Subsingleton (Source X G (n + 1)) ∧ Subsingleton (Target X G (n + 1))

/-- A normalized comparison is uniquely determined by its degree zero component. -/
theorem normalized_unique (X : Scheme.{u}) (m : Maps X)
    (efface : Effaces X m)
    (c d : Family X) (hc : IsNormalized X m c) (hd : IsNormalized X m d) : c = d := by
  funext F hF q
  apply AddMonoidHom.ext
  intro x
  induction q generalizing F with
  | zero =>
      apply (targetZero X F).injective
      exact Eq.trans (hc.2.1 F x) (Eq.symm (hd.2.1 F x))
  | succ n ih =>
      obtain ⟨G, Q, hG, hQ, i, p, hz, hS, ha, hez, he, hza, hze⟩ := efface F n
      let := hG
      let := hQ
      let := hza
      let S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) := ShortComplex.mk i p hz
      obtain ⟨y, hy⟩ := source_surjective S ha n hza x
      rw [← hy, hc.2.2 S hS hez ha he n y, hd.2.2 S hS hez ha he n y,
        ih Q hQ y]


/-- A normalized comparison is invertible by simultaneous dimension shifting. -/
theorem normalized_bijective (X : Scheme.{u}) (m : Maps X)
    (efface : Effaces X m)
    (c : Family X) (hc : IsNormalized X m c)
    (hzero : ∀ (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent],
      Function.Bijective (c F 0))
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (q : ℕ) :
    Function.Bijective (c F q) := by
  induction q generalizing F with
  | zero => exact hzero F
  | succ n ih =>
      obtain ⟨G, Q, hG, hQ, i, p, hz, hS, ha, hez, he, hza, hze⟩ := efface F n
      let := hG
      let := hQ
      let := hza
      let := hze
      let S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) := ShortComplex.mk i p hz
      refine ⟨?_, ?_⟩
      · apply (injective_iff_map_eq_zero (c F (n + 1))).2
        intro x hx
        obtain ⟨y, hy⟩ := source_surjective S ha n hza x
        have hcy : targetBoundary m S hez he n (c Q n y) = 0 := by
          exact (hc.2.2 S hS hez ha he n y).symm.trans
            ((congrArg (c F (n + 1)) hy).trans hx)
        obtain ⟨z, hz⟩ := ((target_exact m S hez he n) (c Q n y)).1 hcy
        obtain ⟨w, hw⟩ := (ih G).surjective z
        have hyw : y = sourceMap X p n w := by
          apply (ih Q).injective
          rw [hc.1 G Q p n w, hw]
          exact hz.symm
        rw [← hy, hyw]
        exact ((source_exact S ha n) _).2 ⟨w, rfl⟩
      · intro x
        obtain ⟨y, hy⟩ := target_surjective m S hez he n hze x
        obtain ⟨z, hz⟩ := (ih Q).surjective y
        refine ⟨sourceBoundary S ha n z, ?_⟩
        exact (hc.2.2 S hS hez ha he n z).trans
          ((congrArg (targetBoundary m S hez he n) hz).trans hy)


/-- Normalization identifies degree zero with an isomorphism on sections. -/
theorem normalized_zero_bijective (X : Scheme.{u}) (m : Maps X)
    (c : Family X) (hc : IsNormalized X m c)
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] :
    Function.Bijective (c F 0) := by
  have : IsIso (⊤_ X.Etale).hom :=
    AlgebraicGeometry.Etale.isIso_terminal_hom X
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  have hsections : ∀ {A B : Scheme.{u}} (a : A ⟶ B) [IsIso a]
      (G : B.Modules), IsIso (tensorSectionsUnit a G) := by
    intro A B a hia G
    let E : B.Modules ≌ A.Modules :=
      CategoryTheory.Equivalence.mk (pushforward (inv a)) (pushforward a)
        ((pushforwardId B).symm ≪≫
          pushforwardCongr (by simp only [IsIso.inv_hom_id]) ≪≫ (pushforwardComp _ _).symm)
        (pushforwardComp _ _ ≪≫
          pushforwardCongr (by simp only [IsIso.hom_inv_id]) ≪≫ pushforwardId A)
    let : (pushforward a).IsEquivalence := inferInstanceAs E.inverse.IsEquivalence
    have : IsIso ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app G) :=
      inferInstance
    have : IsIso (homOfLE a.preimage_top.ge) := homOfLE_isIso_of_eq _ a.preimage_top
    unfold tensorSectionsUnit
    infer_instance
  have : IsIso (tensorSectionsUnit (⊤_ X.Etale).hom F) :=
    hsections (⊤_ X.Etale).hom F
  let a := sourceZero X F
  let b := targetZero X F
  let e : Source X F 0 ≃+ Target X F 0 :=
    ((a.trans (asIso (tensorSectionsUnit (⊤_ X.Etale).hom F)).addCommGroupIsoToAddEquiv).trans
      AddEquiv.ulift.symm).trans b.symm
  have he : c F 0 = e.toAddMonoidHom := by
    ext x
    apply b.injective
    exact (hc.2.1 F x).trans (b.apply_symm_apply _).symm
  rw [he]
  exact e.bijective

end
end AlgebraicGeometry.Scheme.Modules.CoherentEtale
