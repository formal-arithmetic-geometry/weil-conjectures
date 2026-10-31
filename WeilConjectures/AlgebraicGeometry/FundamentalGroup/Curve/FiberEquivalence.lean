/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison
public import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
public import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import Mathlib.GroupTheory.Index
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Curve.ImageStabilizer

/-!
# The fundamental-group equivalence and base change

Source: Stacks Project, Theorem 0BND and Remark 0DV6; SGA 1, Exposé V,
Proposition 6.13 and §7 (blueprint: thm-galois-fundamental).
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The fibre equivalence, on finite étale covers and finite locally constant sheaves,
including the identification of the fundamental group and finite-limit/colimit compatibility.
Source: Stacks Project, Theorem 0BND (1), Remark 0DV6; SGA 1 V §7
(blueprint: thm-galois-fundamental).

Proof: `lem-fet-galois-category` and `thm-galois-abstract-equivalence` give the existing
`equivalenceContAction`. `lem-galois-aut-profinite` gives the evaluation topology.
The Yoneda equivalence `thm-galois-lc-etale` identifies both fibre functors; conjugation
along it identifies their automorphism groups, homeomorphically because evaluation
coordinates correspond and every sheaf is represented. Transporting the first equivalence
along its inverse gives the FLC equivalence. Its action is the evaluation action under
this group identification. Finally `lem-galois-equivalence-preserves-limits` says that
both equivalences preserve finite limits and colimits. -/
theorem exists_fiber_flc_equivalence {Y : Scheme.{w}} [ConnectedSpace Y]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (G : Type w) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G] :
    ∃ (Φ : Y.FiniteEtale ≌ Y.FLC) (E : Y.FLC ≌ ContAction FintypeCat.{w} G)
      (γ : G ≃ₜ* Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
        (pointSmallEtale s).sheafFiber (A := Type (w + 1)))),
      Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ≅
        ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{w + 1}) ∧
      Nonempty (Φ.functor ⋙ E.functor ≅ (equivalenceContAction s G).functor) ∧
      (∃ τ : E.functor ⋙ forget₂ (ContAction FintypeCat.{w} G) FintypeCat.{w} ⋙
          CategoryTheory.forget FintypeCat.{w} ⋙ uliftFunctor.{w + 1, w} ≅
          ObjectProperty.ι _ ⋙ (pointSmallEtale s).sheafFiber (A := Type (w + 1)),
        ∀ (F : Y.FLC) (g : G) (z : ULift.{w + 1} (E.functor.obj F).obj.V),
          τ.hom.app F ⟨((E.functor.obj F).obj.ρ g).hom z.down⟩ =
            (γ g).hom.app F (τ.hom.app F z)) ∧
      PreservesFiniteLimits (equivalenceContAction s G).functor ∧
      PreservesFiniteColimits (equivalenceContAction s G).functor ∧
      PreservesFiniteLimits E.functor ∧ PreservesFiniteColimits E.functor := by
  classical
  obtain ⟨Φ, hΦ, hβ, _⟩ := exists_finiteEtale_flc_equivalence_sheaf Y
  obtain ⟨β⟩ := hβ Ω s
  let E := Φ.symm.trans (equivalenceContAction s G)
  let K : Y.FLC ⥤ Type (w + 1) :=
    ObjectProperty.ι _ ⋙ (pointSmallEtale s).sheafFiber (A := Type (w + 1))
  let B := CategoryTheory.forget FintypeCat.{w} ⋙ uliftFunctor.{w + 1, w}
  let τ : E.functor ⋙ forget₂ (ContAction FintypeCat.{w} G) FintypeCat.{w} ⋙
      CategoryTheory.forget FintypeCat.{w} ⋙ uliftFunctor.{w + 1, w} ≅ K :=
    Functor.isoWhiskerLeft Φ.inverse β.symm ≪≫ Φ.invFunIdAssoc K
  let a : Aut (fiber s) ≃* Aut (fiber s ⋙ B) :=
    let ha := (Functor.FullyFaithful.ofFullyFaithful B).whiskeringRight Y.FiniteEtale
    ha.autMulEquivOfFullyFaithful (fiber s)
  let b : Aut (fiber s ⋙ B) ≃* Aut (Φ.inverse ⋙ fiber s ⋙ B) :=
    (Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringLeft _ _ _).obj Φ.inverse)).autMulEquivOfFullyFaithful _
  let γ₀ : G ≃* Aut K :=
    (toAutMulEquiv (fiber s) G).trans (a.trans (b.trans (Aut.autMulEquivOfIso τ)))
  have hact (F : Y.FLC) (g : G)
      (z : ULift.{w + 1} (E.functor.obj F).obj.V) :
      τ.hom.app F ⟨((E.functor.obj F).obj.ρ g).hom z.down⟩ =
        (γ₀ g).hom.app F (τ.hom.app F z) := by
    change τ.hom.app F ⟨g • (show (fiber s).obj (Φ.inverse.obj F) from z.down)⟩ =
      τ.hom.app F ⟨g • (show (fiber s).obj (Φ.inverse.obj F) from
        (τ.inv.app F (τ.hom.app F z)).down)⟩
    rw [show τ.inv.app F (τ.hom.app F z) = z from
      ConcreteCategory.congr_hom (τ.hom_inv_id_app F) z]
  have hcont : Continuous γ₀ := by
    change @Continuous G (Aut K) _
      (TopologicalSpace.induced (SetFunctorAut.evaluation K) _) γ₀
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro F
    let : TopologicalSpace (K.obj F) := ⊥
    change @Continuous G (Aut (K.obj F)) _ (TopologicalSpace.induced
      (fun σ : Aut (K.obj F) ↦ (σ.hom : K.obj F → K.obj F)) _) _
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro x
    change Continuous fun g : G ↦ τ.hom.app F
      ⟨g • (show (fiber s).obj (Φ.inverse.obj F) from (τ.inv.app F x).down)⟩
    let : ContinuousSMul G ((fiber s).obj (Φ.inverse.obj F)) :=
      IsFundamentalGroup.continuous_smul _
    have hc : Continuous (fun y : (fiber s).obj (Φ.inverse.obj F) ↦
        τ.hom.app F ⟨y⟩) := continuous_of_discreteTopology
    exact hc.comp (continuous_id.smul continuous_const)
  have (F : Y.FLC) : Finite (K.obj F) := by
    let i : K.obj F → ULift.{w + 1} ((fiber s).obj (Φ.inverse.obj F)) := τ.inv.app F
    exact Finite.of_injective i
      ((ConcreteCategory.isIso_iff_bijective (τ.inv.app F)).mp inferInstance).1
  have : T2Space (Aut K) :=
    ((SetFunctorAut.evaluation_isClosedEmbedding_and_profinite K).2
      (fun F ↦ inferInstance)).2.1
  let γ : G ≃ₜ* Aut K :=
    { γ₀ with
      continuous_toFun := hcont
      continuous_invFun := hcont.continuous_symm_of_equiv_compact_to_t2 }
  refine ⟨Φ, E, γ, hΦ, ?_, ⟨τ, hact⟩, inferInstance, inferInstance,
    inferInstance, inferInstance⟩
  exact ⟨Functor.isoWhiskerRight Φ.unitIso.symm (equivalenceContAction s G).functor⟩

/-- Base change corresponds to restriction of the action along the continuous map on π₁.
Source: Stacks Project, Theorem 0BND (3)
(blueprint: thm-galois-fundamental).

Proof: `lem-galois-pi1-functoriality` gives `fundamentalGroupMap`, its continuity,
and `pullbackFiberIso`. Its characterization is precisely equivariance of the
components of that natural isomorphism. The component bijections therefore lift
to an isomorphism of functors to continuous finite actions. -/
theorem fiber_equivalence_baseChange
    {X Y : Scheme.{w}} [ConnectedSpace X] [ConnectedSpace Y] (f : X ⟶ Y)
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (GX GY : Type w) [Group GX] [TopologicalSpace GX] [IsTopologicalGroup GX]
    [CompactSpace GX] [∀ Q, MulAction GX ((fiber s).obj Q)]
    [IsFundamentalGroup (fiber s) GX]
    [Group GY] [TopologicalSpace GY] [IsTopologicalGroup GY] [CompactSpace GY]
    [∀ P, MulAction GY ((fiber (s ≫ f)).obj P)]
    [IsFundamentalGroup (fiber (s ≫ f)) GY] :
    ∃ h : GX →ₜ* GY,
      h.toMonoidHom = fundamentalGroupMap (pullbackFiberIso f s) GX GY ∧
      ∃ η : pullback f ⋙ (equivalenceContAction s GX).functor ≅
          (equivalenceContAction (s ≫ f) GY).functor ⋙ ContAction.res FintypeCat.{w} h,
        ∀ (P : Y.FiniteEtale) (z : (fiber s).obj ((pullback f).obj P)),
          (η.hom.app P).hom.hom z = (pullbackFiberIso f s).hom.app P z := by
  let (Q : X.FiniteEtale) : ContinuousSMul GX ((fiber s).obj Q) :=
    IsFundamentalGroup.continuous_smul Q
  let h : GX →ₜ* GY :=
    ⟨fundamentalGroupMap (pullbackFiberIso f s) GX GY,
      continuous_fundamentalGroupMap (pullbackFiberIso f s) GX GY⟩
  refine ⟨h, rfl, ?_⟩
  let η : pullback f ⋙ (equivalenceContAction s GX).functor ≅
      (equivalenceContAction (s ≫ f) GY).functor ⋙ ContAction.res FintypeCat h :=
    NatIso.ofComponents (fun P ↦ ObjectProperty.isoMk _
      (Action.mkIso ((pullbackFiberIso f s).app P) (fun g ↦ by
        ext z
        exact (fundamentalGroupMap_smul (pullbackFiberIso f s) GX GY g P z).symm)))
      (fun {P Q} φ ↦ by
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        exact (pullbackFiberIso f s).hom.naturality φ)
  exact ⟨η, fun _ _ ↦ rfl⟩

/-- For finite étale base change the map is injective with open finite-index stabilizer image.
Source: SGA 1, Exposé V, Proposition 6.13 and §7, p. 116
(blueprint: thm-galois-fundamental).

Proof: `lem-galois-pi1-finite-etale-injective` gives injectivity.
`lem-galois-pi1-finite-etale-image-stabilizer` gives the image, openness and index,
the latter equal to the size of the finite geometric fibre (`def-galois-categories`).
The preceding base-change clause then says that pullback is restriction to this
open subgroup. Profinite compactness and Hausdorffness identify the source group
homeomorphically with its image (`lem-galois-aut-profinite`). -/
theorem fiber_equivalence_finiteEtale_baseChange
    {X Y : Scheme.{w}} [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (GX GY : Type w) [Group GX] [TopologicalSpace GX] [IsTopologicalGroup GX]
    [CompactSpace GX] [∀ Q, MulAction GX ((fiber s).obj Q)]
    [IsFundamentalGroup (fiber s) GX]
    [Group GY] [TopologicalSpace GY] [IsTopologicalGroup GY] [CompactSpace GY]
    [∀ P, MulAction GY ((fiber (s ≫ f)).obj P)]
    [IsFundamentalGroup (fiber (s ≫ f)) GY] :
    Function.Injective (fundamentalGroupMap (pullbackFiberIso f s) GX GY) ∧
      (fundamentalGroupMap (pullbackFiberIso f s) GX GY).range =
        MulAction.stabilizer GY
          (fiberMk (s ≫ f) ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩ s rfl) ∧
      IsOpen ((MulAction.stabilizer GY
        (fiberMk (s ≫ f) ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩ s rfl)) : Set GY) ∧
      (MulAction.stabilizer GY
        (fiberMk (s ≫ f) ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩ s rfl)).FiniteIndex := by
  let P : Y.FiniteEtale := ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩
  let a : (fiber (s ≫ f)).obj P := fiberMk (s ≫ f) P s rfl
  have hinj : Function.Injective (fundamentalGroupMap (pullbackFiberIso f s) GX GY) :=
    fundamentalGroupMap_injective (pullbackFiberIso f s) GY GX
  have hr := fundamentalGroupMap_range_eq_stabilizer (f := f) (s := s) GX GY
  have hrange : (fundamentalGroupMap (pullbackFiberIso f s) GX GY).range =
      MulAction.stabilizer GY a := by
    simpa [P, a] using hr.1
  have hopen : IsOpen (MulAction.stabilizer GY a : Set GY) := by
    simpa [P, a] using hr.2.1
  have hX : Nonempty X := by
    obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
    exact ⟨s.base z⟩
  have hindex : (MulAction.stabilizer GY a).index ≠ 0 := by
    rw [hr.2.2]
    exact (Nat.card_ne_zero.mpr ⟨nonempty_fiber_of_nonempty (s := s ≫ f) P hX,
      finite_fiber (s := s ≫ f) P⟩)
  have hfinite : (MulAction.stabilizer GY a).FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr hindex
  exact ⟨hinj, hrange, hopen, hfinite⟩

end AlgebraicGeometry.Scheme.FiniteEtale
