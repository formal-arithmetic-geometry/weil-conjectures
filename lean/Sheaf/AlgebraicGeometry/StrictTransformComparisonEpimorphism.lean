module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-! # Comparison of successive module strict transforms

Source: Stacks Project, Divisors, Tag 080I, proof paragraphs 1--2, through the
factorization (blueprint: lem-trf-strict-transform-comparison-epimorphism).

The twice-base-changed scheme is represented by the iterated fibre product.
The single transform is pulled back along the canonical identification with the
fibre product for the specified composite blowup. All quotient maps retain their centres.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The second module strict transform, using the first transform's quasi-coherence proof.
This proof is existentially supplied in the comparison theorem, rather than assumed.
Source: Stacks, Tag 080I, proof paragraph 1
(blueprint: lem-trf-strict-transform-comparison-epimorphism). -/
noncomputable def successiveModuleStrictTransform {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (J : I.blowup.IdealSheafData) [J.toModules.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent]
    (h₁ : (moduleStrictTransform f I F).IsQuasicoherent) :
    (Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap).Modules :=
  @moduleStrictTransform _ _ (pullback.snd f I.blowupMap) J inferInstance
    (moduleStrictTransform f I F) h₁

/-- The composite of the pulled-back first quotient with the second quotient.
Source: Stacks, Tag 080I, proof paragraph 1
(blueprint: lem-trf-strict-transform-comparison-epimorphism). -/
noncomputable def successiveModuleStrictTransformπ {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (J : I.blowup.IdealSheafData) [J.toModules.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent]
    (h₁ : (moduleStrictTransform f I F).IsQuasicoherent) :
    (tensorPullback (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap)).obj
      ((tensorPullback (pullback.fst f I.blowupMap)).obj F) ⟶
        successiveModuleStrictTransform f I J F h₁ :=
  (tensorPullback (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap)).map
    (moduleStrictTransformπ f I F) ≫
      @moduleStrictTransformπ _ _ (pullback.snd f I.blowupMap) J inferInstance
        (moduleStrictTransform f I F) h₁

/-- The canonical map from the iterated fibre product to the fibre product for `K`.
For the specified isomorphism over `S`, it is the canonical fibre-product identification.
Source: Stacks, Tag 080I, displayed diagram in the proof
(blueprint: lem-trf-strict-transform-comparison-epimorphism). -/
noncomputable def moduleStrictTransformCompositeBaseMap {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) (J : I.blowup.IdealSheafData) (K : S.IdealSheafData)
    (e : J.blowup ≅ K.blowup) (he : e.hom ≫ K.blowupMap = J.blowupMap ≫ I.blowupMap) :
    Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap ⟶ Limits.pullback f K.blowupMap :=
  pullback.lift
    (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap ≫ pullback.fst f I.blowupMap)
    (pullback.snd (pullback.snd f I.blowupMap) J.blowupMap ≫ e.hom)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a ↦ pullback.fst (pullback.snd f I.blowupMap) J.blowupMap ≫ a)
        (pullback.condition (f := f) (g := I.blowupMap))).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a ↦ a ≫ I.blowupMap)
            (pullback.condition (f := pullback.snd f I.blowupMap) (g := J.blowupMap))).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun a ↦
                pullback.snd (pullback.snd f I.blowupMap) J.blowupMap ≫ a) he.symm).trans
                (Category.assoc _ _ _).symm))))))

/-- The single `K`-transform transported to the iterated fibre product.
Source: Stacks, Tag 080I, proof paragraph 1
(blueprint: lem-trf-strict-transform-comparison-epimorphism). -/
noncomputable def compositeModuleStrictTransform {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) (J : I.blowup.IdealSheafData)
    (K : S.IdealSheafData) [K.toModules.IsFiniteType]
    (e : J.blowup ≅ K.blowup) (he : e.hom ≫ K.blowupMap = J.blowupMap ≫ I.blowupMap)
    (F : X.Modules) [F.IsQuasicoherent] :
    (Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap).Modules :=
  (tensorPullback (moduleStrictTransformCompositeBaseMap f I J K e he)).obj
    (moduleStrictTransform f K F)

/-- The canonical single-transform quotient, with source `q* p* F`.
The two comparison isomorphisms come from the section-normalized tensor adjunction.
Source: Stacks, Tag 080I, proof paragraph 1
(blueprint: lem-trf-strict-transform-comparison-epimorphism). -/
noncomputable def compositeModuleStrictTransformπ {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) (J : I.blowup.IdealSheafData)
    (K : S.IdealSheafData) [K.toModules.IsFiniteType]
    (e : J.blowup ≅ K.blowup) (he : e.hom ≫ K.blowupMap = J.blowupMap ≫ I.blowupMap)
    (F : X.Modules) [F.IsQuasicoherent] :
    (tensorPullback (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap)).obj
      ((tensorPullback (pullback.fst f I.blowupMap)).obj F) ⟶
        compositeModuleStrictTransform f I J K e he F :=
  (tensorPullbackSectionComp (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap)
    (pullback.fst f I.blowupMap)).inv.app F ≫
  eqToHom (congrArg (fun a ↦ (tensorPullback a).obj F)
    (pullback.lift_fst _ _ _).symm) ≫
  (tensorPullbackSectionComp (moduleStrictTransformCompositeBaseMap f I J K e he)
    (pullback.fst f K.blowupMap)).hom.app F ≫
  (tensorPullback (moduleStrictTransformCompositeBaseMap f I J K e he)).map
    (moduleStrictTransformπ f K F)

/-- Successive strict transforms have a unique epimorphic comparison to the single
transform; the comparison kernel is supported on the inverse image of `V(K)`.
Source: Stacks, Tag 080I, proof paragraphs 1--2 through the factorization; Tag 080D (1)
(blueprint: lem-trf-strict-transform-comparison-epimorphism).

Proof: the iterated-transform quotient/support lemma gives quasi-coherence of both
successive transforms, surjectivity of the composite quotient alpha, and vanishing of
its kernel off the union of the two inverse-image centres. The strict-transform
sheaf-kernel lemma gives quasi-coherence of the transported single transform G and
surjectivity of beta, whose kernel consists of sections vanishing off D. The equality
V(K) = V(I) union b(V(J)) puts both inverse-image centres inside D; hence each local
section killed by alpha is killed by beta. Locally lift sections along alpha and apply
beta to those lifts. Kernel containment makes these values independent of lifts and
allows gluing, yielding the unique linear comparison theta with alpha theta = beta.
Local lifting along beta makes theta epimorphic. Off D both alpha and beta are
isomorphisms, so theta is an isomorphism there and each section of its kernel vanishes
there. The quasi-coherence proof h₁ is quantified existentially to state, rather than
assume, quasi-coherence of the first strict transform. -/
theorem successiveModuleStrictTransform_comparison_epimorphism
    {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (J : I.blowup.IdealSheafData) [J.toModules.IsFiniteType]
    (K : S.IdealSheafData) [K.toModules.IsFiniteType]
    (e : J.blowup ≅ K.blowup) (he : e.hom ≫ K.blowupMap = J.blowupMap ≫ I.blowupMap)
    (hK : (K.support : Set S) = (I.support : Set S) ∪ I.blowupMap '' (J.support : Set I.blowup))
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ h₁ : (moduleStrictTransform f I F).IsQuasicoherent,
      (successiveModuleStrictTransform f I J F h₁).IsQuasicoherent ∧
      (compositeModuleStrictTransform f I J K e he F).IsQuasicoherent ∧
      Epi (successiveModuleStrictTransformπ f I J F h₁) ∧
      Epi (compositeModuleStrictTransformπ f I J K e he F) ∧
      (∀ (V : (Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap).Opens)
        (s : Γ((tensorPullback
          (pullback.fst (pullback.snd f I.blowupMap) J.blowupMap)).obj
            ((tensorPullback (pullback.fst f I.blowupMap)).obj F), V)),
        (successiveModuleStrictTransformπ f I J F h₁).app V s = 0 →
          (compositeModuleStrictTransformπ f I J K e he F).app V s = 0) ∧
      ∃! θ : successiveModuleStrictTransform f I J F h₁ ⟶
          compositeModuleStrictTransform f I J K e he F,
        successiveModuleStrictTransformπ f I J F h₁ ≫ θ =
          compositeModuleStrictTransformπ f I J K e he F ∧
        Epi θ ∧
        ∀ (V : (Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap).Opens)
          (s : Γ(successiveModuleStrictTransform f I J F h₁, V)),
          θ.app V s = 0 →
            ((restrictAdjunction
              ((pullback.fst (pullback.snd f I.blowupMap) J.blowupMap ≫
                pullback.fst f I.blowupMap ≫ f) ⁻¹ᵁ K.support.compl).ι).unit.app
                  (successiveModuleStrictTransform f I J F h₁)).app V s = 0 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
