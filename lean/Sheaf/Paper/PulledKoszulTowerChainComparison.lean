/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.PulledKoszulTowerNormalization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.AdicCoefficientDatum
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.Paper.PrincipalKoszulStrictReplacement
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Sheaf.Paper.KFlatRingedToposPullback
import all Sheaf.Paper.IntegralCompletedTowerPullbackUniverses
import all Sheaf.SecSmoothPurity.CochainCompositeAlgebraic
import Sheaf.Paper.PulledKoszulTowerNormalizedIso
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Ordinary pullback of the principal Koszul tower

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E and 07A4;
sites-modules.tex, Tag 03EL; homology.tex, Tag 02MZ
(blueprint: lem-a1-pulled-koszul-tower-chain-comparison).

The natural number n denotes the positive exponent n+1. The normalization is the
existing equation on both Koszul basis vectors and every local coefficient b.
The generators and normalization belong to the independent definition module
PulledKoszulTowerNormalization, with no import of the downstream comparison theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.PrincipalKoszulStrictReplacement
open WeilConjectures.PulledKoszulTowerModel

namespace WeilConjectures

-- Stacks 0G7E for the specified completed-ring pullback. Present it as
-- inverse image followed by scalar extension, then compare left adjoints of
-- the same pushforward. K-flatness and degreewise flatness transport across
-- this natural isomorphism.
private theorem completed_pull_good
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{t}} (g : X ⟶ Y)
    (P : CochainComplex (CompletedTowerIndependent.Modules l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) :
    integralOperationsGoodComplex l E X ((G l E g).obj P) := by
  classical
  let U := Scheme.proEtaleBaseChange g
  let J := Scheme.ProEt.topology Y
  let K := Scheme.ProEt.topology X
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let S := completedIntegralCommRingSheafUnrestricted l E X
  have : HasColimitsOfSize.{t, t + 1} (Type (max u (t + 1))) :=
    hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  let L := Functor.sheafPullbackConstruction.sheafPullback U
    (Type (max u (t + 1))) J K
  let V := U.sheafPushforwardContinuous (Type (max u (t + 1))) J K
  let adj : L ⊣ V := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
    (Type (max u (t + 1))) J K
  have : AB5OfSize.{t, t + 1} (Type (max u (t + 1))) :=
    AB5OfSize_shrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  have : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  have : PreservesFiniteLimits (U.op.lan :
      (Y.ProEtᵒᵖ ⥤ Type (max u (t + 1))) ⥤ X.ProEtᵒᵖ ⥤ Type (max u (t + 1))) :=
    preservesFiniteLimits_op_lan_of_flat U
  have : PreservesFiniteLimits L := by
    dsimp only [L, Functor.sheafPullbackConstruction.sheafPullback]
    infer_instance
  have : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let RI := SheafOfModules.CochainCompositeConstruction.ringImage L R
  let I := SheafOfModules.CochainCompositeConstruction.algebraicImage L R
  let φ : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{max u (t + 1)} J K).obj S :=
    (sheafCompose J (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).preimage (directRingMap l E g)
  have hφ : (sheafCompose J (forget₂ CommRingCat RingCat)).map φ = directRingMap l E g :=
    Functor.map_preimage _ _
  obtain ⟨c, hc⟩ := IndependentSite.siteStructuralMap_exists U L adj S R φ RI I
  obtain ⟨am⟩ := IndependentSite.supplied_adjunction U L adj S R φ RI I c hc
  let T := I.modules ⋙ IndependentSite.tensorFunctor (K := K) (A := RI) (S := S) c
  have ham : T ⊣ push l E g := by
    change I.modules ⋙ IndependentSite.tensorFunctor (K := K) (A := RI) (S := S) c ⊣
      SheafOfModules.pushforward (directRingMap l E g)
    rw [← hφ]
    exact am
  have : T.Additive := by
    have : (push l E g).Additive := by
      constructor
      intro M N f h
      ext U x
      rfl
    exact ham.left_adjoint_additive
  have hobj (M) : T.obj M = SheafOfModules.changeOfRings c (I.modules.obj M) := rfl
  have hmap {M N} (a : M ⟶ N) : T.map a = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hk := SheafOfModules.isKFlat_ringedToposPullback L V adj I c T hobj hmap
    P hP.1 hP.2
  let e := (adjunction l E g).leftAdjointUniq ham
  let eP := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  refine ⟨SheafOfModules.kFlat_iso_independent S eP.symm hk.1, ?_⟩
  intro n
  exact SheafOfModules.flatOnSite_of_iso S
    ((HomologicalComplex.eval _ _ n).mapIso eP.symm) (hk.2 n)

/-- Ordinary completed-ring pullback preserves good complexes and identifies the
strict principal Koszul towers, with their specified basis normalization. The
augmentation is the target quotient augmentation and is a quasi-isomorphism both
at each level and after transposition to complexes of strict towers.

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E and 07A4;
sites-modules.tex, Tag 03EL; homology.tex, Tag 02MZ
(blueprint: lem-a1-pulled-koszul-tower-chain-comparison).

Proof:
1. The ordinary tensor and basis calculation is supplied by
   lem-a1-pulled-koszul-tower-normalized-iso, for all complexes. Restrict its
   family to the good complexes; its normalization and naturality remain.
2. Present the actual completed-ring pullback as algebraic inverse image
   followed by scalar extension, using the completed structural map. Its
   adjunction identifies it with the specified functor pull, by uniqueness of
   left adjoints. Apply lem-weil-pbc-ringed-pullback-preserves-kflat, then
   transport K-flatness and termwise flatness across this isomorphism.
3. Apply lem-a1-principal-koszul-strict-replacement on Y to see that each
   P tensor Q_n is good; step 2 gives goodness after pullback. Apply that
   replacement theorem again on X to GP. This proves that the actual target
   augmentation is a quasi-isomorphism at each level. Its chain-map naturality
   is precisely PrincipalKoszulStrictReplacement.comparison_naturality.
4. Apply HomologicalComplex.quasiIso_iff_evaluation to the transposed
   augmentation. Evaluation is exactly the level augmentation from step 3,
   so the augmentation is also a quasi-isomorphism in the strict tower category.
-/
theorem pulled_koszul_tower_chain_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{t}} (g : X ⟶ Y)
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ θ : ∀ (P : CochainComplex (CompletedTowerIndependent.Modules l E Y) ℤ),
        integralOperationsGoodComplex l E Y P →
          ((diagramPull l E g).obj (H l E Y P) ≅ H l E X ((G l E g).obj P)),
      ∀ (P : CochainComplex (CompletedTowerIndependent.Modules l E Y) ℤ)
        (hP : integralOperationsGoodComplex l E Y P),
        integralOperationsGoodComplex l E X ((G l E g).obj P) ∧
        (∀ n : ℕ, integralOperationsGoodComplex l E X
          (((diagramPull l E g).obj (H l E Y P)).obj (op n))) ∧
        KoszulNormalization l E g P (θ P hP) ∧
        (∀ (P' : CochainComplex (CompletedTowerIndependent.Modules l E Y) ℤ)
          (hP' : integralOperationsGoodComplex l E Y P') (f : P ⟶ P'),
          Functor.whiskerRight (sourceTowerMap l E Y f) (G l E g) ≫ (θ P' hP').hom =
            (θ P hP).hom ≫ sourceTowerMap l E X ((G l E g).map f)) ∧
        (∀ n : ℕ, QuasiIso
          ((PrincipalKoszulStrictReplacement.comparison l E X ((G l E g).obj P)).app
            (op n))) ∧
        QuasiIso ((transpose l E X).map
          (PrincipalKoszulStrictReplacement.comparison l E X ((G l E g).obj P))) ∧
        (∀ (P' : CochainComplex (CompletedTowerIndependent.Modules l E Y) ℤ)
          (_hP' : integralOperationsGoodComplex l E Y P') (f : P ⟶ P'),
          sourceTowerMap l E X ((G l E g).map f) ≫
              PrincipalKoszulStrictReplacement.comparison l E X ((G l E g).obj P') =
            PrincipalKoszulStrictReplacement.comparison l E X ((G l E g).obj P) ≫
              targetTowerMap l E X ((G l E g).map f)) := by
  have _hX := hX
  have _hY := hY
  obtain ⟨θ, hnorm, hnat⟩ := pulled_koszul_tower_normalized_iso l E g
  refine ⟨fun P _ ↦ θ P, ?_⟩
  intro P hP
  have hGP := completed_pull_good l E g P hP
  have hlevels := principal_koszul_strict_replacement l E X
    ((G l E g).obj P) hGP.1 hGP.2
  refine ⟨hGP, ?_, hnorm P, ?_, fun n ↦ (hlevels n).1, ?_, ?_⟩
  · intro n
    have hsource := principal_koszul_strict_replacement l E Y P hP.1 hP.2 n
    exact completed_pull_good l E g ((H l E Y P).obj (op n)) hsource.2
  · intro P' _ f
    exact hnat f
  · apply (HomologicalComplex.quasiIso_iff_evaluation _).2
    intro n
    exact (hlevels n.unop).1
  · intro P' _ f
    exact comparison_naturality l E X ((G l E g).map f)

end WeilConjectures
