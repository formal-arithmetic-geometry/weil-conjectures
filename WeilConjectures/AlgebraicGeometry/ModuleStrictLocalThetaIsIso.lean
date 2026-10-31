/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.ModuleStrictLocalRestriction
import WeilConjectures.AlgebraicGeometry.ModuleStrictLocalRestrictionIsIso
import WeilConjectures.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeGlobalHomology
import all WeilConjectures.AlgebraicGeometry.StrictLocalOrdinaryDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility

/-! # Invertibility of the module strict-local comparison

Source: Stacks Tags 03Q9, 03FD and 07A7; the small-model base-change theorem and
canonical coefficient-forgetting compatibility.
(blueprint: new-pur-module-strict-local-theta-is-iso).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The specified module derived exchange is invertible on strict-local global cohomology.
Source: Stacks Tags 03Q9, 03FD and 07A7
(blueprint: new-pur-module-strict-local-theta-is-iso).

Proof: the small-model abelian theorem makes the mate invertible after cohomology and
strict-local sections. The resolution characterization identifies that mate with the
specified derived exchange. The canonical coefficient comparisons identify forgotten
module exchange with abelian exchange, up to isomorphisms on both endpoints. Apply
cohomology and sections and cancel the endpoint maps. Exact coefficient forgetting
commutes with cohomology, so this proves invertibility after forgetting the cohomology
map. Global sections commute with forgetting modules by their terminal-section
comparisons. The module forgetful functor reflects isomorphisms, which proves the claim.
-/
private theorem moduleStrictLocalExchange_globalHomology_isIso
    (A : Type (u + 1)) [CommRing A] {X B : Scheme.{u}}
    (f : X ⟶ B) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (q : ℤ) :
    IsIso ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      (ModuleCat.{u + 1} A)).map
      ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback f
            (Scheme.strictHenselizationStructuralMap s)).toCommSq).app K))) := by
  let T := Scheme.strictHenselizationScheme s
  let g := Scheme.strictHenselizationStructuralMap s
  let sq := (IsPullback.of_hasPullback f g).toCommSq
  let U := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}
  let V := moduleAbelianForget A T
  let G := Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)
  let G₀ := Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) q
  let H₀ := DerivedCategory.Plus.homologyFunctor
    (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) q
  let L := H₀ ⋙ G₀
  let δ := (derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq).app K
  have ha := smallModel_isIso_strictHenselization_baseChange_globalHomology f s
    ((moduleAbelianForget A X).mapDerivedCategoryPlus.obj K) q
  rw [mate_eq_derivedExchange] at ha
  have hab : IsIso (L.map ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
      ((moduleAbelianForget A X).mapDerivedCategoryPlus.obj K))) := ha
  have hc := congrArg L.map (moduleAbelianDerivedExchange_compatibility A sq K)
  simp only [Functor.map_comp] at hc
  have hi : IsIso (L.map (V.mapDerivedCategoryPlus.map δ)) := by
    have hcomp : IsIso (L.map (V.mapDerivedCategoryPlus.map δ) ≫
        L.map (moduleAbelianDerivedExchangeTargetIso A (pullback.fst f g)
          (pullback.snd f g) K).hom) := by
      rw [hc]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (L.map (moduleAbelianDerivedExchangeTargetIso A (pullback.fst f g)
        (pullback.snd f g) K).hom)
  have hforgot : IsIso (G₀.map (V.map (H.map δ))) :=
    (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight (V.mapDerivedCategoryPlusHomologyFunctorIso q) G₀) δ).2 hi
  let hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T
  let e : G ⋙ U ≅ V ⋙ G₀ :=
    Functor.isoWhiskerRight
      (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A) hT) U ≪≫
    (Iso.refl _) ≪≫
    Functor.isoWhiskerLeft V
      (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology AddCommGrpCat.{u + 1} hT).symm
  have : IsIso (U.map (G.map (H.map δ))) := (NatIso.isIso_map_iff e (H.map δ)).2 hforgot
  exact isIso_of_reflects_iso _ U

/-- The specified strict-local restriction, derived exchange, coefficient transport and
Leray comparison is an isomorphism for a quasi-compact quasi-separated morphism.
Source: Stacks Tags 03Q9, 03FD and 07A7
(blueprint: new-pur-module-strict-local-theta-is-iso).

Proof: the module restriction to the strict localization is an isomorphism by the
pointed-neighbourhood colimit calculation. For exchange, forget coefficients and use
the small-model abelian base-change theorem after cohomology and sections; canonical
coefficient comparisons and reflection of isomorphisms give the module assertion.
Exactness of strict-local sections identifies its derived functor with its direct
extension, and identifies the latter's cohomology with sections of cohomology. Thus
exchange becomes an isomorphism under derived global sections. The specified Theta
is the composite of these two isomorphisms, coefficient transport and Leray, so is
itself an isomorphism. -/
theorem moduleStrictLocalTheta_isIso
    (A : Type (u + 1)) [CommRing A] {X B : Scheme.{u}} (f : X ⟶ B)
    [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K' : DerivedCategory.Plus
      (Sheaf (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} A)))
    (e : (upperStar (ModuleCat.{u + 1} A)
        (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus.obj
          K ≅ K') :
    IsIso (moduleStrictLocalTheta A f s K K' e) := by
  let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
    (ModuleCat.{u + 1} A)
  let δ := (derivedBaseChangeMapPlus (ModuleCat.{u + 1} A)
    (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq).app K
  have hδ : IsIso (G.rightDerivedFunctorPlus.map δ) := by
    apply (NatIso.isIso_map_iff G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus δ).2
    apply (DerivedCategory.Plus.isIso_iff _).2
    intro q
    exact (NatIso.isIso_map_iff (G.mapDerivedCategoryPlusHomologyFunctorIso q) δ).1
      (moduleStrictLocalExchange_globalHomology_isIso A f s K q)
  have : IsIso (moduleStrictLocalDerivedRestriction A s) :=
    (moduleStrictLocalRestriction_isIso A s).2
  unfold moduleStrictLocalTheta
  change IsIso (_ ≫ G.rightDerivedFunctorPlus.map δ ≫ _ ≫ _)
  infer_instance

end AlgebraicGeometry.Etale
