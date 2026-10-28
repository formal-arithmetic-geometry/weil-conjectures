/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W5
-/
module

public import Sheaf.Paper.ConstantAdicQuotientScalarComparison
import all Sheaf.Paper.AdicLisseRelativeRestriction
import all Sheaf.Paper.PbcFinitePullbackConstructibility
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Isomorphism reflection for a constant adic quotient realization map -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem constantSheaf_faithful_of_point (Z : Scheme.{u}) (z : Z)
    (B : Type (u + 1)) [CommRing B] :
    (constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} B)).Faithful := by
  let J := ProEt.topology Z
  let U : Z.ProEt := ProEt.mk (𝟙 Z)
  have hbot : (⊥ : Sieve U) ∉ J U := by
    intro h
    obtain ⟨Q, hQ, hQS⟩ := ProEt.mem_topology_iff.mp h
    obtain ⟨ι, V, f, rfl⟩ := Q.exists_eq_ofArrows
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hQ
    obtain ⟨i, y, hy⟩ :=
      ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 hQ.2).1 z
    have hf := hQS _ _ (Presieve.ofArrows.mk i)
    simp at hf
  have hinj (M : ModuleCat.{u + 1} B) : Function.Injective
      ((toSheafify J ((Functor.const Z.ProEtᵒᵖ).obj M)).app (op U)) := by
    intro a b hab
    have hS := Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const Z.ProEtᵒᵖ).obj M)) a b hab
    by_contra hab'
    apply hbot
    convert hS using 1
    ext V g
    simp only [Sieve.bot_apply, Presheaf.equalizerSieve_apply, false_iff]
    exact hab'
  refine ⟨fun {M N} f g h ↦ ?_⟩
  ext x
  apply hinj N
  have hn (k : M ⟶ N) := congrArg (fun t ↦ t.app (op U))
    (toSheafify_naturality J ((Functor.const Z.ProEtᵒᵖ).map k))
  have he := congrArg (fun t ↦ t.hom.app (op U)) h
  exact (ConcreteCategory.congr_hom (hn f) x).trans
    ((congrArg (fun k ↦ k
      ((toSheafify J ((Functor.const Z.ProEtᵒᵖ).obj M)).app (op U) x)) he).trans
      (ConcreteCategory.congr_hom (hn g) x).symm)

/--
The reflection step for the point-stalk extraction argument: a morphism of
derived coefficient objects is an isomorphism when its constant adic quotient
realization is an isomorphism.

Source: Stacks Project, sites-modules.tex, Tags 093J and 03DH; proetale.tex,
Tag 03Q3.
(blueprint: lem-weil-pbc-constant-adic-quotient-realization-reflects-iso-of-map).

Proof: encode the pulled-back coefficients as sheaves of modules over
`A/I^(n+1)`. Scalar restriction commutes with inverse image, the finite
coefficient comparison cancels its inverse, and inverse image preserves constant
sheaves. Thus the ordinary realization, followed by this encoding, is restriction
of scalars followed by the constant-sheaf functor on `W.left`. Constant sections
on this nonempty scheme are injective: local equality of two distinct constants
would make the empty sieve covering. Both functors are faithful, so the ordinary
realization is faithful and reflects isomorphisms of modules. It is exact;
its derived functor commutes with homology, and the unbounded derived homology
criterion therefore reflects the given isomorphism.
-/
theorem constantAdicQuotientRealization_reflects_iso_of_map
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (W : Y.Etale) (_w : W.left)
    (E F : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (f : E ⟶ F)
    (hf : IsIso ((constantAdicQuotientRealization (W.hom ≫ g) d n).map f)) :
    IsIso f := by
  let h := W.hom ≫ g
  let B := A ⧸ d.ideal ^ (n + 1)
  let Q := ModuleCat.restrictScalars (constantAdicQuotientMap d.ideal n)
  let L := adicLisseConstantModules X B
  let C := constantAdicQuotientModules X d n
  let e := pbcLevelConstantComparison X d n
  let R := pbcRestrict e.hom
  let T := pbcRestrict ((adicTowerInverseImage h).map e.hom)
  let P := proEtaleRingModulePullback h ((pbcAdicRings X d).obj (op n))
    ((adicTowerInverseImage h).obj ((pbcAdicRings X d).obj (op n))) (Iso.refl _)
  let P₀ := proEtaleRingModulePullback h (adicLisseConstantRing X B)
    ((adicTowerInverseImage h).obj (adicLisseConstantRing X B)) (Iso.refl _)
  let S := relativeRestriction h B
  let S₀ := scalarRestriction X B
  let V := ProEtale.upperStar (ModuleCat.{u + 1} B) h
  let c := proEtaleRingRestrictionPullbackInv h _ _
    ((adicTowerInverseImage h).obj _) ((adicTowerInverseImage h).obj _)
    e.hom ((adicTowerInverseImage h).map e.hom) (Iso.refl _) (Iso.refl _) (by simp)
  have : IsIso c := proEtaleRingRestrictionPullbackInv_isIso h _ _
    ((adicTowerInverseImage h).obj _) ((adicTowerInverseImage h).obj _)
    e.hom ((adicTowerInverseImage h).map e.hom) (Iso.refl _) (Iso.refl _) (by simp)
  let c₀ : P ⋙ T ≅ R ⋙ P₀ := (asIso c).symm
  let a := (proEtaleModuleInverseImageAdjunction h (adicLisseConstantRing X B)).leftAdjointUniq
    (proEtaleRingModuleAdjunction h (adicLisseConstantRing X B)
      ((adicTowerInverseImage h).obj (adicLisseConstantRing X B)) (Iso.refl _))
  let c₁ : P₀ ⋙ S ≅ S₀ ⋙ V :=
    Functor.isoWhiskerRight a.symm S ≪≫ relativeEncoding h B
  let q := proEtaleScalarEquivalence X ((adicLisseForget X).mapIso e)
  let c₂ : (C ⋙ R) ⋙ S₀ ≅ Q ⋙ constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} B) :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (Q ⋙ L) q.counitIso) S₀ ≪≫
      Functor.isoWhiskerLeft Q (constantEncodingNatIso X B).symm
  let c₃ : constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} B) ⋙ V ≅
      constantSheaf (ProEt.topology W.left) (ModuleCat.{u + 1} B) :=
    (((constantSheafΓAdj _ (ModuleCat.{u + 1} B)).comp
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) h)).ofNatIsoRight
        (ProEtale.globalSectionsLowerStarIso (ModuleCat.{u + 1} B) h)).leftAdjointUniq
          (constantSheafΓAdj _ (ModuleCat.{u + 1} B))
  let c₄ : (C ⋙ P) ⋙ T ⋙ S ≅
      Q ⋙ constantSheaf (ProEt.topology W.left) (ModuleCat.{u + 1} B) :=
    Functor.isoWhiskerLeft C (Functor.isoWhiskerRight c₀ S) ≪≫
      Functor.isoWhiskerLeft (C ⋙ R) c₁ ≪≫
        Functor.isoWhiskerRight c₂ V ≪≫ Functor.isoWhiskerLeft Q c₃
  have : (constantSheaf (ProEt.topology W.left) (ModuleCat.{u + 1} B)).Faithful :=
    constantSheaf_faithful_of_point W.left _w B
  have : ((C ⋙ P) ⋙ T ⋙ S).Faithful := Functor.Faithful.of_iso c₄.symm
  have : (C ⋙ P).Faithful := Functor.Faithful.of_comp (C ⋙ P) (T ⋙ S)
  have : IsIso ((C ⋙ P).mapDerivedCategory.map f) :=
    (NatIso.isIso_map_iff (Functor.mapDerivedCategoryCompIso C P) f).2 hf
  apply (DerivedCategory.isIso_iff _ f).2
  intro i
  have : IsIso ((C ⋙ P).map ((DerivedCategory.homologyFunctor _ i).map f)) :=
    (NatIso.isIso_map_iff ((C ⋙ P).mapDerivedCategoryHomologyFunctorIso i) f).2 (by
      change IsIso ((DerivedCategory.homologyFunctor _ i).map
        ((C ⋙ P).mapDerivedCategory.map f))
      infer_instance)
  exact isIso_of_reflects_iso _ (C ⋙ P)

end AlgebraicGeometry.Scheme
