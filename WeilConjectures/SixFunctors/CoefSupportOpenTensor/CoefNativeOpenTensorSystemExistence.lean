/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.NativeOpenTensorPrimitives.CoefNativeOpenTensorPrimitives
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeOpenTensorOrdinarySupported
import all WeilConjectures.Algebra.Homology.CochainCompositeConstruction.CochainCompositeAlgebraic
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeOpenTensorTotalization
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeOpenTensorRestriction
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingTensorComparison
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenOperationModels

/-! # Existence of the sequence-site native open tensor datum

This is the sequence-site part of the construction of [Stacks, Tag 0GL1], separated from the
finite coefficient stages: the localized sequence sites admit the ordinary native open tensor
datum.

## Implementation details

Localize the ambient pro-étale site at the open object; the coefficient ring on the open is the
restricted ambient coefficient ring, and restriction and extension are transported along these
identifications, with the native module direct image as right adjoint. Restriction of tensor
products is computed on pure tensors and sheafified, and pullback preservation of flat-term
K-flat complexes gives the flatness fields.

For `M` on the open and `N` on the ambient site, the localized extension/tensor formula
identifies the transposed comparison with the inverse of the projection isomorphism, since both
send a pure tensor to the unit insertion of its first factor tensored with the second. In total
degree `k` one takes the direct sum over `a + b = k` of these ordinary comparisons, which
commute with the differentials.

The construction is carried out on the product with the coefficient index, with its vertical
covering topology. On horizontal arrows every map is the same tensor or direct-sum insertion
with the coefficient quotient applied, so the quotient squares follow from functoriality and no
separate choice of data at each finite stage is used. The empty open gives zero extensions;
zero rings and unbounded complexes are covered by the same universal properties.

## References

* [Stacks, Tag 0E8I]
* [Stacks, Tag 0GL1]
* [Stacks, Tag 0G7E]
* [Stacks, Tag 012Z]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open WeilConjectures WeilConjectures.SemilinearSections
open AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization.GeneralizedRinged
open AlgebraicGeometry.ProEtale.VaryingRing
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
  WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.sequenceSmall WeilConjectures.SemilinearSections.sliceSmall
attribute [local irreducible] SheafOfModules.monoidalCategory Functor.leftAdjoint

/-- Transpose a natural transformation through an adjunction. -/
private def transposeNatural
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ A} (a : F ⊣ G) {P : C ⥤ A} {Q : C ⥤ B}
    (t : P ⟶ Q ⋙ G) : P ⋙ F ⟶ Q where
  app X := (a.homEquiv _ _).symm (t.app X)
  naturality _ _ f := a.homEquiv_naturality_right_square _ _ _ _ (t.naturality f)

/-- An invertible adjunct with supported target has invertible transpose. -/
private theorem isIso_of_adjunct
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (a : F ⊣ G) [IsIso a.unit] {X : B} {Y : A} (f : F.obj Y ⟶ X)
    (hf : IsIso (a.homEquiv _ _ f)) (hs : F.essImage X) : IsIso f := by
  have : F.Full := a.fullyFaithfulLOfIsIsoUnit.full
  have : F.Faithful := a.fullyFaithfulLOfIsIsoUnit.faithful
  have : IsIso (a.counit.app X) := a.isIso_counit_app_iff_mem_essImage.mpr hs
  have := hf
  have he : f = F.map (a.homEquiv _ _ f) ≫ a.counit.app X :=
    ((a.homEquiv _ _).symm_apply_apply f).symm
  rw [he]
  infer_instance

private theorem ordinary_exists
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    (F : A ⥤ B) (G : B ⥤ A) (adj : F ⊣ G) [IsIso adj.unit]
    (rho : ∀ M N : B, G.obj (M ⊗ N) ≅ G.obj M ⊗ G.obj N)
    (hn : ∀ {M M' N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      G.map (f ⊗ₘ g) ≫ (rho M' N').hom = (rho M N).hom ≫ (G.map f ⊗ₘ G.map g))
    (hs : ∀ M N, F.essImage (F.obj M ⊗ N)) :
    ∃ ordinary : ∀ M N, F.obj M ⊗ N ≅ F.obj (M ⊗ G.obj N),
      (∀ M N, adj.homEquiv _ _ (ordinary M N).inv =
        (adj.unit.app M ⊗ₘ 𝟙 (G.obj N)) ≫ (rho (F.obj M) N).inv) ∧
      (∀ {M M' : A} {N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
        (F.map f ⊗ₘ g) ≫ (ordinary M' N').hom =
          (ordinary M N).hom ≫ F.map (f ⊗ₘ G.map g)) := by
  let c : tensor B ⋙ G ≅ G.prod G ⋙ tensor A := NatIso.ofComponents
    (fun X ↦ rho X.1 X.2) (fun f ↦ hn f.1 f.2)
  let tau : (𝟭 A).prod G ⋙ tensor A ⟶ (F.prod (𝟭 B) ⋙ tensor B) ⋙ G :=
    { app X := (adj.unit.app X.1 ⊗ₘ 𝟙 (G.obj X.2)) ≫ c.inv.app (F.obj X.1, X.2)
      naturality X Y f := by
        have he : Prod.mkHom f.1 (G.map f.2) ≫
              Prod.mkHom (adj.unit.app Y.1) (𝟙 _) =
            Prod.mkHom (adj.unit.app X.1) (𝟙 _) ≫
              (G.prod G).map (Prod.mkHom (F.map f.1) f.2) := by
          ext
          · exact adj.unit.naturality f.1
          · simp
        change (tensor A).map (Prod.mkHom f.1 (G.map f.2)) ≫
            ((tensor A).map (Prod.mkHom (adj.unit.app Y.1) (𝟙 _)) ≫
              c.inv.app (F.obj Y.1, Y.2)) =
          ((tensor A).map (Prod.mkHom (adj.unit.app X.1) (𝟙 _)) ≫
            c.inv.app (F.obj X.1, X.2)) ≫ G.map (F.map f.1 ⊗ₘ f.2)
        dsimp only [Functor.prod_map, Functor.id_map, Functor.comp_map]
        rw [← Category.assoc, ← (tensor A).map_comp, he, (tensor A).map_comp,
          Category.assoc, Category.assoc]
        congr 1
        exact c.inv.naturality (Prod.mkHom (F.map f.1) f.2) }
  let t := transposeNatural adj tau
  have ht (X : A × B) : IsIso (t.app X) := by
    apply isIso_of_adjunct adj _ _ (hs X.1 X.2)
    change IsIso (adj.homEquiv _ _ ((adj.homEquiv _ _).symm (tau.app X)))
    rw [Equiv.apply_symm_apply]
    let q : (X.1, G.obj X.2) ⟶ (G.obj (F.obj X.1), G.obj X.2) :=
      Prod.mkHom (adj.unit.app X.1) (𝟙 _)
    have : IsIso q := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    change IsIso ((tensor A).map q ≫ c.inv.app (F.obj X.1, X.2))
    infer_instance
  let : IsIso t := NatIso.isIso_of_isIso_app _
  let e := (asIso t).symm
  refine ⟨fun M N ↦ e.app (M, N), ?_, ?_⟩
  · intro M N
    exact Equiv.apply_symm_apply _ _
  · intro M M' N N' f g
    exact e.hom.naturality (Prod.mkHom f g)

namespace WeilConjectures.CoefSupportOpenTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

-- The original existential statement names a witness unused by True.
set_option linter.unusedVariables false in
/-- The localized sequence sites admit the ordinary native open tensor datum. -/
theorem nativeOpenTensor_system_exists {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] :
    ∃ D : NativeOpenTensorPrimitives.SystemOpenCochainsData l E j, True := by
  classical
  let J := coefficientSequenceTopology (ProEt.topology Z)
  let K := coefficientSequenceTopology (ProEt.topology X)
  let RZ := coefficientSequenceCommRingSheaf.{u, u} l E Z
  let RX := coefficientSequenceCommRingSheaf.{u, u} l E X
  let g := ProEtale.VaryingRing.baseChange j
  let F : SemilinearSections.Mod K RX ⥤ SemilinearSections.Mod J RZ :=
    ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j
  let G : SemilinearSections.Mod J RZ ⥤ SemilinearSections.Mod K RX :=
    ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j
  let adj : F ⊣ G := ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j
  let aG : G ⊣ ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j :=
    ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j
  let hF : F.Additive := ProEtale.VaryingRing.extensionAdditive (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j
  let hG : G.Additive := ProEtale.VaryingRing.pullAdditive (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j
  have : RepresentablyFlat (Scheme.proEtaleBaseChange j) := flat_of_preservesFiniteLimits _
  have : RepresentablyFlat g := by
    constructor
    intro U
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence U.1 U.2 (𝟭 ℕ) (Scheme.proEtaleBaseChange j)).symm
  have : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  let L := Functor.sheafPullbackConstruction.sheafPullback g (Type (u + 1)) J K
  let a : L ⊣ g.sheafPushforwardContinuous (Type (u + 1)) J K :=
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    g (Type (u + 1)) J K
  have : PreservesFiniteLimits L := by dsimp only [L]; infer_instance
  let := BraidedCategory.ofCartesianMonoidalCategory (C := Sheaf J (Type (u + 1)))
  let := BraidedCategory.ofCartesianMonoidalCategory (C := Sheaf K (Type (u + 1)))
  let : L.Monoidal := Functor.Monoidal.ofChosenFiniteProducts L
  have : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let RI := SheafOfModules.CochainCompositeConstruction.ringImage L RZ
  let I : SheafOfModules.AlgebraicInverseImage L RZ RI :=
    SheafOfModules.CochainCompositeConstruction.algebraicImage L RZ
  clear_value I RI a L
  have : F.Additive := hF
  have : G.Additive := hG
  let φ := ProEtale.VaryingRing.commutativeRingMap (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j
  obtain ⟨c, hc⟩ :=
    SheafOfModules.OpenTensorNormalization.GeneralizedRinged.siteStructuralMap_exists
      g L a RX RZ φ RI I
  obtain ⟨rho, hn, hp, hf⟩ :=
    nativeOpenTensor_restriction_exists J K g RZ RX φ L a RI I c hc G aG (hAdd := hG)
  let : MonoidalCategory (coefficientSequenceModules.{u, u} l E X) :=
    SheafOfModules.cochainModulesMonoidal RX
  let : MonoidalCategory (coefficientSequenceModules.{u, u} l E Z) :=
    SheafOfModules.cochainModulesMonoidal RZ
  let : IsIso adj.unit := ProEtale.VaryingRing.moduleJAdj_unit_isIso
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  obtain ⟨ordinary, hi, ho⟩ := ordinary_exists F G adj rho hn
    (nativeOpenTensor_ordinary_supported l E j)
  obtain ⟨chain, hs, hc⟩ :=
    nativeOpenTensor_totalization_exists.{u + 1, u, u} J RZ K RX F G
      (hF := hF) (hG := hG) adj ordinary ho
  refine ⟨{
    right := ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j
    pullAdjunction := aG
    pullTensor := rho
    pullNaturality := hn
    pullPure := hp
    pullKFlat := fun P hP hflat ↦ (hf P hP hflat).1
    pullFlat := fun P hP hflat ↦ (hf P hP hflat).2
    ordinary := ordinary
    ordinaryInverse := hi
    ordinaryNaturality := ho
    chain := chain
    summand := hs
    chainNaturality := hc
  }, trivial⟩

end WeilConjectures.CoefSupportOpenTensor
