/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingCompactificationCoherence
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
public import WeilConjectures.CategoryTheory.BrownHypothesesStatement
public import WeilConjectures.CategoryTheory.BrownRepresentabilityHomLocallySmall
public import WeilConjectures.CategoryTheory.CompactTestsRightAdjointCoproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/--
Existence of the exceptional inverse image on the localizing constructible categories.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-brown-representability-for-all-coefficient-rings/sk-prop-sf-existence/_section.md,
entire statement, and both paragraphs of `sk-prop-sf-existence.proof.md`; standing base
field: part-six-operations/prose-P1-01.md, final paragraph (finite or algebraically
closed), and det-def-sfb-dc-setting; Stacks Tags 0A8F, 0A8G, 0A8D.
The functor in the statement is the compact-support functor supplied by
`sk-prop-sf-comp-coherence`; its displayed adjunction is natural in both objects.  The
uniqueness clause is uniqueness of a right adjoint together with its counit.
(blueprint: sk-prop-sf-existence)

Proof:
1. Put `T_Z = Loc(Dctf(Z, Λ))` for `Z = X, Y`.  By sk-lem-brown-hypotheses, applied
   separately at `X` and `Y` in the standing setting, `T_Z` is locally small and
   triangulated with arbitrary small coproducts, `Dctf(Z, Λ)` is thick and essentially
   small, and a small skeleton is a set of compact generators.  By
   sk-prop-sf-comp-coherence, `F = Rf_! = Rp_* j_!` for the fixed compactification is
   exact, preserves direct sums, and maps `Dctf(X, Λ)` into `Dctf(Y, Λ)`.
2. For `N ∈ T_Y`, lem-pc-brown-hom-representability-locally-small represents the
   cohomological sum-to-product functor `M ↦ Hom(F M, N)` by `G_N ∈ T_X`;
   lem-sfb-right-adjoint-from-objectwise-representability assembles them into
   `G : T_Y ⥤ T_X` with `F ⊣ G`.  Set `f^! = G`.
3. lem-weil-pbc-adjunction-shift-compatibility-unique supplies the shifts on `G`
   compatible with unit and counit; lem-sf-triangulated-right-adjoint makes `G` exact;
   det-sp-unique-right-adjoint gives the unique counit-compatible isomorphism to any
   other right adjoint.
4. For a small family `N_α`, the comparison `⨁ G N_α ⟶ G (⨁ N_α)` induces a bijection on
   `Hom(S[n], -)` for each `S ∈ Dctf(X, Λ)`, since `S[n]` and `F(S[n])` are compact
   (def-pc-compact-object) and both sides are `⨁ Hom(F S[n], N_α)` by adjunction.
   lem-sf-localizing-hom-test in `T_X`, which is the localizing closure of `Dctf(X, Λ)`
   (sk-def-localizing-closure), makes it an isomorphism, also for the empty family.
-/
theorem sk_prop_sf_existence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : Finite k ∨ IsAlgClosed k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ∀ c : Compactification.BoundaryCompactification f,
      ∃ (h : ∀ K, localizingClosureProEtale Λ X K →
          localizingClosureProEtale Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)),
        ∃ (hX : (localizingClosureProEtale Λ X).IsTriangulated)
          (hY : (localizingClosureProEtale Λ Y).IsTriangulated),
          let _ := hX
          let _ := hY
          (localizingLowerShriek Λ c.obj.obj h).IsTriangulated ∧
          (∀ I : Type (u + 1),
            PreservesColimitsOfShape (Discrete I)
              (localizingLowerShriek Λ c.obj.obj h)) ∧
          ∃ G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
              (localizingClosureProEtale Λ X).FullSubcategory,
            ∃ s : G.CommShift ℤ,
              let _ := s
              G.IsTriangulated ∧
              (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G) ∧
              ∃ adj : localizingLowerShriek Λ c.obj.obj h ⊣ G,
                ∀ (J : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
                    (localizingClosureProEtale Λ X).FullSubcategory)
                  (adjJ : localizingLowerShriek Λ c.obj.obj h ⊣ J),
                  ∃! e : G ≅ J, ∀ N,
                    (localizingLowerShriek Λ c.obj.obj h).map
                        (e.hom.app N) ≫ adjJ.counit.app N = adj.counit.app N := by
  classical
  intro c
  let hBX := brownHypotheses_finite_or_algebraicallyClosed ℓ (ringChar k)
    (Fact.out : (ringChar k).Prime).pos (Ne.symm (Fact.out : ringChar k ≠ ℓ)) hk
    (X ↘ Spec (.of k)) Λ hΛ
  let hBY := brownHypotheses_finite_or_algebraicallyClosed ℓ (ringChar k)
    (Fact.out : (ringChar k).Prime).pos (Ne.symm (Fact.out : ringChar k ≠ ℓ)) hk
    (Y ↘ Spec (.of k)) Λ hΛ
  obtain ⟨hsmallX, hX, hrepX, hSX, hisoSX, _, hessX, _, hsumX, hgenX⟩ := hBX
  obtain ⟨hsmallY, hY, hrepY, _, _, _, hessY, _, hsumY, hgenY⟩ := hBY
  let := hX
  let := hY
  let := hsmallX
  let := hsmallY
  let := hrepX
  let := hrepY
  let := hsumX
  let := hsumY
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  obtain ⟨h, _hexact, hsums, hctf⟩ :=
    (localizingCompactificationCoherence Λ ℓ k f hΛ).1 c
  refine ⟨h, hX, hY, ?_⟩
  let F := localizingLowerShriek Λ c.obj.obj h
  have hFtri : F.IsTriangulated := by
    dsimp [F, localizingLowerShriek]
    infer_instance
  let := hFtri
  let SX := constantModelBoundedConstructible Λ X ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  obtain ⟨hambientX, _, _, hlocalX, _, _, _, _⟩ := localizingClosure_exists Λ X SX
  let := hambientX
  have hclosedBig (I : Type (u + 2)) :
      (localizingClosureProEtale Λ X).IsClosedUnderColimitsOfShape (Discrete I) := by
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨K, hK⟩
    exact hlocalX.2.2 K inferInstance (fun i ↦ hK (Discrete.mk i))
  have hFsums : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F := by
    intro I
    let eI := Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I)
    let := hclosedBig (ULift.{u + 2} I)
    let : (localizingClosureProEtale Λ X).IsClosedUnderColimitsOfShape (Discrete I) :=
      ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence eI
    have hcomp : PreservesColimitsOfShape (Discrete I)
        ((localizingClosureProEtale Λ X).ι ⋙
          rightDerivedLowerShriekOfCompactification Λ c.obj.obj) := by
      constructor
      intro K
      have hpres : PreservesColimit (K ⋙ (localizingClosureProEtale Λ X).ι)
          (rightDerivedLowerShriekOfCompactification Λ c.obj.obj) := by
        let H := K ⋙ (localizingClosureProEtale Λ X).ι
        let := hsums (ULift.{u + 2} I) (eI.functor ⋙ H)
          (fun i ↦ (K.obj (eI.functor.obj (Discrete.mk i))).property)
        exact Functor.Final.preservesColimit_of_comp eI.functor
      let := hpres
      infer_instance
    have : PreservesColimitsOfShape (Discrete I)
        (F ⋙ (localizingClosureProEtale Λ Y).ι) := by
      let := hcomp
      exact preservesColimitsOfShape_of_natIso
        ((localizingClosureProEtale Λ Y).liftCompιIso _ _).symm
    exact preservesColimitsOfShape_of_reflects_of_preserves F
      (localizingClosureProEtale Λ Y).ι
  let : ObjectProperty.EssentiallySmall.{u + 1} SX := hessX
  have hSXL : SX ≤ localizingClosureProEtale Λ X := by
    intro K hK P hP hSP
    exact hSP K hK
  let : LocallySmall.{u + 1} SX.FullSubcategory :=
    locallySmall_of_faithful (ObjectProperty.ιOfLE hSXL)
  obtain ⟨QX, hQX, hQSX, hSXQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le SX
  let := hQX
  let : LocallySmall.{u + 1} QX.FullSubcategory :=
    locallySmall_of_faithful (ObjectProperty.ιOfLE hQSX)
  let : (ObjectProperty.ιOfLE hQSX).IsEquivalence :=
    (ObjectProperty.isEquivalence_ιOfLE_iff hQSX).mpr hSXQ
  let : EssentiallySmall.{u + 1} SX.FullSubcategory :=
    (essentiallySmall_congr (ObjectProperty.ιOfLE hQSX).asEquivalence).mp
      (essentiallySmall_of_small_of_locallySmall _)
  let IX := SmallModel.{u + 1} SX.FullSubcategory
  let e := (equivSmallModel.{u + 1} SX.FullSubcategory).symm
  have hLX : ∀ i : IX, localizingClosureProEtale Λ X (e.functor.obj i).obj := by
    intro i P hP hSP
    exact hSP _ (e.functor.obj i).property
  obtain ⟨hcompactX, hgenerateX⟩ := hgenX IX e hLX
  have hC : IsCompactlyGeneratedTriangulated.{u + 1}
      (localizingClosureProEtale Λ X).FullSubcategory :=
    ⟨IX, _, hcompactX, hgenerateX⟩
  have hleft : F.IsLeftAdjoint := by
    apply Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
    funext N
    apply propext
    exact ⟨fun _ ↦ trivial, fun _ ↦
      brownHomRepresentabilityLocallySmall F hC hFsums N⟩
  let := hleft
  let G := F.rightAdjoint
  let adj : F ⊣ G := Adjunction.ofIsLeftAdjoint F
  let s : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let := s
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have hGtri : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  have hcompactAllX (K : (localizingClosureProEtale Λ X).FullSubcategory)
      (hK : SX K.obj) : IsCompactObject K := by
    let i := e.inverse.obj ⟨K.obj, hK⟩
    let ei := e.counitIso.app ⟨K.obj, hK⟩
    let q : K ≅ (⟨(e.functor.obj i).obj, hLX i⟩ :
        (localizingClosureProEtale Λ X).FullSubcategory) :=
      (localizingClosureProEtale Λ X).fullyFaithfulι.preimageIso
        (SX.ι.mapIso ei).symm
    exact compact_of_iso q (hcompactX i)
  let SY := constantModelBoundedConstructible Λ Y ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  let : ObjectProperty.EssentiallySmall.{u + 1} SY := hessY
  have hSYL : SY ≤ localizingClosureProEtale Λ Y := by
    intro K hK P hP hSP
    exact hSP K hK
  let : LocallySmall.{u + 1} SY.FullSubcategory :=
    locallySmall_of_faithful (ObjectProperty.ιOfLE hSYL)
  obtain ⟨QY, hQY, hQSY, hSYQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le SY
  let := hQY
  let : LocallySmall.{u + 1} QY.FullSubcategory :=
    locallySmall_of_faithful (ObjectProperty.ιOfLE hQSY)
  let : (ObjectProperty.ιOfLE hQSY).IsEquivalence :=
    (ObjectProperty.isEquivalence_ιOfLE_iff hQSY).mpr hSYQ
  let : EssentiallySmall.{u + 1} SY.FullSubcategory :=
    (essentiallySmall_congr (ObjectProperty.ιOfLE hQSY).asEquivalence).mp
      (essentiallySmall_of_small_of_locallySmall _)
  let IY := SmallModel.{u + 1} SY.FullSubcategory
  let eY := (equivSmallModel.{u + 1} SY.FullSubcategory).symm
  have hLY : ∀ i : IY, localizingClosureProEtale Λ Y (eY.functor.obj i).obj :=
    fun i ↦ hSYL _ (eY.functor.obj i).property
  obtain ⟨hcompactY, _⟩ := hgenY IY eY hLY
  have hcompactAllY (K : (localizingClosureProEtale Λ Y).FullSubcategory)
      (hK : SY K.obj) : IsCompactObject K := by
    let i := eY.inverse.obj ⟨K.obj, hK⟩
    let ei := eY.counitIso.app ⟨K.obj, hK⟩
    let q : K ≅ (⟨(eY.functor.obj i).obj, hLY i⟩ :
        (localizingClosureProEtale Λ Y).FullSubcategory) :=
      (localizingClosureProEtale Λ Y).fullyFaithfulι.preimageIso
        (SY.ι.mapIso ei).symm
    exact compact_of_iso q (hcompactY i)
  let E : IX → (localizingClosureProEtale Λ X).FullSubcategory :=
    fun i ↦ ⟨(e.functor.obj i).obj, hLX i⟩
  let tests : IX × ULift.{u + 1} ℤ → (localizingClosureProEtale Λ X).FullSubcategory :=
    fun i ↦ (E i.1) ⟦i.2.down⟧
  have htestctf (i : IX × ULift.{u + 1} ℤ) : SX (tests i).obj := by
    let : SX.IsTriangulated := hSX
    let : SX.IsClosedUnderIsomorphisms := hisoSX
    exact SX.prop_of_iso
      (((localizingClosureProEtale Λ X).ι.commShiftIso i.2.down).app (E i.1)).symm
      (ObjectProperty.le_shift SX i.2.down _ (e.functor.obj i.1).property)
  have htests : ∀ i, IsCompactObject (tests i) ∧ IsCompactObject (F.obj (tests i)) := by
    intro i
    exact ⟨hcompactAllX _ (htestctf i), hcompactAllY _ (hctf _ (htestctf i))⟩
  have hdetect : ∀ (A B : (localizingClosureProEtale Λ X).FullSubcategory) (g : A ⟶ B),
      (∀ i, Function.Bijective (fun a : tests i ⟶ A ↦ a ≫ g)) → IsIso g := by
    intro A B g hg
    exact generators_detect_iso E hgenerateX g (fun i n ↦ hg (i, ⟨n⟩))
  have hGsums : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G :=
    compactTests_rightAdjoint_preservesCoproducts F G adj _ tests htests hdetect
  refine ⟨hFtri, hFsums, G, s, hGtri, hGsums, adj, ?_⟩
  intro J adjJ
  refine ⟨adj.rightAdjointUniq adjJ, ?_, ?_⟩
  · intro N
    exact adj.rightAdjointUniq_hom_app_counit adjJ N
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply (adjJ.homEquiv _ _).symm.injective
    exact (he N).trans (adj.rightAdjointUniq_hom_app_counit adjJ N).symm

end AlgebraicGeometry.ProEtale.CondensedRing
