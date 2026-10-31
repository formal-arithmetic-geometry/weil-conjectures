/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.AlgebraicGeometry.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import WeilConjectures.AlgebraicGeometry.LocalizingExceptionalAdjoint
import all WeilConjectures.AlgebraicGeometry.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctorsBasics.BrownHypotheses
import WeilConjectures.AlgebraicGeometry.LocalizingCompactificationCoherence

/-!
# Compact generation, `Rf_!` and the Brown adjoint on `Loc(Dctf)`

Source: blueprint latest, `sec-six-functors-basics/sk-thm-existence/det-existence-localizing.md`
and `det-existence-localizing.proof.md` (blueprint: det-existence-localizing).

The ambient categories are the localizing closures `localizingClosureProEtale` of the bounded
constructible finite-Tor objects in the unbounded module-object derived categories. For a
compactification `c` of `f`, the compactly supported direct image is the existing restriction
`localizingLowerShriek` of the actual composite `Rp_{c*} ∘ D(j_!)` to these closures, with the
shift structure induced from the ambient derived functor.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Compactness transports by precomposition with an isomorphism. -/
private theorem compact_of_iso
    {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{u} C]
    {K L : C} (e : K ≅ L) (hL : IsCompactObject L) : IsCompactObject K := by
  classical
  intro I A
  let d := DirectSum.map (fun i ↦ Preadditive.leftComp (A i) e.hom)
  have hd : Function.Bijective d :=
    ⟨(DirectSum.map_injective _).2 (fun i ↦ e.symm.homFromEquiv.injective),
      (DirectSum.map_surjective _).2 (fun i ↦ e.symm.homFromEquiv.surjective)⟩
  let post := Preadditive.leftComp (∐ A) e.hom
  have hp : Function.Bijective post := e.symm.homFromEquiv.bijective
  let a := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K (Sigma.ι A i))
  let b := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp L (Sigma.ι A i))
  have square : a.comp d = post.comp b := by
    apply DirectSum.addHom_ext
    intro i f
    simp only [AddMonoidHom.comp_apply]
    dsimp [a, b, d]
    rw [DirectSum.map_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    exact Category.assoc _ _ _
  have hb : Function.Bijective b := hL I A
  have hcomp : Function.Bijective (a ∘ d) := by
    change Function.Bijective (a.comp d)
    rw [square]
    exact hp.comp hb
  exact (Function.Bijective.of_comp_iff a hd).mp hcomp

/-- Extract a small family meeting every Dctf isomorphism class from the Brown bundle,
and transport its compactness to every Dctf object. -/
private theorem compact_generators_of_brown
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Z : Scheme.{u}) (hB : BrownHypothesesFor Λ Z) :
    ∃ (hTri : (localizingClosureProEtale Λ Z).IsTriangulated)
      (hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ Z).FullSubcategory),
      (fun [_tri : (localizingClosureProEtale Λ Z).IsTriangulated]
          [_sums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ Z).FullSubcategory] ↦
        (∀ K : (localizingClosureProEtale Λ Z).FullSubcategory,
          constantModelBoundedConstructible Λ Z K.obj ∧
            DerivedCategory.finiteTorAmplitude _ K.obj → IsCompactObject K) ∧
        ∃ (I : Type (u + 1))
          (E : I → (localizingClosureProEtale Λ Z).FullSubcategory),
          (∀ i, constantModelBoundedConstructible Λ Z (E i).obj ∧
            DerivedCategory.finiteTorAmplitude _ (E i).obj) ∧
          (∀ K, constantModelBoundedConstructible Λ Z K.obj ∧
            DerivedCategory.finiteTorAmplitude _ K.obj → ∃ i, Nonempty (E i ≅ K)) ∧
          (∀ i, IsCompactObject (E i)) ∧ IsTriangulatedGeneratingFamily E)
        (_tri := hTri) (_sums := hSums) := by
  classical
  obtain ⟨hsmall, hTri, _, _, _, _, hess, _, hSums, hgen⟩ := hB
  let := hTri
  let := hsmall
  let := hSums
  let S := constantModelBoundedConstructible Λ Z ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  have hSL : S ≤ localizingClosureProEtale Λ Z := by
    intro K hK P hP hSP
    exact hSP K hK
  let : ObjectProperty.EssentiallySmall.{u + 1} S := hess
  let : LocallySmall.{u + 1} S.FullSubcategory :=
    locallySmall_of_faithful (ObjectProperty.ιOfLE hSL)
  obtain ⟨Q, hQ, hQS, hSQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le S
  let := hQ
  let : LocallySmall.{u + 1} Q.FullSubcategory :=
    locallySmall_of_faithful (ObjectProperty.ιOfLE hQS)
  let : (ObjectProperty.ιOfLE hQS).IsEquivalence :=
    (ObjectProperty.isEquivalence_ιOfLE_iff hQS).mpr hSQ
  let : EssentiallySmall.{u + 1} S.FullSubcategory :=
    (essentiallySmall_congr (ObjectProperty.ιOfLE hQS).asEquivalence).mp
      (essentiallySmall_of_small_of_locallySmall _)
  let I := SmallModel.{u + 1} S.FullSubcategory
  let e := (equivSmallModel.{u + 1} S.FullSubcategory).symm
  have hL (i : I) : localizingClosureProEtale Λ Z (e.functor.obj i).obj :=
    hSL _ (e.functor.obj i).property
  let E : I → (localizingClosureProEtale Λ Z).FullSubcategory :=
    fun i ↦ ⟨(e.functor.obj i).obj, hL i⟩
  obtain ⟨hcompact, hgenerate⟩ := hgen I e hL
  have hcover (K : (localizingClosureProEtale Λ Z).FullSubcategory)
      (hK : S K.obj) : ∃ i, Nonempty (E i ≅ K) := by
    let i := e.inverse.obj ⟨K.obj, hK⟩
    refine ⟨i, ⟨?_⟩⟩
    exact (localizingClosureProEtale Λ Z).fullyFaithfulι.preimageIso
      (S.ι.mapIso (e.counitIso.app ⟨K.obj, hK⟩))
  refine ⟨hTri, hSums, ?_, I, E, ?_, hcover, hcompact, hgenerate⟩
  · intro K hK
    obtain ⟨i, ⟨ei⟩⟩ := hcover K hK
    exact compact_of_iso ei.symm (hcompact i)
  · intro i
    exact (e.functor.obj i).property

set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
-- The proof assembles two small models and the restricted compactification functors.
/-- Compact generation of `Loc(Dctf)`, the compactly supported direct image `Rf_!^c` on the
localizing closures, and its exact Brown right adjoint `f^!`.
Source: blueprint latest, `sec-six-functors-basics/sk-thm-existence/det-existence-localizing.md`,
clauses (1)-(3) (blueprint: det-existence-localizing).

Clause (1) is rendered for `X` and for `Y`: every bounded constructible finite-Tor object is
compact in the closure, and a `u+1`-small family of such objects meeting every isomorphism class
(so every small skeleton) is a generating family of compact objects. Clause (2): for every
quasi-compact compactification `c` of `f`, `Rp_{c*} ∘ D(j_!)` maps the closure of `X` into that
of `Y` (`h c`), and its restriction `localizingLowerShriek`, with its induced shift structure, is
exact, preserves `u+1`-small coproducts, preserves `Dctf`, and is isomorphic to the restriction
for any other compactification. Clause (3): this restriction has an exact right adjoint.

Proof:
1. Put `T_Z = Loc(Dctf(Z, Λ))` for `Z = X, Y`. Apply sk-lem-brown-hypotheses
   (`brownHypotheses`) to each `Z`: `cd_ℓ(k) < ∞`, `Z` separated of finite type and `Λ`
   admissible. So `T_Z` is triangulated with the required coproducts and any small skeleton of
   `Dctf(Z, Λ)` consists of compact generators. Every object of `Dctf(Z, Λ)` is isomorphic to a
   skeleton representative, and compactness transports along that isomorphism
   (def-pc-compact-object). This proves (1).
2. Fix `c`. Apply sk-prop-sf-comp-coherence (`localizingCompactificationCoherence`): it gives
   preservation of the closures, exactness on distinguished triangles, preservation of all
   coproducts and of `Dctf` by `Rp_{c*} D(j_!)`, and the canonical comparisons between any two
   compactifications, with identity and cocycle clauses. This proves (2).
3. Apply sk-prop-sf-existence (`exists_localizingExceptionalAdjoint`) to `f` and `c`, under the
   same hypotheses; its functor is the same `localizingLowerShriek Λ c (h c)`. It gives an exact
   right adjoint `f^! : T_Y ⥤ T_X`. This proves (3). -/
theorem det_existence_localizing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (_hΛ : IsLocalizingAdmissibleCoefficient ell Λ) :
    ∃ (hX : (localizingClosureProEtale Λ X.left).IsTriangulated)
      (hY : (localizingClosureProEtale Λ Y.left).IsTriangulated)
      (sX : HasCoproducts.{u + 1}
        (localizingClosureProEtale Λ X.left).FullSubcategory)
      (sY : HasCoproducts.{u + 1}
        (localizingClosureProEtale Λ Y.left).FullSubcategory)
      (h : ∀ c : Compactification.BoundaryCompactification f.left, ∀ K,
        localizingClosureProEtale Λ X.left K → localizingClosureProEtale Λ Y.left
          ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)),
      (fun [triX : (localizingClosureProEtale Λ X.left).IsTriangulated]
          [triY : (localizingClosureProEtale Λ Y.left).IsTriangulated]
          [sumsX : HasCoproducts.{u + 1}
            (localizingClosureProEtale Λ X.left).FullSubcategory]
          [sumsY : HasCoproducts.{u + 1}
            (localizingClosureProEtale Λ Y.left).FullSubcategory] ↦
        (∀ K : (localizingClosureProEtale Λ X.left).FullSubcategory,
          constantModelBoundedConstructible Λ X.left K.obj ∧
            DerivedCategory.finiteTorAmplitude _ K.obj → IsCompactObject K) ∧
        (∀ K : (localizingClosureProEtale Λ Y.left).FullSubcategory,
          constantModelBoundedConstructible Λ Y.left K.obj ∧
            DerivedCategory.finiteTorAmplitude _ K.obj → IsCompactObject K) ∧
        (∃ (I : Type (u + 1))
          (E : I → (localizingClosureProEtale Λ X.left).FullSubcategory),
          (∀ i, constantModelBoundedConstructible Λ X.left (E i).obj ∧
            DerivedCategory.finiteTorAmplitude _ (E i).obj) ∧
          (∀ K, constantModelBoundedConstructible Λ X.left K.obj ∧
            DerivedCategory.finiteTorAmplitude _ K.obj →
            ∃ i, Nonempty (E i ≅ K)) ∧
          (∀ i, IsCompactObject (E i)) ∧ IsTriangulatedGeneratingFamily E) ∧
        (∃ (I : Type (u + 1))
          (E : I → (localizingClosureProEtale Λ Y.left).FullSubcategory),
          (∀ i, constantModelBoundedConstructible Λ Y.left (E i).obj ∧
            DerivedCategory.finiteTorAmplitude _ (E i).obj) ∧
          (∀ K, constantModelBoundedConstructible Λ Y.left K.obj ∧
            DerivedCategory.finiteTorAmplitude _ K.obj →
            ∃ i, Nonempty (E i ≅ K)) ∧
          (∀ i, IsCompactObject (E i)) ∧ IsTriangulatedGeneratingFamily E) ∧
        ∀ c : Compactification.BoundaryCompactification f.left,
          (localizingLowerShriek Λ c.obj.obj (h c)).IsTriangulated ∧
          (∀ I : Type (u + 1),
            PreservesColimitsOfShape (Discrete I) (localizingLowerShriek Λ c.obj.obj (h c))) ∧
          (∀ K : (localizingClosureProEtale Λ X.left).FullSubcategory,
            (constantModelBoundedConstructible Λ X.left K.obj ∧
              DerivedCategory.finiteTorAmplitude _ K.obj) →
            constantModelBoundedConstructible Λ Y.left
                ((localizingLowerShriek Λ c.obj.obj (h c)).obj K).obj ∧
              DerivedCategory.finiteTorAmplitude _
                ((localizingLowerShriek Λ c.obj.obj (h c)).obj K).obj) ∧
          (∀ d : Compactification.BoundaryCompactification f.left,
            Nonempty (localizingLowerShriek Λ c.obj.obj (h c) ≅
              localizingLowerShriek Λ d.obj.obj (h d))) ∧
          ∃ G : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
              (localizingClosureProEtale Λ X.left).FullSubcategory,
            ∃ shiftG : G.CommShift ℤ,
              (fun [commG : G.CommShift ℤ] ↦
                Nonempty (localizingLowerShriek Λ c.obj.obj (h c) ⊣ G) ∧ G.IsTriangulated)
                (commG := shiftG))
        (triX := hX) (triY := hY) (sumsX := sX) (sumsY := sY) := by
  classical
  obtain ⟨hX, sX, hcompactX, hgenX⟩ := compact_generators_of_brown Λ X.left
    (brownHypotheses ell (ringChar k) (Fact.out : (ringChar k).Prime).pos
      (Fact.out : ringChar k ≠ ell) hcd X.hom Λ _hΛ)
  obtain ⟨hY, sY, hcompactY, hgenY⟩ := compact_generators_of_brown Λ Y.left
    (brownHypotheses ell (ringChar k) (Fact.out : (ringChar k).Prime).pos
      (Fact.out : ringChar k ≠ ell) hcd Y.hom Λ _hΛ)
  let := hX
  let := hY
  let := sX
  let := sY
  have : IsSeparated (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : QuasiCompact (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  let : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  let : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  let : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : f.left.IsOver (Spec (.of k)) := ⟨f.w⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
  let : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  let : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  let : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  have hcoh := localizingCompactificationCoherence Λ ell k f.left _hΛ
  obtain ⟨φ, _⟩ := hcoh.2.2.2.2.2.2
  choose h hTX hTY hdata using
    (fun c : Compactification.BoundaryCompactification f.left ↦
      exists_localizingExceptionalAdjoint Λ ell k hcd f.left c _hΛ)
  refine ⟨hX, hY, sX, sY, h, hcompactX, hcompactY, hgenX, hgenY, ?_⟩
  intro c
  obtain ⟨hF, _, _, hsum, G, sG, hG, _, adj, _⟩ := hdata c
  refine ⟨hF, hsum, ?_, ?_, G, sG, ⟨adj⟩, hG⟩
  · intro K hK
    exact (hcoh.1 c).2.2.2 K.obj hK
  · intro d
    refine ⟨((localizingClosureProEtale Λ Y.left).fullyFaithfulι.whiskeringRight _).preimageIso ?_⟩
    exact (localizingClosureProEtale Λ Y.left).liftCompιIso _ _ ≪≫
      φ c d ≪≫ ((localizingClosureProEtale Λ Y.left).liftCompιIso _ _).symm

end AlgebraicGeometry.ProEtale.CondensedRing
