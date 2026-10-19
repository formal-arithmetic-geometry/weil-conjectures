/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.CompactificationRefinementLocalizing
public import Sheaf.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Adjunction
import Sheaf.CategoryTheory.BrownRepresentabilityHomLocallySmall
import Sheaf.Paper.LocalizingClosureExistence
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Final
import Sheaf.SixFunctorsBasics.BrownHypotheses
import Sheaf.Paper.CompactificationLocalizing
import Sheaf.CategoryTheory.BrownRepresentabilityRightAdjoint
import Mathlib.CategoryTheory.Yoneda
import Sheaf.Compactification.BoundaryRefinement
public import Sheaf.Paper.CompactificationCoherenceCocycle
import Sheaf.Paper.CompactificationRefinementIdentity
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# Brown exceptional adjoints and compactification independence

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-existence,
det-sf-existence-brown.proof.md, parts (1)--(3); Stacks Tags 0A8F, 0A8G, 0A8D
(blueprint: det-sf-existence-brown).

All functors act on the recorded localizing closures in the ordinary derived categories
of internal modules. Comparisons are normalized by the existing open-adjunction refinement
map and the K-injective-normalized direct-image compositor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

private theorem coherentRightAdjoints
    {C D : Type*} [Category C] [Category D] {I : Type*}
    (F : I → C ⥤ D) (G : I → D ⥤ C) (adj : ∀ i, F i ⊣ G i)
    (phi : ∀ i j, F i ≅ F j)
    (hphiId : ∀ i, phi i i = Iso.refl _)
    (hphiComp : ∀ i j k, phi i j ≪≫ phi j k = phi i k) :
    ∃ gamma : ∀ i j, G i ≅ G j,
      (∀ i j N, (F j).map ((gamma i j).hom.app N) ≫ (adj j).counit.app N =
        (phi i j).inv.app ((G i).obj N) ≫ (adj i).counit.app N) ∧
      (∀ i j (e : G i ≅ G j),
        (∀ N, (F j).map (e.hom.app N) ≫ (adj j).counit.app N =
          (phi i j).inv.app ((G i).obj N) ≫ (adj i).counit.app N) → e = gamma i j) ∧
      (∀ i, gamma i i = Iso.refl _) ∧
      (∀ i j k, gamma i j ≪≫ gamma j k = gamma i k) := by
  let gamma := fun c d ↦ ((adj c).ofNatIsoLeft (phi c d)).rightAdjointUniq (adj d)
  have hgamma (c d) (N) :
      (F d).map ((gamma c d).hom.app N) ≫ (adj d).counit.app N =
        (phi c d).inv.app ((G c).obj N) ≫ (adj c).counit.app N := by
    exact ((adj c).ofNatIsoLeft (phi c d)).rightAdjointUniq_hom_app_counit (adj d) N
  have huniq (c d) (e : G c ≅ G d)
      (he : ∀ N, (F d).map (e.hom.app N) ≫ (adj d).counit.app N =
        (phi c d).inv.app ((G c).obj N) ≫ (adj c).counit.app N) :
      e = gamma c d := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply ((adj d).homEquiv _ _).symm.injective
    exact (he N).trans (hgamma c d N).symm
  refine ⟨gamma, hgamma, huniq, ?_, ?_⟩
  · intro c
    symm
    apply huniq
    intro N
    change (F c).map (𝟙 _) ≫ (adj c).counit.app N = _
    rw [hphiId]
    dsimp only [Iso.refl_inv, NatTrans.id_app]
    simp
  · intro c d e
    apply huniq
    intro N
    change (F e).map ((gamma c d).hom.app N ≫ (gamma d e).hom.app N) ≫
      (adj e).counit.app N = _
    rw [Functor.map_comp, Category.assoc, hgamma]
    rw [← Category.assoc, (phi d e).inv.naturality, Category.assoc, hgamma]
    rw [← Category.assoc]
    have hi := congrArg (fun a ↦ a.inv.app ((G c).obj N)) (hphiComp c d e)
    rw [← hi]
    rfl

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Push the canonical open refinement map along the coarse proper map, then undo the
canonical derived direct-image compositor. This is the specified map from the coarse
compact-support composite to the fine one, before any invertibility assertion.
Source: blueprint det-sf-existence-brown.proof.md (3), using the refinement construction
in det-sf-comp-coherence-cocycle, proof step 4
(blueprint: det-sf-existence-brown). -/
def brownCompactificationRefinementMap
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K ⟶
      (rightDerivedLowerShriekOfCompactification Λ d.obj.obj).obj K :=
  compactificationRefinementComponent Λ r K


set_option linter.unusedVariables false
/-- Brown representability on the localizing constructible closure gives exact exceptional
adjoints, with their adjunction-induced coherent shifts. The adjoints are unique among
counit-compatible natural isomorphisms. Their comparisons for different compactifications
are normalized by the canonical compact-support comparisons and satisfy identity and
cocycle laws. The source triangulation and sums are the standing Brown hypotheses; the
set of compact generators is explicitly required to lie in Dctf. The target triangulation
and the restriction-membership witnesses are conclusions, not extra assumptions.

Source: blueprint main-20261015, det-sf-existence-brown, statement and proof parts (1)--(3);
Stacks Tags 0A8F, 0A8G and 0A8D (blueprint: det-sf-existence-brown).

Proof:
1. The geometric setting makes Y qcqs (lem-weil-pbc-qcqs-over-affine). For every
compactification, det-sf-comp-coherence-single gives preservation of the localizing
closures, exactness and preservation of small sums. sk-lem-brown-hypotheses supplies
the target Brown structures. The assumed compact generators supply the source condition.
2. Apply lem-pc-brown-representability-right-adjoint to each restricted functor. For each N,
Hom(F(-),N) is cohomological and carries sums to products, hence is representable by Brown.
Yoneda assembles these representing objects into G, with natural Hom bijections F ⊣ G.
3. Transpose the shifted counit, obtaining G(N)[n] ≅ G(N[n]). Full faithfulness of Yoneda
(lem-galois-yoneda-fully-faithful) gives naturality. The transpose of the identity shift
is the counit; transposing successive shifts gives the sum shift by coherence for F.
The triangle identities give compatibility of both unit and counit with these shifts.
This is exactly Adjunction.rightAdjointCommShift, including zero and addition coherence.
4. Apply lem-sf-triangulated-right-adjoint with these compatible shifts: G is exact.
5. det-sp-unique-right-adjoint transposes the counits of two adjunctions to inverse natural
transformations. The adjunction bijection is injective, so the counit equation uniquely
determines the isomorphism, and also implies compatibility with every Hom bijection.
6. det-sf-comp-coherence-cocycle constructs the canonical F comparisons through any common
dense refinement, normalized by brownCompactificationRefinementMap. Restricting the ambient
comparisons along the fully faithful inclusions gives phi. Transfer one adjunction along
phi and apply step 5 to obtain gamma. Transposing its counit equation gives uniqueness.
For three compactifications, substitute the two counit equations and use naturality of
phi and its cocycle. The result is the counit equation for the third comparison; uniqueness
gives the gamma cocycle. The same calculation for identity phi gives identity gamma.
-/
theorem exists_brownExceptionalAdjoints
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    [(localizingClosureProEtale Λ X).IsTriangulated]
    [LocallySmall.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory]
    [HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory]
    (_hgen : ∃ (I : Type (u + 1))
      (E : I → (localizingClosureProEtale Λ X).FullSubcategory),
      (∀ i, constantModelBoundedConstructible Λ X (E i).obj ∧
        DerivedCategory.finiteTorAmplitude _ (E i).obj) ∧
      (∀ i, IsCompactObject (E i)) ∧ IsTriangulatedGeneratingFamily E) :
    ∃ (h : ∀ (c : Compactification.BoundaryCompactification f) K,
        localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
          ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hY : (localizingClosureProEtale Λ Y).IsTriangulated),
      (fun [triY : (localizingClosureProEtale Λ Y).IsTriangulated] ↦
        ∃ (G : Compactification.BoundaryCompactification f →
            ((localizingClosureProEtale Λ Y).FullSubcategory ⥤
              (localizingClosureProEtale Λ X).FullSubcategory))
          (adj : ∀ c : Compactification.BoundaryCompactification f,
            localizingLowerShriek Λ c.obj.obj (h c) ⊣ G c),
          (∀ c, (fun [comm : (G c).CommShift ℤ] ↦
            (G c).IsTriangulated ∧ (adj c).CommShift ℤ)
              (comm := (adj c).rightAdjointCommShift ℤ)) ∧
          (∀ (c : Compactification.BoundaryCompactification f)
            (J : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
              (localizingClosureProEtale Λ X).FullSubcategory)
              (adjJ : localizingLowerShriek Λ c.obj.obj (h c) ⊣ J),
            ∃! e : G c ≅ J, ∀ N,
              (localizingLowerShriek Λ c.obj.obj (h c)).map (e.hom.app N) ≫
                adjJ.counit.app N = (adj c).counit.app N) ∧
          ∃ phi : ∀ c d : Compactification.BoundaryCompactification f,
              localizingLowerShriek Λ c.obj.obj (h c) ≅
                localizingLowerShriek Λ d.obj.obj (h d),
            (∀ (c : Compactification.BoundaryCompactification f)
              (d : Compactification.DenseBoundaryCompactification f)
              (r : d.obj ⟶ c) (K : (localizingClosureProEtale Λ X).FullSubcategory),
              ((phi c d.obj).hom.app K).hom = brownCompactificationRefinementMap Λ r K.obj) ∧
            (∀ c, phi c c = Iso.refl _) ∧
            (∀ c d e, phi c d ≪≫ phi d e = phi c e) ∧
            ∃ gamma : ∀ c d : Compactification.BoundaryCompactification f, G c ≅ G d,
              (∀ (c d : Compactification.BoundaryCompactification f)
                (N : (localizingClosureProEtale Λ Y).FullSubcategory),
                (localizingLowerShriek Λ d.obj.obj (h d)).map ((gamma c d).hom.app N) ≫
                  (adj d).counit.app N =
                    (phi c d).inv.app ((G c).obj N) ≫ (adj c).counit.app N) ∧
              (∀ (c d : Compactification.BoundaryCompactification f) (e : G c ≅ G d),
                (∀ N : (localizingClosureProEtale Λ Y).FullSubcategory,
                  (localizingLowerShriek Λ d.obj.obj (h d)).map (e.hom.app N) ≫
                  (adj d).counit.app N =
                    (phi c d).inv.app ((G c).obj N) ≫ (adj c).counit.app N) →
                e = gamma c d) ∧
              (∀ c, gamma c c = Iso.refl _) ∧
              (∀ c d e, gamma c d ≪≫ gamma d e = gamma c e))
        (triY := hY) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      classical
      let : Fact (ringChar k).Prime := ⟨by
        rw [ringChar.eq k p]
        exact (CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt _hp)⟩
      let : Fact (ringChar k ≠ ℓ) := ⟨by simpa only [ringChar.eq k p] using _hpℓ⟩
      let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
      let : QuasiSeparatedSpace Y :=
        quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
      obtain ⟨hsmallY, hY, hrepY, hSY, hisoSY, hretY, hessY, hidY, hsumY, hgenY⟩ :=
        brownHypotheses ℓ p _hp _hpℓ (Y ↘ Spec (.of k)) Λ _hΛ
      let := hY
      let := hsmallY
      let := hsumY
      let h := fun c ↦ (compactification_localizing Λ ℓ k f c _hΛ).1
      refine ⟨h, hY, ?_⟩
      let F := fun c : Compactification.BoundaryCompactification f ↦
        localizingLowerShriek Λ c.obj.obj (h c)
      have hFtri (c) : (F c).IsTriangulated := by
        dsimp [F, localizingLowerShriek]
        infer_instance
      let S := constantModelBoundedConstructible Λ X ⊓ fun K ↦
        DerivedCategory.finiteTorAmplitude _ K
      obtain ⟨hambientX, _, _, hlocalX, _, _, _, _⟩ := localizingClosure_exists Λ X S
      let := hambientX
      let : (localizingClosureProEtale Λ X).IsClosedUnderIsomorphisms := hlocalX.2.1
      have hclosedBig (I : Type (u + 2)) :
          (localizingClosureProEtale Λ X).IsClosedUnderColimitsOfShape (Discrete I) := by
        apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
        rintro _ ⟨K, hK⟩
        exact hlocalX.2.2 K inferInstance (fun i ↦ hK (Discrete.mk i))
      have hFsums (c) (I : Type (u + 1)) :
          PreservesColimitsOfShape (Discrete I) (F c) := by
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
            let := (compactification_localizing Λ ℓ k f c _hΛ).2.2.1
              (ULift.{u + 2} I) (eI.functor ⋙ H)
              (fun i ↦ (K.obj (eI.functor.obj (Discrete.mk i))).property)
            exact Functor.Final.preservesColimit_of_comp eI.functor
          let := hpres
          infer_instance
        have : PreservesColimitsOfShape (Discrete I)
            (F c ⋙ (localizingClosureProEtale Λ Y).ι) := by
          let := hcomp
          exact preservesColimitsOfShape_of_natIso
            ((localizingClosureProEtale Λ Y).liftCompιIso _ _).symm
        exact preservesColimitsOfShape_of_reflects_of_preserves (F c)
          (localizingClosureProEtale Λ Y).ι
      have hC : IsCompactlyGeneratedTriangulated.{u + 1}
          (localizingClosureProEtale Λ X).FullSubcategory := by
        obtain ⟨I, E, _, hc, hg⟩ := _hgen
        exact ⟨I, E, hc, hg⟩
      have hleft (c) : (F c).IsLeftAdjoint := by
        let := hFtri c
        apply Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
        funext N
        apply propext
        exact ⟨fun _ ↦ trivial, fun _ ↦
          brownHomRepresentabilityLocallySmall (F c) hC (hFsums c) N⟩
      let G := fun c ↦ (F c).rightAdjoint
      let adj := fun c ↦ Adjunction.ofIsLeftAdjoint (F c)
      refine ⟨G, adj, ?_, ?_, ?_⟩
      · intro c
        let := hFtri c
        let := (adj c).rightAdjointCommShift ℤ
        let := (adj c).commShift_of_leftAdjoint ℤ
        exact ⟨(adj c).isTriangulated_rightAdjoint, inferInstance⟩
      · intro c J adjJ
        refine ⟨(adj c).rightAdjointUniq adjJ, ?_, ?_⟩
        · exact fun N ↦ (adj c).rightAdjointUniq_hom_app_counit adjJ N
        · intro e he
          apply Iso.ext
          apply NatTrans.ext
          funext N
          apply (adjJ.homEquiv _ _).symm.injective
          exact (he N).trans ((adj c).rightAdjointUniq_hom_app_counit adjJ N).symm
      · obtain ⟨psi, hiso, hnorm, hid, hcomp⟩ :=
          compactification_coherence_cocycle Λ ℓ _hΛ f
        let liftIso : ∀ c : Compactification.BoundaryCompactification f,
            F c ⋙ (localizingClosureProEtale Λ Y).ι ≅
              compactificationLocalizingCandidate Λ c := fun c ↦
          (localizingClosureProEtale Λ Y).liftCompιIso
            ((localizingClosureProEtale Λ X).ι ⋙
              rightDerivedLowerShriekOfCompactification Λ c.obj.obj)
            (fun K ↦ h c K.obj K.property)
        let phi : ∀ c d : Compactification.BoundaryCompactification f, F c ≅ F d :=
          fun c d ↦ Functor.fullyFaithfulCancelRight
          (localizingClosureProEtale Λ Y).ι (liftIso c ≪≫ psi c d ≪≫ (liftIso d).symm)
        have hphi (c d) (K) : ((phi c d).hom.app K).hom = (psi c d).hom.app K := by
          change (localizingClosureProEtale Λ Y).ι.map ((phi c d).hom.app K) = _
          simp only [phi, Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
          simp only [liftIso, ObjectProperty.liftCompιIso, Iso.trans_hom,
            Iso.symm_hom, Iso.refl_hom, Iso.refl_inv, NatTrans.comp_app,
            NatTrans.id_app]
          erw [Category.comp_id, Category.id_comp]
        have hphiId (c) : phi c c = Iso.refl _ := by
          apply Iso.ext
          apply NatTrans.ext
          funext K
          apply (localizingClosureProEtale Λ Y).ι.map_injective
          change ((phi c c).hom.app K).hom = 𝟙 _
          rw [hphi, hid]
          rfl
        have hphiComp (c d e) : phi c d ≪≫ phi d e = phi c e := by
          apply Iso.ext
          apply NatTrans.ext
          funext K
          apply (localizingClosureProEtale Λ Y).ι.map_injective
          change ((phi c d).hom.app K).hom ≫ ((phi d e).hom.app K).hom =
            ((phi c e).hom.app K).hom
          simp only [hphi]
          exact congrArg (fun a ↦ a.hom.app K) (hcomp c d e)
        refine ⟨phi, ?_, hphiId, hphiComp, ?_⟩
        · intro c d r K
          rw [hphi]
          have hn := hnorm c d.obj d r (𝟙 d.obj) K
          rw [compactificationRefinementComponent_id Λ ℓ k _hΛ f d K.obj] at hn
          have hn' : (psi c d.obj).hom.app K =
              compactificationRefinementComponent Λ r K.obj := by
            erw [Category.comp_id] at hn
            exact hn
          exact hn'
        · exact coherentRightAdjoints F G adj phi hphiId hphiComp

end AlgebraicGeometry.ProEtale.CondensedRing
