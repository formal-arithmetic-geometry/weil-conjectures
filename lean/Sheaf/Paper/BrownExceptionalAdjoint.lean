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
public import Sheaf.Paper.CompactificationCoherenceCocycle
import Sheaf.Paper.CompactificationRefinementIdentity
import Sheaf.Compactification.BoundaryRefinement
import Sheaf.Paper.LocalizingClosureExistence
import Mathlib.CategoryTheory.Limits.FullSubcategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Sheaf.SixFunctorsBasics.BrownHypotheses
import Sheaf.Paper.CompactificationLocalizing
import Sheaf.CategoryTheory.BrownRepresentabilityRightAdjoint

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

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

private theorem closure_closedUnderIsomorphisms
    {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) : (localizingClosure S).IsClosedUnderIsomorphisms where
  of_iso e h := by
    intro P hP hS
    let := hP.2.1
    exact P.prop_of_iso e (h P hP hS)

private theorem closure_closedUnderSums
    {C : Type v} [Category* C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) (I : Type v) :
    (localizingClosure S).IsClosedUnderColimitsOfShape (Discrete I) := by
  let := closure_closedUnderIsomorphisms S
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  intro P hP hS
  exact hP.2.2 F inferInstance (fun i ↦ hF ⟨i⟩ P hP hS)

private theorem restricted_preservesColimits
    {C D J : Type*} [Category* C] [Category* D] [Category* J]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    [HasColimitsOfShape J C] [P.IsClosedUnderColimitsOfShape J]
    (F : C ⥤ D) (h : ∀ K, P K → Q (F.obj K))
    (hF : ∀ K : J ⥤ C, (∀ j, P (K.obj j)) → PreservesColimit K F) :
    PreservesColimitsOfShape J (Q.lift (P.ι ⋙ F) (fun K ↦ h K.obj K.property)) := by
  have : PreservesColimitsOfShape J (P.ι ⋙ F) := by
    constructor
    intro K
    let : PreservesColimit (K ⋙ P.ι) F :=
      hF (K ⋙ P.ι) (fun j ↦ (K.obj j).property)
    infer_instance
  let : PreservesColimitsOfShape J
      (Q.lift (P.ι ⋙ F) (fun K ↦ h K.obj K.property) ⋙ Q.ι) :=
    preservesColimitsOfShape_of_natIso (Q.liftCompιIso (P.ι ⋙ F) _).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _ Q.ι

private theorem counitCompatibleIsoUnique
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G J : D ⥤ C} (adj : F ⊣ G) (adjJ : F ⊣ J) :
    ∃! e : G ≅ J, ∀ N,
      F.map (e.hom.app N) ≫ adjJ.counit.app N = adj.counit.app N := by
  refine ⟨adj.rightAdjointUniq adjJ, fun N ↦
    adj.rightAdjointUniq_hom_app_counit adjJ N, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply (adjJ.homEquiv _ _).symm.injective
  simpa only [Adjunction.homEquiv_counit] using
    (he N).trans (adj.rightAdjointUniq_hom_app_counit adjJ N).symm

private theorem coherentRightAdjointComparisons
    {C D A : Type*} [Category* C] [Category* D]
    (F : A → C ⥤ D) (G : A → D ⥤ C) (adj : ∀ a, F a ⊣ G a)
    (phi : ∀ a b, F a ≅ F b)
    (hid : ∀ a, phi a a = Iso.refl _)
    (hcomp : ∀ a b c, phi a b ≪≫ phi b c = phi a c) :
    ∃ gamma : ∀ a b, G a ≅ G b,
      (∀ a b N, (F b).map ((gamma a b).hom.app N) ≫ (adj b).counit.app N =
        (phi a b).inv.app ((G a).obj N) ≫ (adj a).counit.app N) ∧
      (∀ a b (e : G a ≅ G b),
        (∀ N, (F b).map (e.hom.app N) ≫ (adj b).counit.app N =
          (phi a b).inv.app ((G a).obj N) ≫ (adj a).counit.app N) →
        e = gamma a b) ∧
      (∀ a, gamma a a = Iso.refl _) ∧
      (∀ a b c, gamma a b ≪≫ gamma b c = gamma a c) := by
  let gamma := fun a b ↦ conjugateIsoEquiv (adj a) (adj b) (phi a b).symm
  have hc : ∀ a b N,
      (F b).map ((gamma a b).hom.app N) ≫ (adj b).counit.app N =
        (phi a b).inv.app ((G a).obj N) ≫ (adj a).counit.app N := by
    intro a b N
    exact conjugateEquiv_counit (adj a) (adj b) (phi a b).inv N
  refine ⟨gamma, hc, ?_, ?_, ?_⟩
  · intro a b e he
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply ((adj b).homEquiv _ _).symm.injective
    simpa only [Adjunction.homEquiv_counit] using (he N).trans (hc a b N).symm
  · intro a
    apply Iso.ext
    dsimp [gamma]
    rw [hid]
    exact conjugateEquiv_id (adj a)
  · intro a b c
    apply Iso.ext
    change conjugateEquiv (adj a) (adj b) (phi a b).inv ≫
      conjugateEquiv (adj b) (adj c) (phi b c).inv =
        conjugateEquiv (adj a) (adj c) (phi a c).inv
    rw [conjugateEquiv_comp]
    exact congrArg (conjugateEquiv (adj a) (adj c))
      (congrArg Iso.inv (hcomp a b c))

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

set_option linter.unusedVariables false in
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
  classical
  have hpchar : ringChar k = p := ringChar.eq k p
  have : Fact (ringChar k).Prime := ⟨by
    rw [hpchar]
    exact (CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt _hp)⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by simpa [hpchar] using _hpℓ⟩
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  let SY := constantModelBoundedConstructible Λ Y ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  let := (localizingClosure_exists Λ Y SY).1
  have hY : (localizingClosureProEtale Λ Y).IsTriangulated :=
    (localizingClosure_exists Λ Y SY).2.2.2.1.1
  let := hY
  have : LocallySmall.{u + 1} (localizingClosureProEtale Λ Y).FullSubcategory :=
    locallySmall_of_faithful (localizingClosureProEtale Λ Y).ι
  have hsumsY : HasCoproducts.{u + 1}
      (localizingClosureProEtale Λ Y).FullSubcategory := by
    intro I
    let Q := localizingClosureProEtale Λ Y
    let : Q.IsClosedUnderColimitsOfShape (Discrete (ULift.{u + 2} I)) :=
      closure_closedUnderSums SY (ULift.{u + 2} I)
    let : Q.IsClosedUnderColimitsOfShape (Discrete I) :=
      ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
        (Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I))
    exact hasColimitsOfShape_of_closedUnderColimits (Discrete I) Q
  let := hsumsY
  have hpres (c : Compactification.BoundaryCompactification f) :=
    (compactification_localizing Λ ℓ k f c _hΛ).1
  refine ⟨hpres, hY, ?_⟩
  dsimp only
  have htri : ∀ c : Compactification.BoundaryCompactification f,
      (localizingLowerShriek Λ c.obj.obj (hpres c)).IsTriangulated := by
    intro c
    let P := localizingClosureProEtale Λ X
    let Q := localizingClosureProEtale Λ Y
    let F := rightDerivedLowerShriekOfCompactification Λ c.obj.obj
    have : F.IsTriangulated := by infer_instance
    exact inferInstanceAs ((Q.lift (P.ι ⋙ F) _).IsTriangulated)
  let SX := constantModelBoundedConstructible Λ X ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  let := (localizingClosure_exists Λ X SX).1
  have hsum : ∀ (c : Compactification.BoundaryCompactification f) (I : Type (u + 1)),
      PreservesColimitsOfShape (Discrete I) (localizingLowerShriek Λ c.obj.obj (hpres c)) := by
    intro c I
    let P := localizingClosureProEtale Λ X
    let Q := localizingClosureProEtale Λ Y
    let F := rightDerivedLowerShriekOfCompactification Λ c.obj.obj
    let e : Discrete (ULift.{u + 2} I) ≌ Discrete I :=
      Discrete.equivalence Equiv.ulift
    let : P.IsClosedUnderColimitsOfShape (Discrete (ULift.{u + 2} I)) :=
      closure_closedUnderSums SX (ULift.{u + 2} I)
    let : HasColimitsOfShape (Discrete (ULift.{u + 2} I))
        (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))) :=
      hasColimitsOfShape_of_equivalence e.symm
    have hlarge : PreservesColimitsOfShape (Discrete (ULift.{u + 2} I))
        (localizingLowerShriek Λ c.obj.obj (hpres c)) := by
      apply restricted_preservesColimits P Q F (hpres c)
      intro K hK
      exact (compactification_localizing Λ ℓ k f c _hΛ).2.2.1
        (ULift.{u + 2} I) K (fun i ↦ hK ⟨i⟩)
    let := hlarge
    exact preservesColimitsOfShape_of_equiv e _
  have hcg : IsCompactlyGeneratedTriangulated.{u + 1}
      (localizingClosureProEtale Λ X).FullSubcategory := by
    obtain ⟨I, E, _, hE, hgen⟩ := _hgen
    exact ⟨I, E, hE, hgen⟩
  have hleft : ∀ c : Compactification.BoundaryCompactification f,
      (localizingLowerShriek Λ c.obj.obj (hpres c)).IsLeftAdjoint := by
    intro c
    let := htri c
    exact brownRepresentabilityRightAdjoint.{u + 1} _ hcg (hsum c)
  choose G hadj using fun c ↦ (hleft c).exists_rightAdjoint
  let adj := fun c ↦ Classical.choice (hadj c)
  refine ⟨G, adj, ?_, ?_, ?_⟩
  · intro c
    let := htri c
    let := (adj c).rightAdjointCommShift ℤ
    have := (adj c).commShift_of_leftAdjoint ℤ
    exact ⟨(adj c).isTriangulated_rightAdjoint, this⟩
  · intro c J adjJ
    exact counitCompatibleIsoUnique (adj c) adjJ
  · obtain ⟨phi₀, _, hnorm₀, hid₀, hcomp₀⟩ :=
      compactification_coherence_cocycle Λ ℓ _hΛ f
    let phi : ∀ c d : Compactification.BoundaryCompactification f,
        localizingLowerShriek Λ c.obj.obj (hpres c) ≅
          localizingLowerShriek Λ d.obj.obj (hpres d) := fun c d ↦
      NatIso.ofComponents
        (fun K ↦ (localizingClosureProEtale Λ Y).isoMk ((phi₀ c d).app K))
        (fun v ↦ by
          apply ObjectProperty.hom_ext
          exact (phi₀ c d).hom.naturality v)
    have hid : ∀ c, phi c c = Iso.refl _ := by
      intro c
      apply Iso.ext
      apply NatTrans.ext
      funext K
      apply ObjectProperty.hom_ext
      exact congrArg (fun e ↦ e.hom.app K) (hid₀ c)
    have hcomp : ∀ c d e, phi c d ≪≫ phi d e = phi c e := by
      intro c d e
      apply Iso.ext
      apply NatTrans.ext
      funext K
      apply ObjectProperty.hom_ext
      exact congrArg (fun e ↦ e.hom.app K) (hcomp₀ c d e)
    refine ⟨phi, ?_, hid, hcomp, ?_⟩
    · intro c d r K
      have hn := hnorm₀ c d.obj d r (𝟙 d.obj) K
      change (phi₀ c d.obj).hom.app K = compactificationRefinementComponent Λ r K.obj
      have hrid₀ := compactificationRefinementComponent_id Λ ℓ k p _hp _hpℓ _hΛ f d K.obj
      rw [hrid₀] at hn
      exact (Category.comp_id _).symm.trans hn
    · exact coherentRightAdjointComparisons
        (C := (localizingClosureProEtale Λ X).FullSubcategory)
        (D := (localizingClosureProEtale Λ Y).FullSubcategory)
        (A := Compactification.BoundaryCompactification f)
        (fun c : Compactification.BoundaryCompactification f ↦
          localizingLowerShriek Λ c.obj.obj (hpres c)) G adj phi hid hcomp

end AlgebraicGeometry.ProEtale.CondensedRing
