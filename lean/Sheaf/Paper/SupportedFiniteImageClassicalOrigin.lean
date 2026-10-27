/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups E1, Q7
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Sheaf.Paper.FiniteDiscreteEncodingConstructibility
import all Sheaf.Paper.FiniteDiscreteEncodingCompactification
import all Sheaf.Paper.FiniteDiscreteEncodingPullbackFixed
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.GroupTheory.Torsion

/-! # Classical torsion origin of supported finite-coefficient images

Only the finite discrete coefficient branch is considered. This assertion uses no
Noetherianity and makes no claim about continuous integral images or their reductions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

namespace FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]

omit [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] [Finite A] in
private theorem localModel_classical (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (h : ordinaryLocalModel A T M) :
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).essImage M := by
  let B := ULift.{u + 1} A
  let F := (sheafCompose (Scheme.ProEt.topology T) (forget (ModuleCat.{u + 1} B))).obj M
  obtain ⟨C, hC⟩ := h
  have (i : C.I₀) : WeaklyEtale (C.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ ⟨i⟩
  let V : ULift.{u + 1} C.I₀ → T.ProEt := fun i ↦ Scheme.ProEt.mk (C.f i.down)
  have hV : (Scheme.ProEt.topology T).CoversTop V := by
    intro W
    apply (Scheme.ProEt.topology T).superset_covering _
      (Scheme.ProEt.ofArrows_baseChange_mem_topology W C.f C.mem₀)
    rintro Z f ⟨_, a, _, ⟨i⟩, rfl⟩
    exact ⟨ULift.up i, ⟨MorphismProperty.Over.homMk
      (a.left ≫ pullback.snd W.hom (C.f i)) (by
        change (a.left ≫ pullback.snd W.hom (C.f i)) ≫ C.f i = Z.hom
        rw [Category.assoc, ← pullback.condition]
        exact MorphismProperty.Over.w a)⟩⟩
  have hlocal : Scheme.IsProEtaleLocallyConstant T F := by
    refine ⟨_, V, hV, fun i ↦ ?_⟩
    obtain ⟨P, _, ⟨e⟩⟩ := hC i.down
    let q := (sheafCompose (Scheme.ProEt.topology (C.X i.down))
      (forget (ModuleCat.{u + 1} B))).mapIso
        (((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B)
          (C.f i.down) inferInstance).app M).symm ≪≫ e)
    exact ⟨P, ⟨q ≪≫ (constantCommuteCompose (Scheme.ProEt.topology (C.X i.down))
      (forget (ModuleCat.{u + 1} B))).app P⟩⟩
  have hc := (Scheme.proEtale_locallyClassical_etaleCover T F).2.1 hlocal
  have hclass : IsClassical F := (Scheme.proEtaleClassicalSheavesImage T F).1.mp hc.2
  obtain ⟨_, _, _, _, _, himage⟩ := proEtaleClassicalSheavesModules T B
  exact (himage M).mp hclass

omit [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] [Finite A] in
private theorem classical_image {T : Scheme.{u}}
    {L M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (f : L ⟶ M)
    (hL : (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).essImage L)
    (hM : (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).essImage M) :
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).essImage (image f) := by
  let N := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
  obtain ⟨L₀, ⟨eL⟩⟩ := hL
  obtain ⟨M₀, ⟨eM⟩⟩ := hM
  let g := N.preimage (eL.hom ≫ f ≫ eM.inv)
  refine ⟨image g, ⟨(PreservesImage.iso N g).symm ≪≫
    im.mapIso (Arrow.isoMk' (N.map g) f eL eM ?_)⟩⟩
  simp [g]

private theorem encoding_classical {T : Scheme.{u}} (e : Encoding A T)
    (M : Internal A T) (h : HasFiniteConstantLocalModel (coefficient A) T M) :
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).essImage
      ((e.ordinary.functor ⋙ e.fixed.functor).obj M) := by
  exact localModel_classical A T _ ((encoding_constructibility A T e).1 M |>.mp h)

omit [DiscreteTopology A] [Finite A] in
private theorem extension_classical {X S : Scheme.{u}} {t : QcqsOpenClosedTree X}
    (p : t.Path S) (E : ∀ T : Scheme.{u}, Encoding A T) (M : Internal A S)
    (h : (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S).essImage
      (((E S).ordinary.functor ⋙ (E S).fixed.functor).obj M)) :
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).essImage
      (((E X).ordinary.functor ⋙ (E X).fixed.functor).obj
        ((p.extension (coefficient A)).obj M)) := by
  induction p with
  | root t => exact h
  | @openBranch X U Z W _ _ j i _ _ _ _ hc a b p ih =>
    obtain ⟨G, ⟨e⟩⟩ := ih M h
    refine ⟨(Etale.openImmersionLowerShriek _ j).obj G, ⟨?_⟩⟩
    exact (openImmersionLowerShriekComparisonUpperStarIso _ j).app G ≪≫
      (openImmersionLowerShriek _ j).mapIso e ≪≫
        ((encodingOpenShriekIso A j (E X) (E U)).app
          ((p.extension (coefficient A)).obj M)).symm
  | @closedBranch X U Z W _ _ j i _ _ _ _ hc a b p ih =>
    obtain ⟨G, ⟨e⟩⟩ := ih M h
    have : IsIso (lowerStarComparisonUpperStarBaseChange i
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
      isIso_lowerStarComparisonUpperStarBaseChange i _
    refine ⟨(Etale.lowerStar _ i).obj G, ⟨?_⟩⟩
    exact (asIso (lowerStarComparisonUpperStarBaseChange i
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))).app G ≪≫
      (lowerStar _ i).mapIso e ≪≫
        ((encodingPushforwardNatIso A X Z i (E X) (E Z)).app
          ((p.extension (coefficient A)).obj M)).symm

private def encodingUnderlyingIso (T : Scheme.{u}) (e : Encoding A T) (M : Internal A T) :
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1})).obj
        ((e.ordinary.functor ⋙ e.fixed.functor).obj M) ≅ M.X := by
  rw [e.ordinary_functor, e.fixed_functor]
  exact ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))

end FiniteDiscreteOrdinary

/-- The underlying abelian sheaf of a supported finite-coefficient image is classical torsion.
Source: HRS Section 8, proof of Lemma 8.6, discrete torsion paragraph;
Bhatt--Scholze Proposition 5.1.1 and Lemma 5.1.4; Stacks Tags 09BM and 09BN.
(blueprint: lem-sfb-supported-finite-image-classical-origin).

Proof: normalized finite-coefficient encoding turns each scalar local model into a
constant finite module on its specified pro-etale cover. Local classical descent and
full faithfulness descend addition and every scalar operation to etale sheaves.
Descend f by full faithfulness and apply preservation of images to the etale morphism;
this identifies its image with the actual image of f. Induct along p. At an open
edge use the finite-coefficient extension-by-zero comparison. At a closed edge the
morphism is affine, hence qcqs, and the existing underived direct-image comparison
identifies its pushforward with a classical sheaf. The internal/ordinary operations
comparison identifies these with the path functors used below. Pullback along v
commutes with comparison inverse image, giving an etale A-module antecedent on U.
Choose a positive integer annihilating the finite additive group of A (one can use
its finite cardinality, or 1 for the zero ring). It annihilates every A-module.
The etale antecedent has this scalar module structure sectionwise, so its underlying
abelian sheaf has torsion sections and is therefore locally torsion. This construction also
handles empty paths, empty schemes and zero maps; no common local-model cover is needed.
-/
theorem supported_finite_image_classical_origin
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A]
    {X S : Scheme.{u}} (tree : QcqsOpenClosedTree X) (p : tree.Path S)
    (L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (FiniteDiscreteOrdinary.coefficient A) S)) (f : L ⟶ M)
    (hL : HasFiniteConstantLocalModel (FiniteDiscreteOrdinary.coefficient A) S L)
    (hM : HasFiniteConstantLocalModel (FiniteDiscreteOrdinary.coefficient A) S M)
    {U : Scheme.{u}} (v : U ⟶ X) :
    ∃ G : Sheaf U.smallEtaleTopology Ab.{u + 1}, G.IsTorsion ∧
      Nonempty ((comparisonUpperStar Ab.{u + 1} U).obj G ≅
        ((CondensedRing.upperStar (FiniteDiscreteOrdinary.coefficient A) v).obj
          ((p.extension (FiniteDiscreteOrdinary.coefficient A)).obj (image f))).X) := by
  classical
  let E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T :=
    fun T ↦ Classical.choice (FiniteDiscreteOrdinary.encoding_exists A T)
  let H := (E S).ordinary.functor ⋙ (E S).fixed.functor
  have hI := FiniteDiscreteOrdinary.classical_image A (H.map f)
    (FiniteDiscreteOrdinary.encoding_classical A (E S) L hL)
    (FiniteDiscreteOrdinary.encoding_classical A (E S) M hM)
  obtain ⟨I₀, ⟨eI⟩⟩ := hI
  have hImage : (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S).essImage
      (H.obj (image f)) := ⟨I₀, ⟨eI ≪≫ PreservesImage.iso H f⟩⟩
  obtain ⟨G₀, ⟨e₀⟩⟩ := FiniteDiscreteOrdinary.extension_classical A p E (image f) hImage
  let G := (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) v).obj G₀
  let e₁ := (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) v).app G₀
  let e₂ := (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) v).mapIso e₀
  let e₃ := (FiniteDiscreteOrdinary.encoding_pullback_fixed A v (E X) (E U)
    ((p.extension (FiniteDiscreteOrdinary.coefficient A)).obj (image f))).some
  let e : (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) U).obj G ≅
      (((E U).ordinary.functor ⋙ (E U).fixed.functor).obj
        ((CondensedRing.upperStar (FiniteDiscreteOrdinary.coefficient A) v).obj
          ((p.extension (FiniteDiscreteOrdinary.coefficient A)).obj (image f)))) :=
    e₁.symm ≪≫ e₂ ≪≫ e₃.symm
  let V := sheafCompose U.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1})
  refine ⟨V.obj G, Sheaf.IsTorsion.of_forall_isAddTorsion (fun W ↦ ?_), ⟨?_⟩⟩
  · exact IsAddTorsion.module_of_finite (ULift.{u + 1} A) (G.obj.obj W)
  · exact (sheafComposeForget₂CompComparisonUpperStarIso (ULift.{u + 1} A) U).app G ≪≫
      (sheafCompose (Scheme.ProEt.topology U)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1})).mapIso e ≪≫
      FiniteDiscreteOrdinary.encodingUnderlyingIso A U (E U) _

end AlgebraicGeometry.ProEtale
