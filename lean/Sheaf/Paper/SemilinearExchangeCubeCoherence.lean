/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.SemilinearExchangeCubeData
import Sheaf.Paper.SemilinearRationalOrdinaryCubes
import Sheaf.Paper.SemilinearRationalSupportCubes
import Sheaf.Paper.SemilinearRationalRefinementCubes
import Sheaf.Paper.SemilinearCommonOrdinaryCubes
import Sheaf.Paper.SemilinearCommonSupportCubes
import Sheaf.Paper.SemilinearCommonRefinementCubes


/-! # Semilinear Frobenius exchange coherence

Assembly of the ordinary, compact-support and refinement cube equations into the
fixed-pair and representative-change laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w a b c d e f
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open CategoryTheory.SuppliedExchangeProjection
open WeilConjectures.PodConstructibleMate
namespace WeilConjectures.PodExchangeCube

private theorem equivariant_of_cube
    {C : Type a} {B : Type b} [Category.{c} C] [Category.{d} B]
    {P : C ⥤ C} {Q : B ⥤ B} {F G : C ⥤ B}
    (cF : F ⋙ Q ≅ P ⋙ F) (cG : G ⋙ Q ≅ P ⋙ G) (α : F ⟶ G)
    (h : ∀ K, cF.hom.app K ≫ α.app (P.obj K) = Q.map (α.app K) ≫ cG.hom.app K) :
    Equivariant cF cG α := by
  refine ⟨h, ?_⟩
  have hh : Functor.whiskerRight α Q ≫ cG.hom =
      cF.hom ≫ Functor.whiskerLeft P α := by
    ext K
    exact (h K).symm
  intro K
  exact ((IsoAlgebra.mapOfNatIsoHom α hh).app K).hom.h.symm

private theorem equivariant_comp
    {C : Type a} {B : Type b} [Category.{c} C] [Category.{d} B]
    {P : C ⥤ C} {Q : B ⥤ B} {F G H : C ⥤ B}
    {cF : F ⋙ Q ≅ P ⋙ F} {cG : G ⋙ Q ≅ P ⋙ G} {cH : H ⋙ Q ≅ P ⋙ H}
    {α : F ⟶ G} {β : G ⟶ H}
    (hα : Equivariant cF cG α) (hβ : Equivariant cG cH β) :
    Equivariant cF cH (α ≫ β) := by
  apply equivariant_of_cube
  intro K
  simp only [NatTrans.comp_app, Functor.map_comp]
  rw [← Category.assoc, hα.1, Category.assoc, hβ.1, ← Category.assoc]

private theorem equivariant_whiskerRight
    {C : Type a} {B : Type b} {T : Type c}
    [Category.{d} C] [Category.{e} B] [Category.{f} T]
    {P : C ⥤ C} {Q : B ⥤ B} {R : T ⥤ T} {F F' : C ⥤ B} {G : B ⥤ T}
    {cF : F ⋙ Q ≅ P ⋙ F} {cF' : F' ⋙ Q ≅ P ⋙ F'}
    (cG : G ⋙ R ≅ Q ⋙ G) {α : F ⟶ F'} (hα : Equivariant cF cF' α) :
    Equivariant (iterated cF cG) (iterated cF' cG) (Functor.whiskerRight α G) := by
  apply equivariant_of_cube
  intro K
  simp only [iterated, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]
  have hn : cG.hom.app (F.obj K) ≫ G.map (Q.map (α.app K)) =
      R.map (G.map (α.app K)) ≫ cG.hom.app (F'.obj K) := by
    simpa only [Functor.comp_map] using (cG.hom.naturality (α.app K)).symm
  rw [Category.assoc, ← G.map_comp, hα.1, G.map_comp, ← Category.assoc, hn,
    Category.assoc]

private theorem equivariant_whiskerLeft
    {C : Type a} {B : Type b} {T : Type c}
    [Category.{d} C] [Category.{e} B] [Category.{f} T]
    {P : C ⥤ C} {Q : B ⥤ B} {R : T ⥤ T} {F : C ⥤ B} {G G' : B ⥤ T}
    (cF : F ⋙ Q ≅ P ⋙ F) {cG : G ⋙ R ≅ Q ⋙ G} {cG' : G' ⋙ R ≅ Q ⋙ G'}
    {α : G ⟶ G'} (hα : Equivariant cG cG' α) :
    Equivariant (iterated cF cG) (iterated cF cG') (Functor.whiskerLeft F α) := by
  apply equivariant_of_cube
  intro K
  simp only [iterated, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]
  have hn : G.map (cF.hom.app K) ≫ α.app (F.obj (P.obj K)) =
      α.app (Q.obj (F.obj K)) ≫ G'.map (cF.hom.app K) := α.naturality _
  rw [Category.assoc, hn, ← Category.assoc, hα.1, Category.assoc]

private theorem changedExchange_comparison
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
    [∀ X : SixFunctorSpace D, Category.{w} (B X)]
    (S : SixFunctorPushStage D B)
    {T : ∀ X : SixFunctorSpace D, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (E : SixFunctorExchangeData S T Q)
    (c d : Compactification Q.f.hom.left) (c' d' : Compactification Q.f'.hom.left) :
    Functor.whiskerRight (S.comparison Q.f c d).hom (S.pull Q.g) ≫
        changedExchange S E d d' =
      changedExchange S E c c' ≫
        Functor.whiskerLeft (S.pull Q.g') (S.comparison Q.f' c' d').hom := by
  have comp (f : Q.X ⟶ Q.Y) (a b c : Compactification f.hom.left) :
      (S.comparison f a b).hom ≫ (S.comparison f b c).hom =
        (S.comparison f a c).hom :=
    (congrArg Iso.hom (S.comparison_trans f a b c)).symm
  have comp' (a b c : Compactification Q.f'.hom.left) :
      (S.comparison Q.f' a b).hom ≫ (S.comparison Q.f' b c).hom =
        (S.comparison Q.f' a c).hom :=
    (congrArg Iso.hom (S.comparison_trans Q.f' a b c)).symm
  ext K
  simp only [changedExchange, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, ← Functor.map_comp, ← Category.assoc]
  rw [← NatTrans.comp_app, comp]
  simp only [Category.assoc]
  rw [← NatTrans.comp_app, comp']

private theorem supportComposition_comparison_aux
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
    [∀ X : SixFunctorSpace D, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) {X Y Z : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (e : k = f ≫ g)
    (cf df : Compactification f.hom.left) (cg dg : Compactification g.hom.left)
    (c d : Compactification k.hom.left) :
    Functor.whiskerRight (S.comparison f cf df).hom (S.support g cg) ≫
        Functor.whiskerLeft (S.support f df) (S.comparison g cg dg).hom ≫
        ((S.composition f g df dg
          (d.copy (congrArg (fun t ↦ t.hom.left) e).symm)).symm ≪≫
          (supportTransport S e d).symm).hom =
      ((S.composition f g cf cg
          (c.copy (congrArg (fun t ↦ t.hom.left) e).symm)).symm ≪≫
          (supportTransport S e c).symm).hom ≫ (S.comparison k c d).hom := by
  cases e
  have ht (a : Compactification f.hom.left) (b : Compactification g.hom.left)
      (c : Compactification (f ≫ g).hom.left) :
      (S.composition f g a b
          (c.copy (congrArg (fun t ↦ t.hom.left) (rfl : f ≫ g = f ≫ g)).symm)).symm ≪≫
        (supportTransport S rfl c).symm = (S.composition f g a b c).symm := by
    cases c
    exact Iso.trans_refl _
  rw [ht, ht]
  simp only [Iso.symm_hom]
  have h := congrArg Iso.hom (S.composition_comparison f g cf df cg dg c d)
  dsimp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom] at h
  apply (cancel_epi (S.composition f g cf cg c).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.id_comp, Category.comp_id] using
      congrArg (fun t ↦ t ≫ (S.composition f g df dg d).inv) h.symm

private theorem laws_of_cubes
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
    [∀ X : SixFunctorSpace D, Category.{w} (B X)]
    (S : SixFunctorPushStage D B)
    (T : ∀ X : SixFunctorSpace D, B X ⥤ B X ⥤ B X)
    (E : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (P : ∀ X : Models D, B ((fiberModels D).obj X) ⥤ B ((fiberModels D).obj X))
    (L : Comparisons S P)
    (h1 : (∀ (Q : ModelSquare D) [IsSeparated Q.f.hom.left] [IsSeparated Q.f'.hom.left]
      [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left],
    Equivariant (iterated (L.direct Q.f) (L.pull Q.g))
      (iterated (L.pull Q.g') (L.direct Q.f')) (directExchange S (E Q.fiber))))
    (h2 : (∀ (Q : ModelSquare D) [IsSeparated Q.f.hom.left] [IsSeparated Q.f'.hom.left]
      [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left]
      (c₀ : Compactification Q.f.hom.left) (c₀' : Compactification Q.f'.hom.left)
      (c : Compactification ((fiberModels D).map Q.f).hom.left)
      (c' : Compactification ((fiberModels D).map Q.f').hom.left),
    Equivariant (iterated (L.support Q.f c₀ c) (L.pull Q.g))
      (iterated (L.pull Q.g') (L.support Q.f' c₀' c'))
      (changedExchange S (E Q.fiber) c c')))
    (h3 : (∀ {X Y Z : Models D} (f : X ⟶ Y) (h : Y ⟶ Z)
      [IsSeparated f.hom.left] [IsSeparated h.hom.left],
    Equivariant (iterated (L.direct f) (L.direct h)) (L.direct (f ≫ h))
      (directComposition S f h).hom))
    (h4 : (∀ {X Y Z : Models D} (f : X ⟶ Y) (h : Y ⟶ Z)
      [IsSeparated f.hom.left] [IsSeparated h.hom.left]
      (cf₀ : Compactification f.hom.left) (ch₀ : Compactification h.hom.left)
      (c₀ : Compactification (f ≫ h).hom.left)
      (cf : Compactification ((fiberModels D).map f).hom.left)
      (ch : Compactification ((fiberModels D).map h).hom.left)
      (c : Compactification ((fiberModels D).map (f ≫ h)).hom.left),
    Equivariant (iterated (L.support f cf₀ cf) (L.support h ch₀ ch))
      (L.support (f ≫ h) c₀ c) (supportComposition S f h cf ch c).hom))
    (h5 : (∀ {X Y : Models D} (f : X ⟶ Y) (c₀ c₀' : Compactification f.hom.left)
      (c c' : Compactification ((fiberModels D).map f).hom.left),
    Equivariant (L.support f c₀ c) (L.support f c₀' c')
      (S.comparison ((fiberModels D).map f) c c').hom))
    : Laws S T E P L := by
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · intro Q _ _ _ _ c₀ d₀ c₀' d₀' c d c' d'
    exact ⟨equivariant_whiskerRight (L.pull Q.g) (h5 Q.f c₀ d₀ c d),
      equivariant_whiskerLeft (L.pull Q.g') (h5 Q.f' c₀' d₀' c' d'),
      changedExchange_comparison S (E Q.fiber) c d c' d'⟩
  · intro X Y Z f h _ _ cf₀ df₀ ch₀ dh₀ c₀ d₀ cf df ch dh c d
    refine ⟨equivariant_comp
      (equivariant_whiskerRight (L.support h ch₀ ch) (h5 f cf₀ df₀ cf df))
      (equivariant_whiskerLeft (L.support f df₀ df) (h5 h ch₀ dh₀ ch dh)),
      h5 (f ≫ h) c₀ d₀ c d, ?_⟩
    exact supportComposition_comparison_aux S
      ((fiberModels D).map f) ((fiberModels D).map h)
      ((fiberModels D).map (f ≫ h)) ((fiberModels D).map_comp f h)
      cf df ch dh c d

/-- The specified rational exchanges and compositors satisfy the semilinear cube identities
and hence are morphisms of the recorded fixed-pair categories. Compactification changes
intertwine these identities on the original operation domains.
Source: prop-weil-operations.proof.md, sentence 1; lem-fix-weil-operations.proof.md,
composition/exchange paragraph (blueprint: lem-pod-semilinear-exchange-cube-coherence).
Proof: (1) Use lem-weil-frobenius-square-cartesian to commute each model arrow with
geometric Frobenius. Relabel each source k-structure by a_W g_W, using relabeling;
the schemes remain finite type and every face is k-linear. (2) Underlying pro-etale
sites, constant coefficients, resolutions and units/counits are unchanged, so the
canonical exchange components of def-exchange-projection are unchanged. (3) Apply
fix-lem-exchanges(1) to this isomorphism of square data, or paste its two horizontal
faces using clause (2). The resulting equation is Equivariant with the displayed
iterated comparisons, for ordinary and proper/open exchange. No inverse to d is used.
(4) Paste the two Frobenius faces vertically. Clause (2), with the prescribed ordinary
and support compositors, gives the composition equation. (5) Base-change any chosen
compactification along g_Y; its projection is an isomorphism. Relabel that source
and the base-changed refinements, without asking that the compactification descend.
Clause (4) gives the refinement equation and intertwines both exchange and composition.
The normalization formulas transport each model anchor to every geometric choice;
refinement equivariance compares the distinct model anchors as part of the conclusion.
(6) Naturality at theta_K turns each cube equation into the fixed-pair morphism equation.
This uses arbitrary Weil structures, without Frobenius-stable integral lattices.
(7) Rationalization preserves the integral equalities and composition; common-stage
representatives use one finite field for the whole finite diagram. The stipulated scalar
comparisons cancel at intermediate objects and the tower cocycle makes the result
independent of further extensions. All finite-Tor, lattice and origin restrictions are
those of fix-lem-exchanges and the supplied operation datum; no domain is enlarged. -/
theorem rational_coherence
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn)
    (L : Comparisons S.higher.rational
      (fun X : Models D ↦ sfWeilFrobeniusPullback D C.l C.different X.obj E))
    (hL : rationalNormalized D C E S.higher L) :
    Laws S.higher.rational S.higher.rationalTensor S.higher.rationalExchange
      (fun X : Models D ↦ sfWeilFrobeniusPullback D C.l C.different X.obj E) L := by
  apply laws_of_cubes
  · intro Q _ _ _ _
    exact equivariant_of_cube _ _ _ ((rational_ordinary_cubes D C E n hn S L hL).1 Q)
  · intro Q _ _ _ _ c₀ c₀' c c'
    exact equivariant_of_cube _ _ _ ((rational_support_cubes D C E n hn S L hL).1
      Q c₀ c₀' c c')
  · intro X Y Z f h _ _
    exact equivariant_of_cube _ _ _ ((rational_ordinary_cubes D C E n hn S L hL).2 f h)
  · intro X Y Z f h _ _ cf₀ ch₀ c₀ cf ch c
    exact equivariant_of_cube _ _ _ ((rational_support_cubes D C E n hn S L hL).2
      f h cf₀ ch₀ c₀ cf ch c)
  · intro X Y f c₀ c₀' c c'
    exact equivariant_of_cube _ _ _ (rational_refinement_cubes D C E n hn S L hL
      f c₀ c₀' c c')

/-- The specified common exchanges and compositors satisfy the semilinear cube identities
and hence are morphisms of the recorded fixed-pair categories. Compactification changes
intertwine these identities on the original operation domains.
Source: prop-weil-operations.proof.md, sentence 1; lem-fix-weil-operations.proof.md,
composition/exchange paragraph (blueprint: lem-pod-semilinear-exchange-cube-coherence).
Proof: (1) Use lem-weil-frobenius-square-cartesian to commute each model arrow with
geometric Frobenius. Relabel each source k-structure by a_W g_W, using relabeling;
the schemes remain finite type and every face is k-linear. (2) Underlying pro-etale
sites, constant coefficients, resolutions and units/counits are unchanged, so the
canonical exchange components of def-exchange-projection are unchanged. (3) Apply
fix-lem-exchanges(1) to this isomorphism of square data, or paste its two horizontal
faces using clause (2). The resulting equation is Equivariant with the displayed
iterated comparisons, for ordinary and proper/open exchange. No inverse to d is used.
(4) Paste the two Frobenius faces vertically. Clause (2), with the prescribed ordinary
and support compositors, gives the composition equation. (5) Base-change any chosen
compactification along g_Y; its projection is an isomorphism. Relabel that source
and the base-changed refinements, without asking that the compactification descend.
Clause (4) gives the refinement equation and intertwines both exchange and composition.
The normalization formulas transport each model anchor to every geometric choice;
refinement equivariance compares the distinct model anchors as part of the conclusion.
(6) Naturality at theta_K turns each cube equation into the fixed-pair morphism equation.
This uses arbitrary Weil structures, without Frobenius-stable integral lattices.
(7) Rationalization preserves the integral equalities and composition; common-stage
representatives use one finite field for the whole finite diagram. The stipulated scalar
comparisons cancel at intermediate objects and the tower cocycle makes the result
independent of further extensions. All finite-Tor, lattice and origin restrictions are
those of fix-lem-exchanges and the supplied operation datum; no domain is enlarged. -/
theorem common_coherence
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn)
    (L : Comparisons S.closure.commonStage
      (fun X : Models D ↦ sfCommonStageWeilFrobeniusPullback D C.l C.different X.obj C.Qbar))
    (hL : commonNormalized D C S.closure L) :
    Laws S.closure.commonStage S.closure.commonStageTensor S.closure.commonStageExchange
      (fun X : Models D ↦ sfCommonStageWeilFrobeniusPullback D C.l C.different X.obj C.Qbar) L := by
  apply laws_of_cubes
  · intro Q _ _ _ _
    exact equivariant_of_cube _ _ _ ((common_ordinary_cubes D C E n hn S L hL).1 Q)
  · intro Q _ _ _ _ c₀ c₀' c c'
    exact equivariant_of_cube _ _ _ ((common_support_cubes D C E n hn S L hL).1
      Q c₀ c₀' c c')
  · intro X Y Z f h _ _
    exact equivariant_of_cube _ _ _ ((common_ordinary_cubes D C E n hn S L hL).2 f h)
  · intro X Y Z f h _ _ cf₀ ch₀ c₀ cf ch c
    exact equivariant_of_cube _ _ _ ((common_support_cubes D C E n hn S L hL).2
      f h cf₀ ch₀ c₀ cf ch c)
  · intro X Y f c₀ c₀' c c'
    exact equivariant_of_cube _ _ _ (common_refinement_cubes D C E n hn S L hL
      f c₀ c₀' c c')

end WeilConjectures.PodExchangeCube
