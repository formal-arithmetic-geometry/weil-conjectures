/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
public import WeilConjectures.AlgebraicGeometry.AffineConormalSections
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.Compactification.StrictTransformBlowup
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation
import Sheaf.RingTheory.RegularSequenceConormal
import Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible

/-!
# Conormal and blowup geometry of a regular flag

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XVI, proof of Lemma 2.3.3,
pp. 234--235, and proof of Theorem 2.3.2, pp. 236--237
(blueprint: lem-per-regular-flag-blowup-geometry).

The auxiliary records describe conclusions about the specified blowups and their actual
ideal sheaves. In particular they are not extra hypotheses on a flag. Conormal maps are
normalized by ideal representatives, and the exceptional projective identification is
normalized by its tautological quotient.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.RegularFlagBlowupGeometry

noncomputable section

/-- The conormal module, using the existing tensor pullback of the actual kernel ideal.
Source: ILO XVI, p. 234 (blueprint: lem-per-regular-flag-blowup-geometry). -/
def conormal {X Z : Scheme.{u}} (i : Z ⟶ X) : Z.Modules :=
  (Scheme.Modules.tensorPullback i).obj i.ker.toModules

/-- Quasi-coherence of the existing conormal construction, from its affine-section theorem.
Source: Stacks 01R3; ILO XVI, p. 234
(blueprint: lem-per-regular-flag-blowup-geometry). -/
instance conormalQuasicoherent {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (conormal i).IsQuasicoherent :=
  (Scheme.Modules.affine_conormal_sections.{u, u} i).1

/-- The ideal-induced conormal map in a commutative square. Its adjoint sends every
ideal representative to its image under the ambient scheme map. The intermediate ideal
map is fixed on sections, so this condition does not permit an arbitrary conormal map.
Source: ILO XVI, p. 235, natural conormal diagram; Stacks 01R4
(blueprint: lem-per-regular-flag-blowup-geometry). -/
def IsConormalMap {X Z X' Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')
    (c : (Scheme.Modules.tensorPullback f).obj (conormal i') ⟶ conormal i) : Prop :=
  ∃ γ : (Scheme.Modules.tensorPullback g).obj i'.ker.toModules ⟶ i.ker.toModules,
    (∀ (U' : X'.Opens) (s : Γ(i'.ker.toModules, U')),
      i.ker.toModulesι.app (g ⁻¹ᵁ U')
        (γ.app (g ⁻¹ᵁ U')
          (Scheme.Modules.tensorPullbackSection g i'.ker.toModules U' s)) =
        g.app U' (i'.ker.toModulesι.app U' s)) ∧
    (Scheme.Modules.tensorPullbackSectionAdjunction i').unit.app i'.ker.toModules ≫
      (Scheme.Modules.pushforward i').map
        ((Scheme.Modules.tensorPullbackSectionAdjunction f).unit.app (conormal i') ≫
          (Scheme.Modules.pushforward f).map c) ≫
      (Scheme.Modules.pushforwardComp f i').hom.app (conormal i) ≫
      (Scheme.Modules.pushforwardCongr h.symm).hom.app (conormal i) =
    (Scheme.Modules.tensorPullbackSectionAdjunction g).unit.app i'.ker.toModules ≫
      (Scheme.Modules.pushforward g).map
        (γ ≫ (Scheme.Modules.tensorPullbackSectionAdjunction i).unit.app i.ker.toModules) ≫
      (Scheme.Modules.pushforwardComp i g).hom.app (conormal i)

/-- Transport of iterated tensor pullback across a commutative square, with the existing
section-normalized composition comparisons.
Source: ILO XVI, p. 235 (blueprint: lem-per-regular-flag-blowup-geometry). -/
def squarePullbackIso {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (d : C ⟶ D) (h : a ≫ b = c ≫ d) (M : D.Modules) :
    (Scheme.Modules.tensorPullback a).obj ((Scheme.Modules.tensorPullback b).obj M) ≅
      (Scheme.Modules.tensorPullback c).obj ((Scheme.Modules.tensorPullback d).obj M) :=
  ((Scheme.Modules.tensorPullbackSectionComp a b).app M).symm ≪≫
    eqToIso (congrArg (fun k ↦ (Scheme.Modules.tensorPullback k).obj M) h) ≪≫
    (Scheme.Modules.tensorPullbackSectionComp c d).app M

/-- The conormal sequence of the flag, including its natural-map normalizations.
Source: ILO XVI, p. 235 and p. 237
(blueprint: lem-per-regular-flag-blowup-geometry). -/
structure ConormalSequence {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    (m n : ℕ) where
  rankI : (conormal i).IsFiniteLocallyFreeOfRank m
  rankJ : (conormal j).IsFiniteLocallyFreeOfRank n
  rankComposite : (conormal (i ≫ j)).IsFiniteLocallyFreeOfRank (m + n)
  inclusion : (Scheme.Modules.tensorPullback i).obj (conormal j) ⟶ conormal (i ≫ j)
  quotient : conormal (i ≫ j) ⟶ conormal i
  naturalInclusion : IsConormalMap (i ≫ j) j (𝟙 X) i (Category.comp_id _) inclusion
  naturalQuotient : IsConormalMap i (i ≫ j) j (𝟙 Z) (Category.id_comp _).symm
    ((Scheme.Modules.tensorPullbackSectionId Z).hom.app (conormal (i ≫ j)) ≫ quotient)
  zero : inclusion ≫ quotient = 0
  shortExact : (ShortComplex.mk inclusion quotient zero).ShortExact

/-- The Rees degree-one twist is the exceptional ideal: on each affine base chart its
restriction is the existing `Proj.twist` for the Rees grading. The comparison sends
each pulled-back ideal generator a to the homogeneous section aT. These generators
fix the comparisons on overlaps, giving the global degree-one identification.
Source: ILO XVI, p. 234; Stacks 02OS
(blueprint: lem-per-regular-flag-blowup-geometry). -/
def IsReesTwist {X : Scheme.{u}} (J : X.IdealSheafData)
    (K : J.blowup.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens,
    ∃ e : (Scheme.Modules.tensorPullback (J.blowupι U)).obj K.toModules ≅
      Proj.twist (reesGrading (J.ideal U)) 1,
    ∀ a : J.ideal U,
      ∃ s : Γ(K.toModules, J.blowupMap ⁻¹ᵁ U.1),
        K.toModulesι.app (J.blowupMap ⁻¹ᵁ U.1) s =
          J.blowupMap.app U.1 (a : Γ(X, U.1)) ∧
        e.hom.app (J.blowupι U ⁻¹ᵁ (J.blowupMap ⁻¹ᵁ U.1))
            (Scheme.Modules.tensorPullbackSection (J.blowupι U) K.toModules
              (J.blowupMap ⁻¹ᵁ U.1) s) =
          (Proj.unitToTwist (𝒜 := reesGrading (J.ideal U))
            (reesX_mem (J.ideal U) (a : Γ(X, U.1)) a.2)).app
              (J.blowupι U ⁻¹ᵁ (J.blowupMap ⁻¹ᵁ U.1))
              (1 : Γ(Proj (reesGrading (J.ideal U)),
                J.blowupι U ⁻¹ᵁ (J.blowupMap ⁻¹ᵁ U.1)))

/-- The first blowup diagram, its natural conormal quotients, and its excess kernels.
The kernel isomorphism commutes with their inclusions in the displayed conormal square.
Source: ILO XVI, proof of Lemma 2.3.3, pp. 234--235
(blueprint: lem-per-regular-flag-blowup-geometry). -/
def FirstBlowup {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (m n : ℕ)
    (S : ConormalSequence i j m n) : Prop :=
  ∃ P : Scheme.{u},
  ∃ p : P ⟶ Y,
  ∃ exceptional : P ⟶ j.ker.blowup,
  ∃ cartesian : IsPullback p exceptional j j.ker.blowupMap,
  IsClosedImmersion exceptional ∧
  exceptional.ker.IsInvertible ∧
  IsReesTwist j.ker exceptional.ker ∧
  ∃ quotient : (Scheme.Modules.tensorPullback p).obj (conormal j) ⟶ conormal exceptional,
  IsConormalMap exceptional j j.ker.blowupMap p cartesian.w.symm quotient ∧
  Epi quotient ∧
  ∃ tautological : ProjectiveBundleQuotientGeometry.TautologicalQuotient (conormal j),
  ∃ projective : P ≅ (SymmetricAlgebraSheaf.gradedAlgebraData (conormal j)).relProj,
  ProjectiveBundleQuotientGeometry.Classifies
    tautological p (conormal exceptional) quotient projective.hom ∧
  ∃ P' : Scheme.{u},
  ∃ p' : P' ⟶ Z,
  ∃ inclusion : P' ⟶ P,
  ∃ baseChange : IsPullback p' inclusion i p,
  IsRegularImmersion m inclusion ∧
  IsRegularImmersion (m + 1) (inclusion ≫ exceptional) ∧
  ∃ quotient' : (Scheme.Modules.tensorPullback p').obj (conormal (i ≫ j)) ⟶
    conormal (inclusion ≫ exceptional),
  IsConormalMap (inclusion ≫ exceptional) (i ≫ j)
    j.ker.blowupMap p' (by rw [Category.assoc, ← cartesian.w, ← Category.assoc,
      ← baseChange.w, Category.assoc]) quotient' ∧
  Epi quotient' ∧
  (kernel quotient).IsFiniteLocallyFreeOfRank (n - 1) ∧
  (kernel quotient').IsFiniteLocallyFreeOfRank (n - 1) ∧
  ∃ kernelIso : (Scheme.Modules.tensorPullback inclusion).obj (kernel quotient) ≅ kernel quotient',
  kernelIso.hom ≫ kernel.ι quotient' =
    (Scheme.Modules.tensorPullback inclusion).map (kernel.ι quotient) ≫
      (squarePullbackIso inclusion p p' i baseChange.w.symm (conormal j)).hom ≫
      (Scheme.Modules.tensorPullback p').map S.inclusion ∧
  ∃ conormalIso : (Scheme.Modules.tensorPullback p').obj (conormal i) ≅ conormal inclusion,
  IsConormalMap inclusion i p p' baseChange.w.symm conormalIso.hom

/-- The invertible-ideal product isomorphism is normalized by multiplication of ideal
sections. This includes its canonical trivialization wherever all ideals are unit ideals.
Source: ILO XVI, p. 236 (blueprint: lem-per-regular-flag-blowup-geometry). -/
def IsIdealProduct {X B : Scheme.{u}} (π : B ⟶ X) (I : X.IdealSheafData)
    (J K : B.IdealSheafData)
    (e : (Scheme.Modules.tensorPullback π).obj I.toModules ≅ J.toModules ⊗ K.toModules) :
    Prop :=
  ∀ (U : X.Opens) (s : Γ(I.toModules, U))
    (a : Γ(J.toModules, π ⁻¹ᵁ U)) (b : Γ(K.toModules, π ⁻¹ᵁ U)),
    π.app U (I.toModulesι.app U s) =
        (@id Γ(B, π ⁻¹ᵁ U) (J.toModulesι.app (π ⁻¹ᵁ U) a)) *
          (@id Γ(B, π ⁻¹ᵁ U) (K.toModulesι.app (π ⁻¹ᵁ U) b)) →
      e.hom.app (π ⁻¹ᵁ U) (Scheme.Modules.tensorPullbackSection π I.toModules U s) =
        Scheme.Modules.tmulSection a b

/-- The second blowup, for codimension-one Y. The intersection is a scheme-theoretic
pullback, Cartier on both divisors. The hyperplane ideal uses the dual of O(1), that is
O(-1), with evaluation equal to its actual ideal inclusion.
The isomorphism to Bl_Z Y is over Y.
Source: ILO XVI, proof of Theorem 2.3.2, pp. 236--237
(blueprint: lem-per-regular-flag-blowup-geometry). -/
def DivisorBlowup {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (m n : ℕ)
    (S : ConormalSequence i j m n) : Prop :=
  ∃ P : Scheme.{u},
  ∃ p : P ⟶ Z,
  ∃ exceptional : P ⟶ (i ≫ j).ker.blowup,
  ∃ cartesian : IsPullback p exceptional (i ≫ j) (i ≫ j).ker.blowupMap,
  IsClosedImmersion exceptional ∧
  exceptional.ker.IsInvertible ∧
  ∃ quotient : (Scheme.Modules.tensorPullback p).obj (conormal (i ≫ j)) ⟶ conormal exceptional,
  IsConormalMap exceptional (i ≫ j) (i ≫ j).ker.blowupMap p
    cartesian.w.symm quotient ∧
  ∃ tautological : ProjectiveBundleQuotientGeometry.TautologicalQuotient (conormal (i ≫ j)),
  ∃ projective : P ≅ (SymmetricAlgebraSheaf.gradedAlgebraData (conormal (i ≫ j))).relProj,
  ProjectiveBundleQuotientGeometry.Classifies
    tautological p (conormal exceptional) quotient projective.hom ∧
  (strictTransformMap j (i ≫ j).ker.blowupMap
    (i ≫ j).ker.support.compl).ker.IsInvertible ∧
  ∃ strictBlowup : strictTransform j (i ≫ j).ker.blowupMap (i ≫ j).ker.support.compl ≅ i.ker.blowup,
  strictBlowup.hom ≫ i.ker.blowupMap =
    strictTransformι j (i ≫ j).ker.blowupMap (i ≫ j).ker.support.compl ≫
      pullback.fst j (i ≫ j).ker.blowupMap ∧
  ∃ Q : Scheme.{u},
  ∃ toP : Q ⟶ P,
  ∃ toStrict : Q ⟶ strictTransform j (i ≫ j).ker.blowupMap (i ≫ j).ker.support.compl,
  ∃ _intersection : IsPullback toP toStrict exceptional
    (strictTransformMap j (i ≫ j).ker.blowupMap (i ≫ j).ker.support.compl),
  toP.ker.IsInvertible ∧
  toStrict.ker.IsInvertible ∧
  ∃ intersectionProjective : Q ≅ (SymmetricAlgebraSheaf.gradedAlgebraData (conormal i)).relProj,
  intersectionProjective.hom ≫
    (SymmetricAlgebraSheaf.gradedAlgebraData (conormal i)).relProjHom = toP ≫ p ∧
  ∃ factorization : (Scheme.Modules.tensorPullback (i ≫ j).ker.blowupMap).obj j.ker.toModules ≅
    exceptional.ker.toModules ⊗
      (strictTransformMap j (i ≫ j).ker.blowupMap (i ≫ j).ker.support.compl).ker.toModules,
  IsIdealProduct (i ≫ j).ker.blowupMap j.ker exceptional.ker
    (strictTransformMap j (i ≫ j).ker.blowupMap (i ≫ j).ker.support.compl).ker factorization ∧
  ∃ hyperplane : toP.ker.toModules ≅
    (Scheme.Modules.tensorPullback p).obj
        ((Scheme.Modules.tensorPullback i).obj (conormal j)) ⊗
      SheafOfModules.homObj.{u, u, u, u} (conormal exceptional)
        (SheafOfModules.unit P.ringCatSheaf),
  ∀ (U : P.Opens)
    (a : Γ((Scheme.Modules.tensorPullback p).obj
      ((Scheme.Modules.tensorPullback i).obj (conormal j)), U))
    (b : Γ(SheafOfModules.homObj.{u, u, u, u} (conormal exceptional)
      (SheafOfModules.unit P.ringCatSheaf), U)),
    toP.ker.toModulesι.app U (hyperplane.inv.app U (Scheme.Modules.tmulSection a b)) =
      PresheafOfModules.homObjEvalId (conormal exceptional).val
        (SheafOfModules.unit P.ringCatSheaf).val U b
        (quotient.app U (((Scheme.Modules.tensorPullback p).map S.inclusion).app U a))

/-- The conormal and blowup assertions, without regularity of the ambient schemes.
Source: ILO XVI, pp. 234--237 (blueprint: lem-per-regular-flag-blowup-geometry).

Proof: For a single immersion choose local regular equations; their classes freely
span I/I² by `lem-weil-pbc-regular-sequence-conormal-free`, including the empty sequence.
For a flag concatenate equations f for Y and lifts g for Z in Y. Their conormal bases
make the natural sequence the inclusion of f followed by projection to g. Localize at a
point, permute regular sequences over the Noetherian local ring, and shrink using
`lem-exc-regular-sequence-principal-neighbourhood` to put each blowup pivot first.
The regular-sequence chart presentation is R[u_l]/(h_k u_l-h_l). Its pivot t=h_k is a
nonzerodivisor since the chart embeds in R_t. Modulo t the chart is (R/(h))[u_l], giving
the canonical exceptional projective bundle and Cartier ideal O(1), with identical
transition fractions. For Bl_Y X, P' is cut out by g on P, and by (t,g) on B.
The conormal quotients send f_k to t, f_l to u_l t, and g_j to g_j. Both kernels have
basis f_l-u_l f_k, l≠k; their inclusion-compatible identification is therefore canonical,
and the conormal of P' in P is the pullback of that of Z in Y.
When n=1, put a=f_1 and blow up (a,g). The strict transform is empty in the a-chart;
in a g_k-chart it is (u), u=a/g_k. Both t=g_k and u are nonzerodivisors, also after
restriction to the other divisor. The intersection is Proj Sym(N_{Y/Z}). Multiplication
(t) tensor (u) to (a), t tensor u to a, gives the factorization, taking 1 tensor 1 to 1
off the inverse image of Y. Finally the tautological quotient applied to the line
K_0=i^*N_{X/Y}, tensored with O(-1), has image exactly (u), proving the hyperplane ideal
formula with the asserted sign. All formulas commute with changes of frame and chart. -/
theorem regular_flag_blowup_geometry :
    (∀ (V W : Scheme.{u}) [IsNoetherian V] [IsNoetherian W]
      (k : W ⟶ V) [IsClosedImmersion k] (c : ℕ),
      (∀ w : W, ∃ U : V.affineOpens, k w ∈ U.1 ∧
        ∃ f : List Γ(V, U.1), f.length = c ∧
          RingTheory.Sequence.IsRegular Γ(V, U.1) f ∧ Ideal.ofList f = k.ker.ideal U) →
      (conormal k).IsFiniteLocallyFreeOfRank c) ∧
    (∀ (X Y Z : Scheme.{u}) [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
      (i : Z ⟶ Y) (j : Y ⟶ X) (m n : ℕ)
      [IsRegularImmersion m i] [IsRegularImmersion n j],
      0 < m → 0 < n →
      ∃ S : ConormalSequence i j m n, FirstBlowup i j m n S ∧
        (n = 1 → DivisorBlowup i j m n S)) := by
  sorry

end
end AlgebraicGeometry.RegularFlagBlowupGeometry
