/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension
public import Sheaf.AlgebraicGeometry.ConormalGradedAlgebraBasic
public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.AffineConormalSections
public import WeilConjectures.Blowup.Principalization
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Rees
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.RingTheory.RegularSequenceConormal

/-! # Conormal and strict-transform geometry of a regular flag

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVI, proofs of Lemma 2.3.3
and Theorem 2.3.2, printed pp.234--237
(blueprint: lem-per-regular-flag-blowup-geometry).

The auxiliary predicates describe the conclusions, including normalization on ideal sections.
All conormals below are the existing degree-one conormal modules, namely i^* ker(i).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.ProjectiveBundleQuotientGeometry

noncomputable section
namespace AlgebraicGeometry.RegularFlagBlowupGeometry


attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.IdealSheafData.blowup
  SymmetricAlgebraSheaf.gradedAlgebraData



/-- The conormal map of a commutative square, fixed on actual ideal sections. The two
pulled-back sections are compared on every common subopen, so no implicit equality of
opens or choice of an adjunction occurs.
Source: ILO XVI 2.3.3, p.235 (blueprint: lem-per-regular-flag-blowup-geometry). -/
def IsConormalMap {X Z V W : Scheme.{u}} (i : Z ⟶ X) (k : W ⟶ V)
    [IsClosedImmersion i] [IsClosedImmersion k] (a : W ⟶ Z) (b : V ⟶ X)
    (q : (tensorPullback a).obj (ConormalGradedAlgebra.piece i 1) ⟶
      ConormalGradedAlgebra.piece k 1) : Prop :=
  a ≫ i = k ≫ b ∧
  ∀ (U : X.Opens) (s : Γ(i.ker.toModules, U))
    (t : Γ(k.ker.toModules, b ⁻¹ᵁ U)),
    k.ker.toModulesι.app (b ⁻¹ᵁ U) t = b.app U (i.ker.toModulesι.app U s) →
    ∀ (O : W.Opens) (h₁ : O ≤ a ⁻¹ᵁ (i ⁻¹ᵁ U)) (h₂ : O ≤ k ⁻¹ᵁ (b ⁻¹ᵁ U)),
      q.app O (((tensorPullback a).obj (ConormalGradedAlgebra.piece i 1)).presheaf.map
        (homOfLE h₁).op (tensorPullbackSection a (ConormalGradedAlgebra.piece i 1)
          (i ⁻¹ᵁ U) (tensorPullbackSection i i.ker.toModules U s))) =
      (ConormalGradedAlgebra.piece k 1).presheaf.map (homOfLE h₂).op
        (tensorPullbackSection k k.ker.toModules (b ⁻¹ᵁ U) t)

/-- The canonical conormal transitivity sequence, with the identities that define both maps.
This record is conclusion data, not an additional assumption on the flag.
Source: ILO XVI 2.3.3, p.235 (blueprint: lem-per-regular-flag-blowup-geometry). -/
structure ConormalSequence {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] where
  inclusion : (tensorPullback i).obj (ConormalGradedAlgebra.piece j 1) ⟶
    ConormalGradedAlgebra.piece (i ≫ j) 1
  quotient : ConormalGradedAlgebra.piece (i ≫ j) 1 ⟶ ConormalGradedAlgebra.piece i 1
  inclusion_canonical : IsConormalMap j (i ≫ j) i (𝟙 X) inclusion
  quotient_canonical : IsConormalMap (i ≫ j) i (𝟙 Z) j
    ((tensorPullbackSectionId Z).hom.app (ConormalGradedAlgebra.piece (i ≫ j) 1) ≫
      quotient)
  zero : inclusion ≫ quotient = 0
  shortExact : (ShortComplex.mk inclusion quotient zero).ShortExact

/-- A map to an ideal is the actual pullback map when its composite with the ideal
inclusion is the pullback of the original inclusion, followed by the structural unit map.
Source: ILO XVI 2.3.2, p.236 (blueprint: lem-per-regular-flag-blowup-geometry). -/
def IsIdealPullbackMap {X B : Scheme.{u}} (π : B ⟶ X) (I : X.IdealSheafData)
    (J : B.IdealSheafData) (q : (tensorPullback π).obj I.toModules ⟶ J.toModules) : Prop :=
  q ≫ J.toModulesι = (tensorPullback π).map I.toModulesι ≫ tensorPullbackObjUnitToUnit π

/-- The degree-one Rees twist, normalized by every original ideal section on every affine
base chart. These equations specify compatible chart isomorphisms, not merely local ranks.
Source: ILO XVI 2.3.3, p.234; Stacks 0BIQ and 01MN
(blueprint: lem-per-regular-flag-blowup-geometry). -/
def HasReesTwistOne {X : Scheme.{u}} (I : X.IdealSheafData) (L : I.blowup.Modules)
    (q : (tensorPullback I.blowupMap).obj I.toModules ⟶ L) : Prop :=
  ∀ U : X.affineOpens,
    ∃ e : (tensorPullback (I.blowupι U)).obj L ≅ Proj.twist (reesGrading (I.ideal U)) 1,
      ∀ (s : Γ(I.toModules, U.1)) (a : I.ideal U),
        I.toModulesι.app U.1 s = (a : Γ(X, U.1)) →
        ∀ (O : (AffineBlowup (I.ideal U)).Opens)
          (hO : O ≤ I.blowupι U ⁻¹ᵁ (I.blowupMap ⁻¹ᵁ U.1)),
          e.hom.app O (((tensorPullback (I.blowupι U)).obj L).presheaf.map
            (homOfLE hO).op
            (tensorPullbackSection (I.blowupι U) L (I.blowupMap ⁻¹ᵁ U.1)
              (q.app (I.blowupMap ⁻¹ᵁ U.1)
                (tensorPullbackSection I.blowupMap I.toModules U.1 s)))) =
          (Proj.unitToTwist (𝒜 := reesGrading (I.ideal U))
            (reesX_mem (I.ideal U) a a.property)).app O (unitSectionsEquiv O 1)

/-- The section-normalized comparison for a square of pullbacks.
Source: ILO XVI 2.3.3, p.235 (blueprint: lem-per-regular-flag-blowup-geometry). -/
def squarePullbackIso {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) (M : D.Modules) :
    (tensorPullback a).obj ((tensorPullback b).obj M) ≅
      (tensorPullback c).obj ((tensorPullback d).obj M) :=
  ((tensorPullbackSectionComp a b).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (tensorPullback f).obj M) h) ≪≫
      (tensorPullbackSectionComp c d).app M

attribute [local irreducible] ConormalGradedAlgebra.piece
  Scheme.Hom.ker Scheme.IdealSheafData.toModules
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjHom
  Scheme.IdealSheafData.blowupMap

/-- All conclusions for the blowup along Y. The schemes P and P' are specified by their
projective-bundle comparison and cartesian squares. The kernel comparison is fixed by
its composite with the kernel inclusion and the original conormal inclusion.
Source: ILO XVI 2.3.3, pp.234--235
(blueprint: lem-per-regular-flag-blowup-geometry). -/
def AlongMiddle {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (C := Y.Opens) (J := Opens.grothendieckTopology Y)
      (R := Y.ringCatSheaf) (ConormalGradedAlgebra.piece j 1)]
    (m n : ℕ) (S : ConormalSequence i j) : Prop :=
  ∃ P : Scheme.{u},
  ∃ p : P ⟶ Y,
  ∃ projective : P ≅ (SymmetricAlgebraSheaf.gradedAlgebraData
    (ConormalGradedAlgebra.piece j 1)).relProj,
  ∃ projective_over : projective.hom ≫ (SymmetricAlgebraSheaf.gradedAlgebraData
    (ConormalGradedAlgebra.piece j 1)).relProjHom = p,
  ∃ jP : P ⟶ j.ker.blowup,
  ∃ closed : IsClosedImmersion jP,
  ∃ _cartesian : IsPullback jP p j.ker.blowupMap j,
  ∃ _cartier : jP.ker.IsInvertible,
  ∃ twistMap : (tensorPullback j.ker.blowupMap).obj j.ker.toModules ⟶ jP.ker.toModules,
  ∃ _twistMap_canonical : IsIdealPullbackMap j.ker.blowupMap j.ker jP.ker twistMap,
  ∃ _twist : HasReesTwistOne j.ker jP.ker.toModules twistMap,
  ∃ P' : Scheme.{u},
  ∃ iP : P' ⟶ P,
  ∃ p' : P' ⟶ Z,
  ∃ baseChange : IsPullback iP p' p i,
  ∃ regular_iP : IsRegularClosedImmersionWithCodimension iP (fun _ ↦ m),
  ∃ regular_composite : IsRegularClosedImmersionWithCodimension (iP ≫ jP) (fun _ ↦ m + 1),
  ∃ q : (tensorPullback p).obj (ConormalGradedAlgebra.piece j 1) ⟶
    ConormalGradedAlgebra.piece jP 1,
  ∃ _q_canonical : @IsConormalMap X Y j.ker.blowup P j jP inferInstance closed
    p j.ker.blowupMap q,
  ∃ _q_surjective : Epi q,
  ∃ tautological : TautologicalQuotient (ConormalGradedAlgebra.piece j 1),
  ∃ conormalLine : (tensorPullback projective.hom).obj tautological.line ≅
    ConormalGradedAlgebra.piece jP 1,
  ∃ _quotient_normalized : pulledQuotient tautological p projective.hom projective_over ≫
    conormalLine.hom = q,
  ∃ q' : (tensorPullback p').obj (ConormalGradedAlgebra.piece (i ≫ j) 1) ⟶
    ConormalGradedAlgebra.piece (iP ≫ jP) 1,
  ∃ _q'_canonical : @IsConormalMap X Z j.ker.blowup P' (i ≫ j) (iP ≫ jP)
    inferInstance regular_composite.1 p' j.ker.blowupMap q',
  ∃ _q'_surjective : Epi q',
  ∃ K : P.Modules,
  ∃ κ : K ⟶ (tensorPullback p).obj (ConormalGradedAlgebra.piece j 1),
  ∃ κ_zero : κ ≫ q = 0,
  ∃ _kernel_property : IsLimit (KernelFork.ofι κ κ_zero),
  ∃ K' : P'.Modules,
  ∃ κ' : K' ⟶ (tensorPullback p').obj (ConormalGradedAlgebra.piece (i ≫ j) 1),
  ∃ κ'_zero : κ' ≫ q' = 0,
  ∃ _kernel'_property : IsLimit (KernelFork.ofι κ' κ'_zero),
  ∃ _kernel_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 
    (C := P.Opens) (J := Opens.grothendieckTopology P)
    (R := P.ringCatSheaf) K (n - 1),
  ∃ _kernel'_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 
    (C := P'.Opens) (J := Opens.grothendieckTopology P')
    (R := P'.ringCatSheaf) K' (n - 1),
  ∃ kernelIso : (tensorPullback iP).obj K ≅ K',
  ∃ _kernelIso_canonical : kernelIso.hom ≫ κ' =
    (tensorPullback iP).map κ ≫
      (squarePullbackIso iP p p' i baseChange.w (ConormalGradedAlgebra.piece j 1)).hom ≫
        (tensorPullback p').map S.inclusion,
  ∃ baseConormalIso : (tensorPullback p').obj (ConormalGradedAlgebra.piece i 1) ≅
    ConormalGradedAlgebra.piece iP 1,
  @IsConormalMap Y Z P P' i iP inferInstance
    regular_iP.1 p' p baseConormalIso.hom


/-- The codimension-one construction, now blowing up Z in X. The factorization commutes
with the actual ideal embeddings, which includes compatibility with the canonical
trivializations off the inverse image of Y. The inverse of the normalized tautological
line is O(-1); evaluation and the last equation fix the hyperplane ideal canonically.
Source: ILO XVI 2.3.2, pp.236--237
(blueprint: lem-per-regular-flag-blowup-geometry). -/
def AlongSmallest {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (C := Z.Opens) (J := Opens.grothendieckTopology Z)
      (R := Z.ringCatSheaf) (ConormalGradedAlgebra.piece i 1)]
    [SheafOfModules.IsQuasicoherent.{u, u, u}
      (C := Z.Opens) (J := Opens.grothendieckTopology Z)
      (R := Z.ringCatSheaf) (ConormalGradedAlgebra.piece (i ≫ j) 1)]
    (S : ConormalSequence i j) : Prop :=
  ∃ P : Scheme.{u},
  ∃ p : P ⟶ Z,
  ∃ projective : P ≅ (SymmetricAlgebraSheaf.gradedAlgebraData
    (ConormalGradedAlgebra.piece (i ≫ j) 1)).relProj,
  ∃ projective_over : projective.hom ≫ (SymmetricAlgebraSheaf.gradedAlgebraData
    (ConormalGradedAlgebra.piece (i ≫ j) 1)).relProjHom = p,
  ∃ jP : P ⟶ (i ≫ j).ker.blowup,
  ∃ closed : IsClosedImmersion jP,
  ∃ _cartesian : IsPullback jP p (i ≫ j).ker.blowupMap (i ≫ j),
  ∃ _cartier : jP.ker.IsInvertible,
  ∃ twistMap : (tensorPullback (i ≫ j).ker.blowupMap).obj (i ≫ j).ker.toModules ⟶
    jP.ker.toModules,
  ∃ _twistMap_canonical : IsIdealPullbackMap (i ≫ j).ker.blowupMap (i ≫ j).ker
    jP.ker twistMap,
  ∃ _twist : HasReesTwistOne (i ≫ j).ker jP.ker.toModules twistMap,
  ∃ T : Scheme.{u},
  ∃ strictIso : T ≅ strictTransform j (i ≫ j).ker.blowupMap (i ≫ j).ker.support.compl,
  ∃ t : T ⟶ (i ≫ j).ker.blowup,
  ∃ _strictMap : t = strictIso.hom ≫
    strictTransformMap j (i ≫ j).ker.blowupMap (i ≫ j).ker.support.compl,
  ∃ strictBlowupIso : T ≅ i.ker.blowup,
  ∃ _strictBlowup_over : strictBlowupIso.hom ≫ i.ker.blowupMap = strictIso.hom ≫
    strictTransformToSource j (i ≫ j).ker.blowupMap (i ≫ j).ker.support.compl,
  ∃ _strict_closed : IsClosedImmersion t,
  ∃ _strict_cartier : t.ker.IsInvertible,
  ∃ P' : Scheme.{u},
  ∃ kP : P' ⟶ P,
  ∃ kT : P' ⟶ T,
  ∃ _intersection : IsPullback kP kT jP t,
  ∃ intersection_projective : P' ≅ (SymmetricAlgebraSheaf.gradedAlgebraData
    (ConormalGradedAlgebra.piece i 1)).relProj,
  ∃ _intersection_over : intersection_projective.hom ≫ (SymmetricAlgebraSheaf.gradedAlgebraData
    (ConormalGradedAlgebra.piece i 1)).relProjHom = kP ≫ p,
  ∃ _transverse_on_P : (t.ker.comap jP).IsInvertible,
  ∃ _transverse_on_T : (jP.ker.comap t).IsInvertible,
  ∃ factor : (tensorPullback (i ≫ j).ker.blowupMap).obj j.ker.toModules ≅
    jP.ker.toModules ⊗ t.ker.toModules,
  ∃ _factor_canonical : factor.hom ≫
    (jP.ker.toModulesι ▷ t.ker.toModules) ≫
      ((𝟙_ ((i ≫ j).ker.blowup.Modules)) ◁ t.ker.toModulesι) ≫
        (λ_ (𝟙_ ((i ≫ j).ker.blowup.Modules))).hom =
    (tensorPullback (i ≫ j).ker.blowupMap).map j.ker.toModulesι ≫
      tensorPullbackObjUnitToUnit (i ≫ j).ker.blowupMap,
  ∃ _factor_invertible :
    ((tensorPullback (i ≫ j).ker.blowupMap).obj j.ker.toModules).IsInvertible,
  ∃ _exceptional_invertible : jP.ker.toModules.IsInvertible,
  ∃ _strict_invertible : t.ker.toModules.IsInvertible,
  ∃ _K0_line : ((tensorPullback i).obj (ConormalGradedAlgebra.piece j 1)).IsInvertible,
  ∃ tautological : TautologicalQuotient (ConormalGradedAlgebra.piece (i ≫ j) 1),
  ∃ line : P.Modules,
  ∃ lineIso : (tensorPullback projective.hom).obj tautological.line ≅ line,
  ∃ quotient : (tensorPullback p).obj (ConormalGradedAlgebra.piece (i ≫ j) 1) ⟶ line,
  ∃ _quotient_canonical : pulledQuotient tautological p projective.hom projective_over ≫
    lineIso.hom = quotient,
  ∃ conormalLine : line ≅ ConormalGradedAlgebra.piece jP 1,
  ∃ _exceptional_quotient_canonical :
    @IsConormalMap X Z (i ≫ j).ker.blowup P (i ≫ j) jP inferInstance closed
      p (i ≫ j).ker.blowupMap (quotient ≫ conormalLine.hom),
  ∃ minusOne : P.Modules,
  ∃ evaluation : line ⊗ minusOne ≅ 𝟙_ P.Modules,
  ∃ hyperplane :
    ((tensorPullback p).obj ((tensorPullback i).obj (ConormalGradedAlgebra.piece j 1))) ⊗
      minusOne ≅ kP.ker.toModules,
  hyperplane.hom ≫ kP.ker.toModulesι =
    (((tensorPullback p).map S.inclusion ≫ quotient) ▷ minusOne) ≫ evaluation.hom


attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

private theorem affine_conormal_coordinates {V W : Scheme.{u}}
    (k : W ⟶ V) [IsClosedImmersion k] (U : V.affineOpens) (c : ℕ)
    (f : Fin c → Γ(V, U.1))
    (hreg : RingTheory.Sequence.IsRegular Γ(V, U.1) (List.ofFn f))
    (hI : Ideal.span (Set.range f) = RingHom.ker (k.app U.1).hom) :
    Nonempty (Γ(ConormalGradedAlgebra.piece k 1, k ⁻¹ᵁ U.1) ≃ₗ[Γ(W, k ⁻¹ᵁ U.1)]
      (Fin c →₀ Γ(W, k ⁻¹ᵁ U.1))) := by
  classical
  have hpiece : ConormalGradedAlgebra.piece k 1 =
      (tensorPullback k).obj k.ker.toModules := by
    simp only [ConormalGradedAlgebra.piece, ConormalGradedAlgebra.power,
      Scheme.idealSheafPower]
  rw [hpiece]
  let A := Γ(V, U.1)
  let B := Γ(W, k ⁻¹ᵁ U.1)
  let J := RingHom.ker (k.app U.1).hom
  have hf := (RingTheory.Sequence.regularSequence_conormal_free A c f hreg).2.2
  rw [hI] at hf
  obtain ⟨b⟩ := hf
  obtain ⟨e₀, _⟩ := (affine_conormal_sections.{u, u} k).2 U A (RingEquiv.refl A) J
    (by simp [J])
  let T := Γ((tensorPullback k).obj k.ker.toModules, k ⁻¹ᵁ U.1)
  let : Module A T := Module.compHom T (k.app U.1).hom
  let e : J.Cotangent ≃ₗ[A] T := e₀
  let q : A ⧸ J ≃+* B :=
    RingHom.quotientKerEquivOfSurjective (k.app_surjective U.1 U.2)
  let d : Γ((tensorPullback k).obj k.ker.toModules, k ⁻¹ᵁ U.1) ≃+ (Fin c →₀ B) :=
    e.symm.toAddEquiv.trans (b.toAddEquiv.trans (Finsupp.mapRange.addEquiv q.toAddEquiv))
  refine ⟨{ d with map_smul' := ?_ }⟩
  intro r x
  -- Surjectivity upgrades the affine coordinates from A-linearity to B-linearity.
  obtain ⟨a, rfl⟩ := k.app_surjective U.1 U.2 r
  have he : e.symm ((k.app U.1) a • x) = a • e.symm x := e.symm.map_smul a x
  have hb (z : J.Cotangent) : b (a • z) = (Ideal.Quotient.mk J a) • b z := by
    rw [← IsScalarTower.algebraMap_smul (A ⧸ J) a z]
    exact b.map_smul _ _
  change Finsupp.mapRange q.toAddEquiv q.toAddEquiv.map_zero
    (b (e.symm ((k.app U.1) a • x))) = _
  rw [he, hb]
  ext t
  simp [d, q]
  rfl

private theorem affine_conormal_frame {V W : Scheme.{u}}
    (k : W ⟶ V) [IsClosedImmersion k] (U : V.affineOpens) (c : ℕ)
    (a : List Γ(V, U.1)) (ha : a.length = c)
    (hreg : RingTheory.Sequence.IsRegular Γ(V, U.1) a)
    (hI : Ideal.ofList a = RingHom.ker (k.app U.1).hom) :
    Nonempty ((ConormalGradedAlgebra.piece k 1).restrict (U.2.preimage k).fromSpec ≅
      SheafOfModules.free (ULift.{u} (Fin c))) := by
  classical
  let M := ConormalGradedAlgebra.piece k 1
  have : M.IsQuasicoherent := by
    simpa only [M, ConormalGradedAlgebra.piece, ConormalGradedAlgebra.power,
      Scheme.idealSheafPower] using (affine_conormal_sections.{u, u} k).1
  have hspan : Ideal.span (Set.range a.get) = Ideal.ofList a := by
    calc
      _ = Ideal.ofList (List.ofFn a.get) :=
        (congrArg Ideal.span (Set.ext (List.mem_ofFn' a.get))).symm
      _ = _ := by rw [List.ofFn_get]
  obtain ⟨e⟩ := affine_conormal_coordinates k U a.length a.get
    (by simpa only [List.ofFn_get] using hreg) (hspan.trans hI)
  rw [ha] at e
  let N := M.restrict (U.2.preimage k).fromSpec
  have : N.IsQuasicoherent := isQuasicoherent_restrictFunctor _ M
  let d := (sectionsRestrictFromSpecLinearEquiv M (U.2.preimage k)).trans e |>.trans
    (Finsupp.domLCongr (R := Γ(W, k ⁻¹ᵁ U.1)) Equiv.ulift.symm)
  exact ⟨(asIso N.fromTildeΓ).symm ≪≫
    (tilde.functor Γ(W, k ⁻¹ᵁ U.1)).mapIso d.toModuleIso ≪≫ tildeFinsupp _⟩

/-- A regular closed immersion of Noetherian schemes has conormal of its constant
codimension, including codimension zero and the empty scheme.
Source: ILO XVI 2.3.1--2.3.3, pp.233--235; Stacks 00LN and 01R3
(blueprint: lem-per-regular-flag-blowup-geometry).

Proof: Work on an affine neighbourhood of each source point with c regular equations.
By lem-weil-pbc-regular-sequence-conormal-free their classes form a basis of I/I^2.
The canonical identification of lem-weil-pbc-affine-conormal-sections sends these classes
to the actual pulled-back ideal sections. Sheafifying this basis gives a free frame
on the inverse-image open. These opens cover the source and prove finite local freeness
of rank c (def-amb-finite-locally-free-module). For c=0 the equations generate the zero
ideal near the source and the conormal is zero. For an empty source the local condition
and the conclusion are both vacuous. -/
theorem regular_immersion_conormal_rank {V W : Scheme.{u}} [IsNoetherian V]
    [IsNoetherian W] (k : W ⟶ V) (c : ℕ)
    (hk : IsRegularClosedImmersionWithCodimension k (fun _ ↦ c)) :
    (ConormalGradedAlgebra.piece k 1).IsFiniteLocallyFreeOfRank c := by
  classical
  let : IsClosedImmersion k := hk.1
  choose U hx a ha hreg hI using hk.2
  refine isFiniteLocallyFreeOfRank_of_restrict_iso_free
    (ConormalGradedAlgebra.piece k 1)
    (fun x : W ↦ ((U x).2.preimage k).fromSpec) ?_ fun x ↦
      affine_conormal_frame k (U x) c (a x) (ha x) (hreg x) (hI x)
  simp only [IsAffineOpen.opensRange_fromSpec]
  apply eq_top_iff.mpr
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩

/-- The full conormal, excess-kernel and strict-transform geometry for a regular flag.
The first construction blows up Y; the second, when n=1, blows up Z. Both predicates are
conclusions for the actual blowups and normalized projective bundles.
Source: ILO XVI, proof of Lemma 2.3.3, pp.234--235, and proof of Theorem 2.3.2,
pp.236--237 (blueprint: lem-per-regular-flag-blowup-geometry).

Proof, following the node's nine steps:
1. Localize at a point of the center. Localization commutes with ideal powers, Rees
algebras, their degree-zero charts and conormals. Choose regular equations f for Y
and lifts g of regular equations for Z in Y. Their concatenation is regular. In the
Noetherian local ring, lem-weil-pbc-regular-sequence-permutation-noetherian-local
allows any f or g to be placed first; outside the center a unit gives the identity chart.
2. Apply lem-weil-pbc-affine-conormal-sections and
lem-weil-pbc-regular-sequence-conormal-free. The conormals have bases f, g, and (f,g).
The first n basis vectors include and the last m project, giving the canonical short
exact sequence and ranks n, m and m+n, and regularity of the composite.
3. The charts of a positive-codimension regular blowup are R[I/h_a], presented by
h_a u_i-h_i (lem-trf-blowup-chart-regular-sequence-presentation and
prop-nagata-affine-blowup-chart-cover). They embed in R localized at h_a, so h_a is
a nonzerodivisor. The extended ideal is (h_a), and its quotient is the polynomial
ring over R/I. The regular-sequence graded-polynomial theorem identifies the
exceptional divisor with P(I/I^2). On overlaps h_a=(h_a/h_b)h_b, giving the normalized
Rees twist O(1) and its equation on each original ideal section.
4. On an f_a-chart, P' has equations (f_a,g). Modulo f_a the g remain regular in the
polynomial ring over R/I_Y. This proves codimensions m and m+1. Their conormal bases
give the canonical base-change identification with the pullback of N_{Y/Z}.
5. The first conormal surjection sends f_i to u_i[f_a]. Its kernel has basis
e_i-u_i e_a for i different from a. The second sends f_i to u_i[f_a] and g_b to [g_b],
so has exactly the same kernel basis with zero g-coordinates. These prove both
surjections, rank n-1 and the kernel isomorphism. The local comparisons glue because
the maps come from the actual ideals. For n=1 both kernels are zero.
6. For n=1 blow up J=(f,g). On a g_b-chart, set a=g_b and t=f/a. Its presentation is
R[t,u_l]/(at-f,au_l-g_l). Modulo t it is the corresponding chart of Bl_Z Y,
embedded in (R/(f)) localized at a. Thus a is a nonzerodivisor modulo t. Since f is
a nonzerodivisor in the chart and f=at, t is also a nonzerodivisor there.
7. The strict-transform saturation is (at):a^infinity=(t), by that injectivity
modulo t. On the f-chart the strict transform is empty. The remaining charts and
their fraction transition maps glue to Bl_Z Y, an effective Cartier divisor.
8. Modulo a the chart is (R/J)[t,u_l], and modulo (a,t) it is (R/J)[u_l]. Thus each
divisor cuts an effective Cartier divisor on the other, and their intersection is
P(N_{Y/Z}). Multiplication (a)(t)=(f), and (f)(1)=(f) on the f-chart, glues to the
ideal factorization. It commutes with the embeddings in O_B, so sends 1 tensor 1 to
1 off the inverse image of Y and respects the stipulated trivializations.
9. The conormal sequence 0 to K0 to F to E to 0 has line kernel when n=1. Locally
split it by lifting a basis of E. The tautological quotient on P(F), composed with
K0 to F, has zero scheme P(E): its equation is T_f/T_g=t on the g-charts and a
unit on the f-chart. Tensoring by O(-1) gives the ideal map. Its injectivity follows
from step 8. Since the inclusion and quotient are canonical, these maps glue and
give the hyperplane ideal p^*K0 tensor O(-1), with the stated sign. -/
theorem regular_flag_blowup_geometry {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (i : Z ⟶ Y) (j : Y ⟶ X) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hi : IsRegularClosedImmersionWithCodimension i (fun _ ↦ m))
    (hj : IsRegularClosedImmersionWithCodimension j (fun _ ↦ n)) :
    IsRegularClosedImmersionWithCodimension (i ≫ j) (fun _ ↦ m + n) ∧
    (ConormalGradedAlgebra.piece i 1).IsFiniteLocallyFreeOfRank m ∧
    (ConormalGradedAlgebra.piece j 1).IsFiniteLocallyFreeOfRank n ∧
    (ConormalGradedAlgebra.piece (i ≫ j) 1).IsFiniteLocallyFreeOfRank (m + n) ∧
    ∃ S : @ConormalSequence X Y Z i j hi.1 hj.1,
      ∃ hqc : SheafOfModules.IsQuasicoherent.{u, u, u}
      (C := Y.Opens) (J := Opens.grothendieckTopology Y)
      (R := Y.ringCatSheaf) (ConormalGradedAlgebra.piece j 1),
        @AlongMiddle X Y Z i j hi.1 hj.1 hqc m n S ∧
        (n = 1 → ∃ hqci : SheafOfModules.IsQuasicoherent.{u, u, u}
      (C := Z.Opens) (J := Opens.grothendieckTopology Z)
      (R := Z.ringCatSheaf) (ConormalGradedAlgebra.piece i 1),
          ∃ hqcij : SheafOfModules.IsQuasicoherent.{u, u, u}
      (C := Z.Opens) (J := Opens.grothendieckTopology Z)
      (R := Z.ringCatSheaf) (ConormalGradedAlgebra.piece (i ≫ j) 1),
            @AlongSmallest X Y Z i j hi.1 hj.1 hqci hqcij S) := by
  sorry

end AlgebraicGeometry.RegularFlagBlowupGeometry
