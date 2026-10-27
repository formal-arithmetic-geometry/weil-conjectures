/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.VaryingDimensionDualizingInverse
import Sheaf.Paper.AllStageCtfPullbackUnit
import Sheaf.Algebra.Homology.CochainTensorModelRigidity
import Sheaf.Paper.CohomologicalSmoothnessComparison
import Sheaf.Paper.FinitePullbackTensorComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The section invariant in intrinsic finite-coefficient coordinates

Source: blueprint master, sec-smooth-purity/sk-def-purity-conv/def-pur-section-invariant.md
(blueprint: def-pur-section-invariant).

This equivalent interface uses the canonical constant-ring realization and the
published finite exceptional functor. It avoids mixing the retired pro-etale
pullback API with the finite-coefficient API. The data remain Ls* Rg! A_B.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/-- The original site fits its object universe, with no extra scalar universe to infer.
Source: small pro-etale site convention (blueprint: def-pur-section-invariant). -/
instance (priority := 2000) intrinsicSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} T.ProEt

/-- Finiteness of the actual positive coefficient quotient, by the published theorem.
Source: finite coefficient convention (blueprint: def-pur-section-invariant). -/
instance intrinsicCoefficientFinite (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The constant coefficient object in degree zero in the recorded intrinsic category.
Source: section-invariant definition, Lambda_B (blueprint: def-pur-section-invariant). -/
def intrinsicCoefficientUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    proEtaleDerivedCategory T P.Ring :=
  (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)

/-- The existing K-flat derived tensor, with independent site and coefficient universes.
Source: section-invariant tensor invertibility (blueprint: def-pur-section-invariant). -/
def intrinsicCoefficientTensor (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  let R := (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} P.Ring))
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
  SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u, u + 1, u + 2}
    (Scheme.ProEt.topology T)
    ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} P.Ring)))

/-- Actual exceptional image of the coefficient unit, using the specified etale adjoint
and the two canonical site comparisons. Source: omega_g in the section-invariant definition
(blueprint: def-pur-section-invariant). -/
def intrinsicDualizing (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] : proEtaleDerivedCategory V P.Ring :=
  (ProEtale.sfFiniteExceptional P.Ring (HasCompactification.compactification g)).obj
    (P.intrinsicCoefficientUnit B)

/-- The actual derived pullback Ls* Rg! A_B, with no choice of an orientation.
Source: section-invariant displayed definition (blueprint: def-pur-section-invariant). -/
def sectionInvariantIntrinsic (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] (s : B ⟶ V) :
    proEtaleDerivedCategory B P.Ring :=
  (Scheme.sfIntrinsicDerivedPullback P.Ring s).obj (P.intrinsicDualizing g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
private def intrinsicTensorComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (n : ℕ) :
    SheafOfModules.siteDerivedTensorIndependentCoefficients
        (Scheme.ProEt.topology T) (integralCoefficientCommRingSheaf l E T n) ≅
      finiteIntrinsicDerivedTensor l E T n := by
  let R := integralCoefficientCommRingSheaf l E T n
  let S := finiteIntrinsicClosed l E T n
  let M := finiteIntrinsicTensorModels l E T n
  let i := ObjectProperty.ιOfLE
    (P := SheafOfModules.cochainTensorFlatRepresentatives (Scheme.ProEt.topology T) R)
    (P' := CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology T) (R := R)) (fun _ h ↦ h.1)
  have h := SheafOfModules.cochain_tensor_model_rigidity.{u + 1, u, u + 1, u + 2, 0, 0}
    (Scheme.ProEt.topology T) R
  exact (h.choose_spec.2.1 S.tensor (Functor.isoWhiskerLeft (i.prod i) M.comparison)).choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
private def intrinsicExceptionalComparison (P : PurityFiniteSetting.{u})
    {V B : Scheme.{u}} [V.Over (Spec (.of P.field.k))] [B.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of P.field.k))]
    [QuasiCompact (B ↘ Spec (.of P.field.k))]
    (g : V ⟶ B) [HasCompactification g] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] :
    ProEtale.sfFiniteExceptional P.Ring (HasCompactification.compactification g) ≅
      Scheme.finiteExceptionalInverseImage P.coefficients.l P.extension P.level P.level_pos
        P.field.k V B g := by
  let F := (sfIntrinsicModuleEquivalence B P.Ring).inverse.mapDerivedCategory
  let H := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} P.Ring))
    B).rightDerivedFunctor
  let G := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1} P.Ring)) g
  exact Functor.isoWhiskerLeft (F ⋙ H ⋙ G)
    (Functor.mapDerivedCategoryCompIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} P.Ring)) V)
      (sfIntrinsicModuleEquivalence V P.Ring).functor).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
private theorem intrinsicGoodIso (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {K L : proEtaleDerivedCategory T P.Ring} (e : K ≅ L)
    (h : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T K) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T L := by
  have hc : intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos T L :=
    (finiteTorsionConstructible P.field P.coefficients.l P.coefficients.different
      P.extension P.level P.level_pos T).prop_of_iso e h.1
  obtain ⟨a, b, hab⟩ := h.2
  refine ⟨hc, a, b, hab.1, ?_⟩
  intro C D hC f hf hD M i hi
  obtain ⟨eC⟩ := hC
  exact hab.2 C D ⟨eC ≪≫ e.symm⟩ f hf hD M i hi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
/-- The invariant is tensor-invertible in the exact recorded finite-Tor category.
Smooth relative dimension may vary; no Tate orientation is supplied.
Source: section-invariant invertibility paragraph (blueprint: def-pur-section-invariant).
Proof: split the finite-type smooth source into its finitely many clopen relative-dimension
loci and use thm-pur-cohomological-smoothness on each. Reassemble the relative dualizing
object and its inverse along this finite partition. Derived inverse image preserves the
coefficient unit and tensor product. Pulling the two inverse isomorphisms along the section
gives the asserted two-sided inverse. Bounded constructibility and a uniform finite Tor
interval descend from the finite partition and are preserved by inverse image. The
canonical coefficient realization identifies precisely finiteTorConstructible, including
empty schemes and the dimension-zero identity section. -/
theorem sectionInvariantIntrinsic_invertible (P : PurityFiniteSetting.{u})
    {V B : Scheme.{u}} (g : V ⟶ B) [HasCompactification g] [Smooth g]
    [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos B
        (P.sectionInvariantIntrinsic g s) ∧
      ∃ Q : proEtaleDerivedCategory B P.Ring,
        finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos B Q ∧
        Nonempty ((P.intrinsicCoefficientTensor B).obj
          (P.sectionInvariantIntrinsic g s, Q) ≅ P.intrinsicCoefficientUnit B) ∧
        Nonempty ((P.intrinsicCoefficientTensor B).obj
          (Q, P.sectionInvariantIntrinsic g s) ≅ P.intrinsicCoefficientUnit B) := by
  classical
  rcases P with ⟨field, coefficients, extension, level, level_pos⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt level_pos)
  let P : PurityFiniteSetting.{u} :=
    ⟨field, coefficients, extension, n + 1, level_pos⟩
  let : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  let : V.Over (Spec (.of P.field.k)) := ⟨g ≫ aB⟩
  let VB : Over (Spec (.of P.field.k)) := Over.mk aB
  let VV : Over (Spec (.of P.field.k)) := Over.mk (g ≫ aB)
  have : LocallyOfFiniteType g := inferInstance
  have : LocallyOfFiniteType (VV.left ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (g ≫ aB))
  have : QuasiCompact (VV.left ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (g ≫ aB))
  have : LocallyOfFiniteType (VB.left ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  have : QuasiCompact (VB.left ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact aB)
  have : g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  obtain ⟨U, hU, hfinite, hclosed, hdisjoint, hcover, hproperties⟩ :=
    P.smooth_dimension_clopen_partition VV VB g
  let I := {d : ℕ // (U d : Set VV.left).Nonempty}
  have : Finite I := hfinite
  let Vi : I → Over (Spec (.of P.field.k)) :=
    fun d ↦ Over.mk ((U d.val).ι ≫ (g ≫ aB))
  let j : ∀ d, Vi d ⟶ VV := fun d ↦ Over.homMk (U d.val).ι rfl
  have : ∀ d, LocallyOfFiniteType (Vi d).hom := fun d ↦ (hproperties d.val).2.2.2.2.1
  have : ∀ d, QuasiCompact (Vi d).hom := fun d ↦ (hproperties d.val).2.2.2.2.2
  have : ∀ d, LocallyOfFiniteType ((Vi d).left ↘ Spec (.of P.field.k)) :=
    fun d ↦ (hproperties d.val).2.2.2.2.1
  have : ∀ d, QuasiCompact ((Vi d).left ↘ Spec (.of P.field.k)) :=
    fun d ↦ (hproperties d.val).2.2.2.2.2
  have : ∀ d, IsOpenImmersion (j d).left :=
    fun d ↦ inferInstanceAs (IsOpenImmersion (U d.val).ι)
  have : ∀ d, IsClosedImmersion (j d).left := by
    intro d
    apply IsClosedImmersion.of_isPreimmersion
    change IsClosed (Set.range (U d.val).ι)
    simpa only [Scheme.Opens.range_ι] using hclosed d.val
  have hjdisjoint : ∀ d e : I, d ≠ e →
      Disjoint (Set.range (j d).left) (Set.range (j e).left) := by
    intro d e hde
    change Disjoint (Set.range (U d.val).ι) (Set.range (U e.val).ι)
    simpa only [Scheme.Opens.range_ι] using
      hdisjoint d.val e.val (fun h ↦ hde (Subtype.ext h))
  have hjcover : (⋃ d : I, Set.range (j d).left) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨⟨d, x, hd⟩, (Scheme.Opens.range_ι (U d)).symm ▸ hd⟩
  have hdim (d : I) := (Scheme.Opens.range_ι (U d.val)).trans (hU d.val)
  have hinverse := P.varyingDimension_finite_dualizing_inverse VV VB g Vi j
    hjdisjoint hjcover (fun d ↦ d.val) Subtype.val_injective
    (fun d ↦ ⟨⟨d.property.choose, d.property.choose_spec⟩⟩) hdim n
  have hω := hinverse.2.1.1
  obtain ⟨Q, hQ, ⟨e₁⟩, ⟨e₂⟩⟩ := hinverse.2.1.2.2.1
  let ω := (clopenFiniteExceptional P P.extension VV VB g n).obj
    (finiteConstantCoefficientObject P.coefficients.l P.extension B n)
  have : LocallyOfFiniteType (V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (g ≫ aB))
  have : QuasiCompact (V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (g ≫ aB))
  have : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  have : QuasiCompact (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact aB)
  have : LocallyOfFiniteType VV.hom := inferInstanceAs (LocallyOfFiniteType (g ≫ aB))
  have : QuasiCompact VV.hom := inferInstanceAs (QuasiCompact (g ≫ aB))
  have : LocallyOfFiniteType VB.hom := inferInstanceAs (LocallyOfFiniteType aB)
  have : QuasiCompact VB.hom := inferInstanceAs (QuasiCompact aB)
  let eω : P.intrinsicDualizing g ≅ ω :=
    (intrinsicExceptionalComparison P g).app (P.intrinsicCoefficientUnit B)
  let sf : VB ⟶ VV := Over.homMk s (by
    change s ≫ (g ≫ aB) = aB
    rw [← Category.assoc, hs, Category.id_comp])
  have : IsSeparated sf.left := inferInstanceAs (IsSeparated s)
  have : LocallyOfFiniteType sf.left := inferInstanceAs (LocallyOfFiniteType s)
  have : QuasiCompact sf.left := inferInstanceAs (QuasiCompact s)
  have hgood := (AllStageCtfPullback.preserves_ctf_and_unit P VB VV sf).2.1 n
  let F := finiteDerivedPullback P.coefficients.l P.extension n s
  let eunit := ConstantGeometricStalkUnit.finiteUnit P.coefficients.l P.extension s n
  let C := F.obj ω
  let C' := F.obj Q
  have hC := hgood ω hω
  have hC' := hgood Q hQ
  let epull : P.sectionInvariantIntrinsic g s ≅ C := F.mapIso eω
  let := fun x : B ↦ AllStageCtfPullback.residueInvertible P B x
  let := fun x : V ↦ AllStageCtfPullback.residueInvertible P V x
  let mu := canonicalFinitePullbackTensor P.coefficients.l P.extension s n
  let t := intrinsicTensorComparison P.coefficients.l P.extension B n
  refine ⟨intrinsicGoodIso P B epull.symm hC, C', hC', ⟨?_⟩, ⟨?_⟩⟩
  · exact (P.intrinsicCoefficientTensor B).mapIso (Iso.prod epull (Iso.refl C')) ≪≫
      t.app (C, C') ≪≫ (mu ω Q).symm ≪≫ F.mapIso e₁ ≪≫ eunit
  · exact (P.intrinsicCoefficientTensor B).mapIso (Iso.prod (Iso.refl C') epull) ≪≫
      t.app (C', C) ≪≫ (mu Q ω).symm ≪≫ F.mapIso e₂ ≪≫ eunit

/-- Nagata supplies the compactification from the source hypotheses, with no added
exceptional-adjoint condition. Source: section-invariant finite-type setting
(blueprint: def-pur-section-invariant).
Proof: B is Noetherian since it is finite type over a field. The separated finite-type
map g therefore admits a compactification by Nagata. Smoothness in particular supplies
local finite type; quasi-compactness supplies finite type. -/
theorem sectionCompactifiable (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    HasCompactification g := by
  exact (P.comparedCompactification g aB).hasCompactification

/-- The section invariant on precisely the finite-type domain of the source.
Compactifiability is a consequence, rather than an additional assumption.
Source: displayed definition C(g,s) (blueprint: def-pur-section-invariant). -/
def sectionInvariantFinite (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    proEtaleDerivedCategory B P.Ring :=
  let _ := hs
  letI := P.sectionCompactifiable g aB
  P.sectionInvariantIntrinsic g s

/-- Tensor invertibility with all auxiliary admissibility hypotheses discharged.
Source: section-invariant Picard assertion (blueprint: def-pur-section-invariant).
Proof: use sectionCompactifiable and sectionInvariantIntrinsic_invertible. Their
coefficient objects and pullback are exactly the definition sectionInvariantFinite,
so the same finite-Tor inverse and its two tensor isomorphisms give the result. -/
theorem sectionInvariantFinite_invertible (P : PurityFiniteSetting.{u})
    {V B : Scheme.{u}} (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos B
        (P.sectionInvariantFinite g aB s hs) ∧
      ∃ Q : proEtaleDerivedCategory B P.Ring,
        finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos B Q ∧
        Nonempty ((P.intrinsicCoefficientTensor B).obj
          (P.sectionInvariantFinite g aB s hs, Q) ≅ P.intrinsicCoefficientUnit B) ∧
        Nonempty ((P.intrinsicCoefficientTensor B).obj
          (Q, P.sectionInvariantFinite g aB s hs) ≅ P.intrinsicCoefficientUnit B) := by
  let := P.sectionCompactifiable g aB
  exact P.sectionInvariantIntrinsic_invertible g aB s hs

end WeilConjectures.PurityFiniteSetting
