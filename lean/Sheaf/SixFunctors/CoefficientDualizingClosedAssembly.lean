module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.FiniteCoefficientDirectImage
import all Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.Paper.EtaleCompactSupportCoefficientChange
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.Paper.ExceptionalCoefficientMaps
public import Mathlib.AlgebraicGeometry.AffineSpace
import Sheaf.Paper.EtaleCompactScalarCoherence
import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension

/-! # Assembly of the closed dualizing coefficient comparison

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md, paragraph 3, sentences 2--3
(blueprint: lem-coef-dualizing-closed-assembly).

The assertion is written under the stipulated counit-compatible structural
identifications: the Y adjunction is literally the composite of closed direct
image and affine-space compact support. Right adjoints and their adjunctions
are quantified, so the assertion applies to every counit-compatible presentation.
All left functors, scalar functors and coefficient components are the recorded
ordinary small-etale constructions, not arbitrary comparison data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The closed assembly assertion under the structural identifications of the node.
The local names abbreviate actual functors and arrows, and introduce no new data.
In particular cY is the normalized composite h followed by F_B(d), not a separately
chosen isomorphism. Its invertibility, and that of d and t, are conclusions before
any inverse is taken. No invertibility is requested for h at the intermediate i_*N.

Source: main-20261015, lem-coef-finite-dualizing.proof.md, paragraph 3
(blueprint: lem-coef-dualizing-closed-assembly). -/
def CoefficientDualizingClosedAssembly
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Y P S : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ S) (c : Compactification p) : Prop :=
  let FA := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let FB := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
  let JA := Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i
  let JB := Etale.rightDerivedLowerStar (ModuleCat.{u + 1} B) i
  let T := fun W : Scheme.{u} ↦ Etale.scalarExtension φ W
  let oneA := Etale.constantComplex A S
  let oneB := Etale.constantComplex B S
  let unit := (Etale.ExceptionalCoefficients.unitIso φ S).hom
  ∀ (GA : Etale.DerivedCategoryModule A S ⥤ Etale.DerivedCategoryModule A P)
    (GB : Etale.DerivedCategoryModule B S ⥤ Etale.DerivedCategoryModule B P)
    (adjPA : FA ⊣ GA) (adjPB : FB ⊣ GB)
    (IA : Etale.DerivedCategoryModule A P ⥤ Etale.DerivedCategoryModule A Y)
    (IB : Etale.DerivedCategoryModule B P ⥤ Etale.DerivedCategoryModule B Y)
    (adjIA : JA ⊣ IA) (adjIB : JB ⊣ IB),
  let M := GA.obj oneA
  let N := IA.obj M
  let MB := GB.obj oneB
  let NB := IB.obj MB
  let epsPA := adjPA.counit.app oneA
  let epsPB := adjPB.counit.app oneB
  let adjYA := adjIA.comp adjPA
  let adjYB := adjIB.comp adjPB
  let epsYA := adjYA.counit.app oneA
  let epsYB := adjYB.counit.app oneB
  let d := Etale.finiteCoefficientDirectImageMap φ i N
  let h := Etale.ExceptionalCoefficients.compactSupportMap φ c (JA.obj N)
  let t := Etale.ExceptionalCoefficients.compactSupportMap φ c M
  let cY := h ≫ FB.map d
  Etale.DerivedCategory.isBoundedConstructible A P M →
  (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A P a b M) →
  Etale.DerivedCategory.isBoundedConstructible A Y N →
  (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A Y a b N) →
  Etale.DerivedCategory.isBoundedConstructible B P MB →
  (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn B P a b MB) →
  Etale.DerivedCategory.isBoundedConstructible B Y NB →
  (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn B Y a b NB) →
  ∃ hd : IsIso d, ∃ ht : IsIso t, ∃ hcY : IsIso cY,
    ∀ (uP : (T P).obj M ⟶ MB), IsIso uP →
      FB.map uP ≫ epsPB = @inv _ _ _ _ t ht ≫ (T S).map epsPA ≫ unit →
    ∀ (b : (T Y).obj N ⟶ IB.obj ((T P).obj M)), IsIso b →
      JB.map b ≫ adjIB.counit.app ((T P).obj M) =
        @inv _ _ _ _ d hd ≫ (T P).map (adjIA.counit.app M) →
    let uY := adjYB.homEquiv ((T Y).obj N) oneB
      (@inv _ _ _ _ cY hcY ≫ (T S).map epsYA ≫ unit)
    uY = b ≫ IB.map uP ∧ IsIso uY ∧
      cY ≫ (JB ⋙ FB).map (b ≫ IB.map uP) ≫ epsYB = (T S).map epsYA ≫ unit

private theorem closedAssembly_counit
    {YA PA SA YB PB SB : Type*}
    [Category YA] [Category PA] [Category SA]
    [Category YB] [Category PB] [Category SB]
    {FA : PA ⥤ SA} {FB : PB ⥤ SB} {JA : YA ⥤ PA} {JB : YB ⥤ PB}
    {GA : SA ⥤ PA} {GB : SB ⥤ PB} {IA : PA ⥤ YA} {IB : PB ⥤ YB}
    (adjPA : FA ⊣ GA) (adjPB : FB ⊣ GB)
    (adjIA : JA ⊣ IA) (adjIB : JB ⊣ IB)
    (TY : YA ⥤ YB) (TP : PA ⥤ PB) (TS : SA ⥤ SB)
    (h : FA ⋙ TS ⟶ TP ⋙ FB) (oneA : SA) (oneB : SB)
    (unit : TS.obj oneA ⟶ oneB)
    (d : TP.obj (JA.obj (IA.obj (GA.obj oneA))) ⟶
      JB.obj (TY.obj (IA.obj (GA.obj oneA)))) [IsIso d]
    [IsIso (h.app (GA.obj oneA))]
    (uP : TP.obj (GA.obj oneA) ⟶ GB.obj oneB)
    (hP : FB.map uP ≫ adjPB.counit.app oneB =
      inv (h.app (GA.obj oneA)) ≫ TS.map (adjPA.counit.app oneA) ≫ unit)
    (b : TY.obj (IA.obj (GA.obj oneA)) ⟶ IB.obj (TP.obj (GA.obj oneA)))
    (hb : JB.map b ≫ adjIB.counit.app (TP.obj (GA.obj oneA)) =
      inv d ≫ TP.map (adjIA.counit.app (GA.obj oneA))) :
    (h.app (JA.obj (IA.obj (GA.obj oneA))) ≫ FB.map d) ≫
        (JB ⋙ FB).map (b ≫ IB.map uP) ≫ (adjIB.comp adjPB).counit.app oneB =
      TS.map ((adjIA.comp adjPA).counit.app oneA) ≫ unit := by
  have he := adjIB.counit.naturality uP
  dsimp only [Functor.comp_map, Functor.id_map] at he
  simp only [Functor.comp_map, Functor.map_comp, Adjunction.comp_counit_app,
    Category.assoc]
  rw [← FB.map_comp_assoc (JB.map (IB.map uP)) (adjIB.counit.app (GB.obj oneB)),
    he, FB.map_comp]
  simp only [Category.assoc]
  rw [← FB.map_comp_assoc (JB.map b) (adjIB.counit.app (TP.obj (GA.obj oneA))),
    hb, FB.map_comp]
  simp only [Category.assoc]
  rw [← FB.map_comp_assoc d (inv d), IsIso.hom_inv_id, FB.map_id, Category.id_comp]
  have hn := h.naturality (adjIA.counit.app (GA.obj oneA))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [← Category.assoc (h.app (JA.obj (IA.obj (GA.obj oneA))))
    (FB.map (TP.map (adjIA.counit.app (GA.obj oneA))))]
  rw [← hn]
  simp only [Category.assoc]
  rw [hP]
  simp only [IsIso.hom_inv_id_assoc]

private theorem closedAssembly_of_noetherian
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Y P S : Scheme.{u}}
    [IsNoetherian Y] [IsNoetherian P] [IsNoetherian S]
    (i : Y ⟶ P) [IsClosedImmersion i] (p : P ⟶ S)
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] (c : Compactification p) :
    CoefficientDualizingClosedAssembly φ i p c := by
  dsimp only [CoefficientDualizingClosedAssembly]
  intro GA GB adjPA adjPB IA IB adjIA adjIB _ _ _ _ _ _ _ _
  let M := GA.obj (Etale.constantComplex A S)
  let N := IA.obj M
  let FB := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
  let d := Etale.finiteCoefficientDirectImageMap φ i N
  let t := Etale.ExceptionalCoefficients.compactSupportMap φ c M
  let h := Etale.ExceptionalCoefficients.compactSupportMap φ c
    ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) i).obj N)
  let cY := h ≫ FB.map d
  have hd : IsIso d := by
    dsimp only [d]
    rw [Etale.finiteCoefficientDirectImageMap_eq_mate]
    change IsIso ((Etale.scalarMate φ i).app N)
    exact (Etale.properFiniteCoefficientExtension φ i).1 N
  have ht : IsIso t := (Etale.etaleCompactScalarCoherence φ p c).1 M
  have hh : IsIso h := (Etale.etaleCompactScalarCoherence φ p c).1 _
  have hcY : IsIso cY := by dsimp only [cY]; infer_instance
  have : IsIso ((Etale.compactScalarMap φ c).app (GA.obj (Etale.constantComplex A S))) :=
    ht
  refine ⟨hd, ht, hcY, ?_⟩
  intro uP huP hP b hb hClosed
  have : IsIso uP := huP
  have : IsIso b := hb
  let v := b ≫ IB.map uP
  have hv := closedAssembly_counit adjPA adjPB adjIA adjIB
    (Etale.scalarExtension φ Y) (Etale.scalarExtension φ P) (Etale.scalarExtension φ S)
    (Etale.compactScalarMap φ c) (Etale.constantComplex A S) (Etale.constantComplex B S)
    (Etale.ExceptionalCoefficients.unitIso φ S).hom d uP hP b hClosed
  change cY ≫
      (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} B) i ⋙ FB).map v ≫
        (adjIB.comp adjPB).counit.app (Etale.constantComplex B S) =
      (Etale.scalarExtension φ S).map
        ((adjIA.comp adjPA).counit.app (Etale.constantComplex A S)) ≫
          (Etale.ExceptionalCoefficients.unitIso φ S).hom at hv
  have heq : (adjIB.comp adjPB).homEquiv
      ((Etale.scalarExtension φ Y).obj N) (Etale.constantComplex B S)
      (inv cY ≫ (Etale.scalarExtension φ S).map
        ((adjIA.comp adjPA).counit.app (Etale.constantComplex A S)) ≫
          (Etale.ExceptionalCoefficients.unitIso φ S).hom) = v := by
    apply ((adjIB.comp adjPB).homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    apply (cancel_epi cY).1
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hv.symm
  refine ⟨heq, ?_, hv⟩
  have : IsIso v := by dsimp only [v]; infer_instance
  exact heq.symm ▸ this

/-- The actual closed coefficient mate followed by I_B(u_P) is the counit-defined
structural dualizing map, and hence is invertible. Positive levels are m+1 ≤ n+1.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md, paragraph 3, sentences 2--3
(blueprint: lem-coef-dualizing-closed-assembly).

Proof:
1. Put N=I_A M, d=c_i,N, h=c_P,i_*N and t=c_P,M. The normalized composition
   identity of lem-sf-compact-coefficient-composition identifies cY with h then
   F_B(d), on the finite-Tor input N. Keep h forward; never invert it.
2. def-weil-pbc-composite-adjunction expresses epsY as F_P(e) followed by epsP.
   Substitute v=b followed by I_B(uP), and expand functorial composition.
3. Naturality of the closed B-counit at uP replaces i_*I_B(uP) followed by eB
   with eB followed by uP. Substitute the assumed closed coefficient-counit
   equation and cancel d inverse against d, only at N.
4. Naturality of the canonical coefficient transformation at eA:i_*N→M
   (lem-sp-et-proet-coefficient-compatibility) moves F_B(T(eA)) across h.
   The resulting factor is t; the defining equation for uP cancels it at M.
   Functoriality and the composite counit give the displayed transpose identity.
5. lem-fix-compact-support-coefficient-change makes cY invertible at N and t
   invertible at M; lem-coef-finite-direct-image makes d invertible at N.
   Cancel cY and apply injectivity of the composite adjunction Hom bijection.
   This identifies v with precisely the displayed definition of uY.
6. The inverse of v is I_B(uP inverse) followed by b inverse. A functor
   preserves inverse equations, so uY is invertible. The empty Y, r=0,
   identity quotient m=n and nonflat B/A require no change to this calculation. -/
theorem coefficientDualizingClosedAssembly
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hmn : m ≤ n) (r : ℕ)
    (Y : Scheme.{u}) [IsAffine Y]
    (aY : Y ⟶ Spec (.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (i : Y ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)))
    [IsClosedImmersion i]
    (_hi : i ≫ AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k) = aY)
    (c : Compactification
      (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k))) :
    @CoefficientDualizingClosedAssembly.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
      inferInstance inferInstance
      (Equiv.ulift.finite_iff.mpr
        (Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)))
      (Equiv.ulift.finite_iff.mpr
        (Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_pos m)))
      (RingHom.ulift.{u + 1, u + 1}
        (Ideal.Quotient.factor
          (S := Padic.coefficientExtensionIdeal l E (n + 1))
          (T := Padic.coefficientExtensionIdeal l E (m + 1))
          (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1))))
      Y (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))) (Spec (.of D.k)) i
      inferInstance
      (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k)) c := by
  have : Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
    Equiv.ulift.finite_iff.mpr
      (Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n))
  have : Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) :=
    Equiv.ulift.finite_iff.mpr
      (Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_pos m))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : IsNoetherian Y := ⟨⟩
  let P := AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian
    (P ↘ Spec (.of D.k))
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace
    (P ↘ Spec (.of D.k))
  have : IsNoetherian P := ⟨⟩
  exact closedAssembly_of_noetherian _ i _ c

end WeilConjectures
