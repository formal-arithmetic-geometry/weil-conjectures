/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.SixFunctors.EtaleRestrictionCompositor
import WeilConjectures.SixFunctors.CompactSupportOriginRestrictionComposition


/-! # Finite coefficient comparison and compact-support composition

Source: Stacks Project, more-etale.tex, Tags 0F7J and 0GL6
(blueprint: lem-sf-compact-coefficient-composition).
The two statements use the actual small-etale and pro-etale compact-support functors,
the specified canonical compositors, and universal B-linear coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
private theorem universalComparison_composition
    {AX AY AZ BX BY BZ : Type*}
    [Category AX] [Category AY] [Category AZ]
    [Category BX] [Category BY] [Category BZ]
    (RX : BX ⥤ AX) (RY : BY ⥤ AY) (RZ : BZ ⥤ AZ)
    (FA : AX ⥤ AY) (GA : AY ⥤ AZ) (HA : AX ⥤ AZ)
    (FB : BX ⥤ BY) (GB : BY ⥤ BZ) (HB : BX ⥤ BZ)
    (rf : RX ⋙ FA ⟶ FB ⋙ RY) (rg : RY ⋙ GA ⟶ GB ⋙ RZ)
    (rh : RX ⋙ HA ⟶ HB ⋙ RZ)
    {K : AX} {M : BX} {N : BY} {P S : BZ}
    (uM : K ⟶ RX.obj M) (uN : FA.obj K ⟶ RY.obj N)
    (uP : GA.obj (FA.obj K) ⟶ RZ.obj P) (uS : HA.obj K ⟶ RZ.obj S)
    (qf : N ⟶ FB.obj M) (qg : P ⟶ GB.obj N) (qh : S ⟶ HB.obj M)
    (t : P ⟶ S)
    (a : GA.obj (FA.obj K) ⟶ HA.obj K)
    (c : GA.obj (FA.obj (RX.obj M)) ⟶ HA.obj (RX.obj M))
    (b : GB.obj (FB.obj M) ⟶ HB.obj M)
    (hu : Function.Injective (fun v : P ⟶ HB.obj M ↦ uP ≫ RZ.map v))
    (hf : uN ≫ RY.map qf = FA.map uM ≫ rf.app M)
    (hg : uP ≫ RZ.map qg = GA.map uN ≫ rg.app N)
    (hh : uS ≫ RZ.map qh = HA.map uM ≫ rh.app M)
    (ht : uP ≫ RZ.map t = a ≫ uS)
    (hc : GA.map (rf.app M) ≫ rg.app (FB.obj M) ≫ RZ.map b =
      c ≫ rh.app M)
    (ha : GA.map (FA.map uM) ≫ c = a ≫ HA.map uM) :
    t ≫ qh = qg ≫ GB.map qf ≫ b := by
  apply hu
  simp only [Functor.map_comp, ← Category.assoc]
  rw [ht, hg]
  simp only [Category.assoc]
  have hn := rg.naturality qf
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  change a ≫ uS ≫ RZ.map qh =
    GA.map uN ≫ GA.map (RY.map qf) ≫ rg.app (FB.obj M) ≫ RZ.map b
  rw [hh, ← GA.map_comp_assoc, hf, GA.map_comp, Category.assoc, hc]
  simpa only [Category.assoc] using (congrArg (· ≫ rh.app M) ha).symm

attribute [local irreducible] Padic.coefficientExtensionIntegers
private theorem tensor_compositor
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (F' : D₀ ⥤ D₁) (G' : D₁ ⥤ D₂) (H' : D₀ ⥤ D₂)
    (U₀ : D₀ ⥤ C₀) (U₁ : D₁ ⥤ C₁) (U₂ : D₂ ⥤ C₂)
    (cF : U₀ ⋙ F ⟶ F' ⋙ U₁) (cG : U₁ ⋙ G ⟶ G' ⋙ U₂)
    (cH : U₀ ⋙ H ⟶ H' ⋙ U₂)
    {K : C₀} {M : D₀} {N : D₁} {P S : D₂}
    (aK : G.obj (F.obj K) ⟶ H.obj K)
    (aM : G.obj (F.obj (U₀.obj M)) ⟶ H.obj (U₀.obj M))
    (bM : G'.obj (F'.obj M) ⟶ H'.obj M)
    (η : K ⟶ U₀.obj M) (ν : F.obj K ⟶ U₁.obj N)
    (ρ : G.obj (F.obj K) ⟶ U₂.obj P) (σ : H.obj K ⟶ U₂.obj S)
    (qF : N ⟶ F'.obj M) (qG : P ⟶ G'.obj N) (qH : S ⟶ H'.obj M) (t : P ⟶ S)
    (hF : ν ≫ U₁.map qF = F.map η ≫ cF.app M)
    (hG : ρ ≫ U₂.map qG = G.map ν ≫ cG.app N)
    (hH : σ ≫ U₂.map qH = H.map η ≫ cH.app M)
    (ht : ρ ≫ U₂.map t = aK ≫ σ)
    (ha : G.map (F.map η) ≫ aM = aK ≫ H.map η)
    (hc : aM ≫ cH.app M =
      G.map (cF.app M) ≫ cG.app (F'.obj M) ≫ U₂.map (bM))
    (hinj : Function.Injective (fun z : P ⟶ H'.obj M ↦ ρ ≫ U₂.map z)) :
    t ≫ qH = qG ≫ G'.map qF ≫ bM := by
  apply hinj
  simp only [Functor.map_comp]
  rw [← Category.assoc, ht, Category.assoc, hH]
  rw [← Category.assoc, ← ha]
  rw [Category.assoc, hc]
  rw [← Category.assoc ρ, hG]
  have hn := cG.naturality qF
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn]
  rw [← G.map_comp_assoc, ← hF, G.map_comp]
  simp only [Category.assoc]

namespace AlgebraicGeometry.ProEtale

private theorem restriction_origin
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u})
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X L) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj L) := by
  rcases hL with ⟨K, hK, ⟨e⟩⟩
  let K' := (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj ⟨K, hK⟩
  refine ⟨K'.obj, K'.property, ⟨?_⟩⟩
  exact ((pbcDerivedComparisonRestrict X φ).app K).symm ≪≫
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).mapIso e


private theorem comparison_unit_pro
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {φ : A →+* B} {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K)) :
    N.unit ≫ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
      (compactSupportCoefficientComparison c M N) =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map M.unit ≫
        (compactSupportRestrictionIso φ c).hom.app M.obj := by
  change N.unit ≫ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
      ((Equiv.ofBijective _ (N.universal _)).symm _) = _
  exact (Equiv.ofBijective _ (N.universal _)).apply_symm_apply _

attribute [local irreducible] originCompositionAmbient

private theorem tensorMap_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {T : Scheme.{u}}
    {K L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ T K) (N : CoefficientTensorModel φ T L) (a : K ⟶ L) :
    M.unit ≫ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ).map
      (M.map N a) = a ≫ N.unit := by
  unfold CoefficientTensorModel.map
  exact Equiv.ofBijective_apply_symm_apply _ (M.universal N.obj) _

private theorem tensorComparison_origin_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K))
    (P : CoefficientTensorModel φ Z ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K)))
    (S : CoefficientTensorModel φ Z
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj K))
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X M.obj) :
    P.map S ((originCompositionAmbient A f g).hom.app ⟨K, hK⟩) ≫
        compactSupportCoefficientComparison (HasCompactification.compactification (f ≫ g)) M S =
      compactSupportCoefficientComparison (HasCompactification.compactification g) N P ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
          (compactSupportCoefficientComparison (HasCompactification.compactification f) M N) ≫
        (originCompositionAmbient B f g).hom.app ⟨M.obj, hM⟩ := by
  let hR := restriction_origin φ X M.obj hM
  exact universalComparison_composition
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g))
    (compactSupportRestrictionIso φ (HasCompactification.compactification f)).hom
    (compactSupportRestrictionIso φ (HasCompactification.compactification g)).hom
    (compactSupportRestrictionIso φ (HasCompactification.compactification (f ≫ g))).hom
    M.unit N.unit P.unit S.unit
    (compactSupportCoefficientComparison (HasCompactification.compactification f) M N)
    (compactSupportCoefficientComparison (HasCompactification.compactification g) N P)
    (compactSupportCoefficientComparison (HasCompactification.compactification (f ≫ g)) M S)
    (P.map S ((originCompositionAmbient A f g).hom.app ⟨K, hK⟩))
    ((originCompositionAmbient A f g).hom.app ⟨K, hK⟩)
    ((originCompositionAmbient A f g).hom.app ⟨_, hR⟩)
    ((originCompositionAmbient B f g).hom.app ⟨M.obj, hM⟩)
    (P.universal _).1
    (comparison_unit_pro _ M N) (comparison_unit_pro _ N P)
    (comparison_unit_pro _ M S) (tensorMap_unit P S _)
    (compactSupportOriginRestrictionComposition φ f g M.obj hM hR)
    (by
      let a : (⟨K, hK⟩ :
          (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory) ⟶
          ⟨(Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj M.obj, hR⟩ :=
        ObjectProperty.homMk M.unit
      simpa only [Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_map,
        ObjectProperty.ι_obj, a, ObjectProperty.homMk] using
        (originCompositionAmbient A f g).hom.naturality a)


/-- Positive-level coefficient rings in the standard coefficient universe are finite.
This only registers the recorded coefficient finiteness theorem at positive levels.
Source: Serre, Local Fields, Chapter II, section 2; Stacks Tag 0GL6
(blueprint: lem-sf-compact-coefficient-composition). -/
instance finiteCompositionCoefficient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ+) : Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
  Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n n.property)

/-- The specified quotient coefficient homomorphism, with only the standard universe lift.
Source: Stacks Tag 0GL6 (blueprint: lem-sf-compact-coefficient-composition). -/
def finiteCompositionReduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ+) (hmn : n ≤ m) :
    ULift.{u + 1} (Padic.coefficientExtensionRing l E m) →+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E n) :=
  RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E m)
    (T := Padic.coefficientExtensionIdeal l E n) (Ideal.pow_le_pow_right hmn))

/-- Register the existing Nagata construction for a separated finite-type morphism
whose target is separated and quasi-compact over the fixed field. The two topological
instances are consequences of its structure morphism, not hypotheses on the theorem.
Source: Stacks Tags 0F41 and 0F7J
(blueprint: lem-sf-compact-coefficient-composition). -/
noncomputable def finiteCompositionCompactification
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Compactification f :=
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k))
  letI := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (CommRingCat.of k))
  NagataCompactification f

/-- The canonical B-linear coefficient comparison respects geometric composition on finite
constructible pro-etale realizations, for every universal tensor presentation.
Source: Stacks Project, Tags 0F7J and 0GL6
(blueprint: lem-sf-compact-coefficient-composition).

Proof: choose the existing Nagata compactifications. The tensor object M has etale
origin by its specified finite-Tor comparison. Restriction of coefficients preserves
that origin by pbcDerivedComparisonRestrict. The canonical origin compositor respects
restriction by compactSupportOriginRestrictionComposition. Apply the universal property
of P: it is enough to compare the two morphisms after restriction and precomposition
with P.unit. The three comparison maps satisfy their defining universal unit equations,
and P.map S satisfies the tensor-map unit equation. Naturality of the restriction
comparison moves q_f past the g-comparison. Naturality of the origin compositor along
M.unit then identifies the two resulting words. This uses the universal bijection's
injectivity, not faithfulness of derived scalar restriction.
-/
theorem finiteCoefficient_compactSupport_composition
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ+) (hmn : n ≤ m)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [Z.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of D.k))] [g.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    letI := (ProEtale.finiteCompositionCompactification D.k f).hasCompactification
    letI := (ProEtale.finiteCompositionCompactification D.k g).hasCompactification
    letI := (ProEtale.finiteCompositionCompactification D.k (f ≫ g)).hasCompactification
    ∀ (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)))))
    (K₀ : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)))))
    (hK₀ : WeilConjectures.finiteTorConstructibleEtale l E m m.property X K₀.obj)
    (e : (comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))) X).mapDerivedCategory.obj K₀.obj ≅ K)
    (M : CoefficientTensorModel (finiteCompositionReduction l E m n hmn) X K)
    (N : CoefficientTensorModel (finiteCompositionReduction l E m n hmn) Y
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) f).obj K))
    (P : CoefficientTensorModel (finiteCompositionReduction l E m n hmn) Z
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) g).obj ((rightDerivedLowerShriek (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))) f).obj K)))
    (S : CoefficientTensorModel (finiteCompositionReduction l E m n hmn) Z
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) (f ≫ g)).obj K)),
    P.map S ((originCompositionAmbient (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m)) f g).hom.app
        ⟨K, ⟨K₀.obj, K₀.property, ⟨e⟩⟩⟩) ≫
        compactSupportCoefficientComparison (HasCompactification.compactification (f ≫ g)) M S =
      compactSupportCoefficientComparison (HasCompactification.compactification g) N P ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E n))) g).map
          (compactSupportCoefficientComparison (HasCompactification.compactification f) M N) ≫
        (originCompositionAmbient (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E n)) f g).hom.app
          ⟨M.obj, M.origin_of_etale_finiteTor l E m n n.property hmn K₀ hK₀ e⟩ := by
  let := finiteCompositionCompactification D.k f |>.hasCompactification
  let := finiteCompositionCompactification D.k g |>.hasCompactification
  let := finiteCompositionCompactification D.k (f ≫ g) |>.hasCompactification
  intro K K₀ hK₀ e M N P S
  exact tensorComparison_origin_composition (finiteCompositionReduction l E m n hmn) f g K
    ⟨K₀.obj, K₀.property, ⟨e⟩⟩ M N P S
    (M.origin_of_etale_finiteTor l E m n n.property hmn K₀ hK₀ e)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

private theorem restriction_map_hom
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (T : Scheme.{u})
    {M N : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))}
    (z : M ⟶ N) :
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.map z).hom =
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map z.hom := by
  rfl

private theorem tensor_injective
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {T : Scheme.{u}}
    {K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ T K)
    (N : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    Function.Injective (fun z : M.obj ⟶ N ↦ M.unit ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.map z) := by
  intro x y h
  apply ObjectProperty.hom_ext
  apply (M.universal _).injective
  simpa only [ObjectProperty.FullSubcategory.comp_hom, restriction_map_hom]
    using congrArg (fun z ↦ z.hom) h

private theorem tensor_map_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {T : Scheme.{u}}
    {K L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ T K) (N : CoefficientTensorModel φ T L) (z : K ⟶ L) :
    M.unit ≫ (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.map
      (M.map N z) = z ≫ N.unit := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, restriction_map_hom]
  exact (Equiv.ofBijective _ (M.universal _)).apply_symm_apply _

private theorem comparison_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj K)) :
    N.unit ≫ (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus.map
      (compactSupportCoefficientComparisonPlus c M N) =
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).map M.unit ≫
      (compactSupportCoefficientRestrictionPlus φ c).hom.app M.obj := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, restriction_map_hom]
  exact (Equiv.ofBijective _ (N.universal _)).apply_symm_apply _

attribute [local implicit_reducible] Functor.mapDerivedCategoryPlus
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctorPlus
  Functor.rightDerivedFunctor
attribute [local implicit_reducible] derivedPlusFormalism
attribute [local irreducible] compactSupportCoefficientRestrictionPlus
attribute [local implicit_reducible] ExchangeFormalism.shriek
attribute [local irreducible] rightDerivedLowerShriekPlusCompIso
  compactSupportCoefficientComparisonPlus CoefficientTensorModel.map

private theorem tensor_compactSupport_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj K))
    (P : CoefficientTensorModel φ Z
      ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) g).obj
        ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj K)))
    (S : CoefficientTensorModel φ Z
      ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) (f ≫ g)).obj K)) :
    P.map S ((rightDerivedLowerShriekPlusCompIso A f g).hom.app K) ≫
        compactSupportCoefficientComparisonPlus
          (HasCompactification.compactification (f ≫ g)) M S =
      compactSupportCoefficientComparisonPlus (HasCompactification.compactification g) N P ≫
        (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} B) g).map
          (compactSupportCoefficientComparisonPlus
            (HasCompactification.compactification f) M N) ≫
        (rightDerivedLowerShriekPlusCompIso B f g).hom.app M.obj := by
  exact tensor_compositor
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f)
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) (f ≫ g))
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} B) f)
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} B) g)
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} B) (f ≫ g))
    (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus
    (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus
    (compactSupportCoefficientRestrictionPlus φ
      (HasCompactification.compactification f)).hom
    (compactSupportCoefficientRestrictionPlus φ
      (HasCompactification.compactification g)).hom
    (compactSupportCoefficientRestrictionPlus φ
      (HasCompactification.compactification (f ≫ g))).hom
    (K := K) (M := M.obj) (N := N.obj) (P := P.obj) (S := S.obj)
    ((rightDerivedLowerShriekPlusCompIso A f g).hom.app K)
    ((rightDerivedLowerShriekPlusCompIso A f g).hom.app
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj M.obj))
    ((rightDerivedLowerShriekPlusCompIso B f g).hom.app M.obj)
    M.unit N.unit P.unit S.unit
    (compactSupportCoefficientComparisonPlus (HasCompactification.compactification f) M N)
    (compactSupportCoefficientComparisonPlus (HasCompactification.compactification g) N P)
    (compactSupportCoefficientComparisonPlus (HasCompactification.compactification (f ≫ g)) M S)
    (P.map S ((rightDerivedLowerShriekPlusCompIso A f g).hom.app K))
    (comparison_unit _ M N) (comparison_unit _ N P) (comparison_unit _ M S)
    (tensor_map_unit P S _)
    ((rightDerivedLowerShriekPlusCompIso A f g).hom.naturality M.unit)
    (compactSupportRestrictionPlus_compositor φ f g M.obj)
    (tensor_injective P _)


/-- The same composition square on the small ordinary-etale site. All tensor units
are universal in the ambient derived categories, so nonflat reductions are included.
Source: Stacks Project, Tags 0F7J and 0GL6
(blueprint: lem-sf-compact-coefficient-composition).

Proof (the ten steps of the node):
1. Finite-type schemes over k are Noetherian and qcqs. Choose compatible compactifications
   by Nagata and lem-weil-pbc-compatible-compactification-triangle. Open extension and
   proper pushforward preserve the finite-Tor constructible domain (lem-trf-open-ctf,
   cor-sf-direct-image-ctf-proetale), so q_g is defined at F_f K.
2. Use lem-sf-flat-model and lem-sf-reduction-flat-model: bounded flat representatives
   stay bounded and flat under nonflat reduction. Finite tensor preserves constructible
   cohomology; constructible origin and full faithfulness of thm-weil-pbc-site-comparison
   reflect etale constructibility and lem-sf-comparison-tor-amplitude reflects the interval.
3. Normalize q as the proper counit mate followed by the open unit mate, as in
   lem-fix-compact-support-coefficient-change. The maps are B-linear universal adjuncts.
4. Inverse-image coefficient identifications compose on K-flat pure tensors. Apply
   lem-weil-pbc-mate-pasting to obtain the proper and open composition identities.
5. Paste the same coefficient squares with the cartesian proper/open inverse-image
   square. Taking mates gives the mixed-interchange coefficient identity.
6. Transpose that identity under the open adjunction, use the open unit identities,
   and cancel the invertible restriction exchange (lem-amb-unbounded-proper-open-interchange).
7. For noncartesian refinements use def-weil-pbc-proper-open-comparison: its exchange,
   open base-change and clopen-section factors all commute with coefficients. Transpose
   and use the universal tensor bijection to obtain refinement compatibility in D(B).
8. Expand the canonical compositor using lem-amb-unbounded-compact-support-comparisons
   or lem-amb-etale-compact-comparisons. Substitute the proper, open and mixed identities
   of steps 4--6, and cancel the refinement factors from step 7.
9. The remaining two paths are exactly the displayed equality with the stated endpoints.
10. Transport through the unit/counit-normalized compactification site comparison,
   lem-sf-class-compact-support-comparison and lem-sf-proper-open-comparison-site-normalization.
   Its three factors respect the same coefficient squares; full faithfulness reflects
   the ordinary-etale equation. No exceptional adjunction or faithfulness of scalar
   restriction in the derived category is used.
-/
theorem finiteCoefficient_compactSupport_composition
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ+) (hmn : n ≤ m)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [Z.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of D.k))] [g.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    letI := (ProEtale.finiteCompositionCompactification D.k f).hasCompactification
    letI := (ProEtale.finiteCompositionCompactification D.k g).hasCompactification
    letI := (ProEtale.finiteCompositionCompactification D.k (f ≫ g)).hasCompactification
    ∀ (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m)))))
    (_hK : WeilConjectures.finiteTorConstructibleEtale l E m m.property X K.obj)
    (M : CoefficientTensorModel (ProEtale.finiteCompositionReduction l E m n hmn) X K)
    (N : CoefficientTensorModel (ProEtale.finiteCompositionReduction l E m n hmn) Y
      ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) f).obj K))
    (P : CoefficientTensorModel (ProEtale.finiteCompositionReduction l E m n hmn) Z
      ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) g).obj
        ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) f).obj K)))
    (S : CoefficientTensorModel (ProEtale.finiteCompositionReduction l E m n hmn) Z
      ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) (f ≫ g)).obj K)),
    P.map S ((rightDerivedLowerShriekPlusCompIso (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m)) f g).hom.app K) ≫
        compactSupportCoefficientComparisonPlus
          (HasCompactification.compactification (f ≫ g)) M S =
      compactSupportCoefficientComparisonPlus (HasCompactification.compactification g) N P ≫
        (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E n))) g).map
          (compactSupportCoefficientComparisonPlus
            (HasCompactification.compactification f) M N) ≫
        (rightDerivedLowerShriekPlusCompIso (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E n)) f g).hom.app M.obj := by
  let := (ProEtale.finiteCompositionCompactification D.k f).hasCompactification
  let := (ProEtale.finiteCompositionCompactification D.k g).hasCompactification
  let := (ProEtale.finiteCompositionCompactification D.k (f ≫ g)).hasCompactification
  intro K _hK M N P S
  exact tensor_compactSupport_composition
    (ProEtale.finiteCompositionReduction l E m n hmn) f g K M N P S

end AlgebraicGeometry.Etale
