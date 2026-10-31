/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor

import all WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginComparisonCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange

/-! # Site realization of normalized coefficient counit mates

Source: main-20261015, lem-coef-finite-dualizing.proof.md, final paragraph, final sentence
(blueprint: lem-coef-dualizing-site-mates).

All comparisons below use the recorded compact-support, tensor, and comparison-unit maps.
The pro-etale Hom equivalence is restricted to its specified etale-origin class.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
open AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.CoefDualizingSiteMates

private local instance fixedSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private local instance finiteCoeff (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)

/-- Ordinary etale module derived category. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev Et (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- Its bounded-below full subcategory. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev EtPlus (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- The corresponding pro-etale category. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev Pro (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))

/-- Derived scalar extension on the unchanged small pro-etale site.
Source: blueprint coefficient convention (blueprint: lem-coef-dualizing-site-mates). -/
abbrev TP {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) : Pro A X ⥤ Pro B X :=
  @pbcFixedScalarExtension.{u} X.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
    A B inferInstance inferInstance φ

/-- The recorded exact comparison pullback. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev S (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) : Et A X ⥤ Pro A X :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory

/-- The recorded comparison direct image. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev U (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) : Pro A X ⥤ Et A X :=
  (comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerivedFunctor

/-- Compact support at the retained compactification. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev F (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : Et A X ⥤ Et A Y :=
  Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- The same compact support on D+. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev Fplus (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : EtPlus A X ⥤ EtPlus A Y :=
  Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c

/-- The recorded pro-etale compact support. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev P (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : Pro A X ⥤ Pro A Y :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- The right functor is precisely S G U. Source: blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
abbrev J (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (G : Et A Y ⥤ Et A X) : Pro A Y ⥤ Pro A X := U A Y ⋙ G ⋙ S A X

/-- Alpha is comparison pullback of G applied to the comparison adjunction unit.
Source: blueprint final paragraph (blueprint: lem-coef-dualizing-site-mates). -/
def alpha (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (G : Et A Y ⥤ Et A X) (H : Et A Y) :
    (S A X).obj (G.obj H) ⟶ (J A G).obj ((S A Y).obj H) :=
  (S A X).map (G.map ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app H))

/-- The universal tensor presentation is canonically isomorphic to the chosen scalar
extension, by the same universal unit. Source: Stacks 07A6 and blueprint final paragraph
(blueprint: lem-coef-dualizing-site-mates). -/
def modelIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {X : Scheme.{u}} {K : EtPlus A X}
    (M : Etale.CoefficientTensorModel φ X K) :
    (Etale.scalarExtension φ X).obj K.obj ≅ M.obj.obj :=
  let ad := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let g := (ad.homEquiv K.obj M.obj.obj).symm M.unit.hom
  have hu : Sheaf.IsDerivedBaseChange (ad.unit.app K.obj) := fun L ↦ by
    convert (ad.homEquiv K.obj L).bijective using 1
    funext g
    exact (ad.homEquiv_unit K.obj L g).symm
  have hg : ad.unit.app K.obj ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map g = M.unit.hom :=
    (ad.homEquiv_unit K.obj M.obj.obj g).symm.trans (Equiv.apply_symm_apply _ _)
  haveI := Sheaf.IsDerivedBaseChange.isIso hu M.universal g hg
  asIso g

/-- Tensor/site comparison at a universal tensor presentation, with B-linearity fixed
by the scalar unit. Source: blueprint final paragraph; Stacks 07A4
(blueprint: lem-coef-dualizing-site-mates). -/
def tensorSiteIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {X : Scheme.{u}} {K : EtPlus A X}
    (M : Etale.CoefficientTensorModel φ X K) :
    (S B X).obj M.obj.obj ≅
      (TP φ X).obj ((S A X).obj K.obj) :=
  (S B X).mapIso (modelIso M).symm ≪≫ (pbcComparisonReduction.{u} X φ).symm.app K.obj

/-- The source endpoint identification a = t followed by scalar extension of alpha.
Source: blueprint final paragraph (blueprint: lem-coef-dualizing-site-mates). -/
def sourceIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {X Y : Scheme.{u}} (G : Et A Y ⥤ Et A X)
    (N : EtPlus A Y) (hGN : _root_.DerivedCategory.TStructure.t.plus (G.obj N.obj))
    (M : Etale.CoefficientTensorModel φ X ⟨G.obj N.obj, hGN⟩)
    (hα : IsIso (alpha A G N.obj)) :
    (S B X).obj M.obj.obj ≅
      (TP φ X).obj
        ((J A G).obj ((S A Y).obj N.obj)) :=
  haveI := hα
  tensorSiteIso M ≪≫
    (TP φ X).mapIso (asIso (alpha A G N.obj))

/-- The quotient map at positive levels, lifted only to the module coefficient universe.
Source: blueprint coefficient convention (blueprint: lem-coef-dualizing-site-mates). -/
abbrev coefficientMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hmn : m ≤ n) :
    ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)) →+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)) :=
  RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E (n + 1))
    (T := Padic.coefficientExtensionIdeal l E (m + 1))
    (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn)))

attribute [local irreducible] counitWord sourceIso tensorSiteIso modelIso
  realizedWord realizedMate
  Etale.compactSupportCoefficientComparisonPlus Etale.CoefficientTensorModel.map
  compactSupportSiteComparison fixedCompactSupportComparisonIso
  pbcComparisonReduction pbcFixedScalarExtension pbcFixedScalarExtensionComp

private theorem map_map_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G.map (F.map (f ≫ g)) = G.map (F.map f) ≫ G.map (F.map g) := by
  rw [F.map_comp, G.map_comp]

end AlgebraicGeometry.ProEtale.CoefDualizingSiteMates

namespace CategoryTheory.CoefDualizingSiteMates

universe u₀ u₁ u₂ w₀ w₁ w₂ v₀ v₁ v₂ z₀ z₁ z₂

/-- Scalar transport through specified endpoint comparisons. The concrete comparison
is realizedMate; here the coherent tensor identifications are explicit parameters.
Source: blueprint final paragraph, quotient cocycle
(blueprint: lem-coef-dualizing-site-mates). -/
def transport {CA : Type u₀} [Category.{v₀} CA] {CB : Type u₁} [Category.{v₁} CB]
    {PA : Type w₀} [Category.{z₀} PA] {PB : Type w₁} [Category.{z₁} PB]
    (SA : CA ⥤ PA) (SB : CB ⥤ PB) (T : CA ⥤ CB) (TP : PA ⥤ PB)
    (t : SA ⋙ TP ≅ T ⋙ SB) {WA : CA} {WB : CB} {VA : PA} {VB : PB}
    (a : SA.obj WA ≅ VA) (b : SB.obj WB ≅ VB) (v : T.obj WA ⟶ WB) :
    TP.obj VA ⟶ VB :=
  TP.map a.inv ≫ t.hom.app WA ≫ SB.map v ≫ b.hom

/-- Transport preserves identity coefficient normalization under the specified tensor
unit identifications, including when the scalar functors are only isomorphic to identity.
Source: blueprint final paragraph, identity clause
(blueprint: lem-coef-dualizing-site-mates).

Proof: expand transport. The ordinary unit identification e and compatibility ht
replace the tensor-comparison factors by ep at S(W). Naturality of ep moves the
source endpoint inverse past ep. Cancel that inverse with the target endpoint.
The remaining arrow is ep at V, precisely the normalized identity. This applies
also to the canonical chosen scalar functors, not only literal identity functors. -/
theorem transport_identity {C : Type u₀} [Category.{v₀} C]
    {P : Type w₀} [Category.{z₀} P] (S : C ⥤ P)
    (T : C ⥤ C) (TP : P ⥤ P) (t : S ⋙ TP ≅ T ⋙ S)
    (e : T ≅ 𝟭 C) (ep : TP ≅ 𝟭 P)
    (_ht : ∀ W : C, t.hom.app W ≫ S.map (e.hom.app W) = ep.hom.app (S.obj W))
    {W : C} {V : P} (a : S.obj W ≅ V) :
    transport S S T TP t a a (e.hom.app W) = ep.hom.app V := by
  dsimp only [transport]
  calc
    _ = TP.map a.inv ≫ (t.hom.app W ≫ S.map (e.hom.app W)) ≫ a.hom := by
      simp only [Category.assoc]
    _ = TP.map a.inv ≫ ep.hom.app (S.obj W) ≫ a.hom := by rw [_ht]
    _ = ep.hom.app V ≫ a.inv ≫ a.hom := by
      rw [← Category.assoc, ep.hom.naturality]
      simp only [Functor.id_map, Category.assoc]
    _ = ep.hom.app V := by simp

/-- Every successive-coefficient cocycle transports under the specified coherent tensor
identifications. This is equality of the displayed arrows, not only of their iso classes.
Source: blueprint final paragraph, quotient cocycle
(blueprint: lem-coef-dualizing-site-mates).

Proof: expand both transported maps. The intermediate endpoint inverse and direct
comparison cancel. Naturality of tBC moves the image of vAB through tBC. The assumed
coherence of the tensor comparisons combines the two t factors into tAC, with the
specified scalar associator. Apply the assumed ordinary coefficient cocycle. The
remaining source endpoint passes through the pro-etale associator by naturality.
This is the direct transported map. The representative coherence required here is
the ordinary K-flat tensor reassociation: (x tensor b) tensor c maps to x tensor bc.
Hence the actual comparison comparisons in siteRealization satisfy this hypothesis. -/
theorem transport_cocycle
    {CA : Type u₀} [Category.{v₀} CA] {CB : Type u₁} [Category.{v₁} CB]
    {CC : Type u₂} [Category.{v₂} CC]
    {PA : Type w₀} [Category.{z₀} PA] {PB : Type w₁} [Category.{z₁} PB]
    {PC : Type w₂} [Category.{z₂} PC]
    (SA : CA ⥤ PA) (SB : CB ⥤ PB) (SC : CC ⥤ PC)
    (TAB : CA ⥤ CB) (TBC : CB ⥤ CC) (TAC : CA ⥤ CC)
    (PAB : PA ⥤ PB) (PBC : PB ⥤ PC) (PAC : PA ⥤ PC)
    (tAB : SA ⋙ PAB ≅ TAB ⋙ SB) (tBC : SB ⋙ PBC ≅ TBC ⋙ SC)
    (tAC : SA ⋙ PAC ≅ TAC ⋙ SC) (e : TAB ⋙ TBC ≅ TAC) (ep : PAB ⋙ PBC ≅ PAC)
    (_ht : ∀ W : CA,
      PBC.map (tAB.hom.app W) ≫ tBC.hom.app (TAB.obj W) ≫ SC.map (e.hom.app W) =
        ep.hom.app (SA.obj W) ≫ tAC.hom.app W)
    {WA : CA} {WB : CB} {WC : CC} {VA : PA} {VB : PB} {VC : PC}
    (a : SA.obj WA ≅ VA) (b : SB.obj WB ≅ VB) (c : SC.obj WC ≅ VC)
    (vAB : TAB.obj WA ⟶ WB) (vBC : TBC.obj WB ⟶ WC) (vAC : TAC.obj WA ⟶ WC)
    (_hv : TBC.map vAB ≫ vBC = e.hom.app WA ≫ vAC) :
    PBC.map (transport SA SB TAB PAB tAB a b vAB) ≫
        transport SB SC TBC PBC tBC b c vBC =
      ep.hom.app VA ≫ transport SA SC TAC PAC tAC a c vAC := by
  simp only [transport, Functor.map_comp, Category.assoc]
  rw [← PBC.map_comp_assoc b.hom b.inv, b.hom_inv_id]
  simp only [Functor.map_id, Category.id_comp]
  have hn := tBC.hom.naturality_assoc vAB (SC.map vBC ≫ c.hom)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [← SC.map_comp_assoc, _hv, SC.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (_ht WA)]
  simpa only [Functor.comp_map, Category.assoc] using
    ep.hom.naturality_assoc a.inv (tAC.hom.app WA ≫ SC.map vAC ≫ c.hom)

end CategoryTheory.CoefDualizingSiteMates

namespace AlgebraicGeometry.ProEtale.CoefDualizingSiteMates

/-- The pro-etale scalar associator, fixed by the composition of the actual restriction
functors. Source: blueprint quotient cocycle (blueprint: lem-coef-dualizing-site-mates). -/
def tensorComp {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (X : Scheme.{u}) :
    TP φ X ⋙ TP ψ X ≅ TP (ψ.comp φ) X :=
  @pbcFixedScalarExtensionComp.{u} X.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
    A B C inferInstance inferInstance inferInstance φ ψ (ψ.comp φ) rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Coherence of the actual site/tensor comparisons for successive coefficients.
Source: blueprint quotient cocycle (blueprint: lem-coef-dualizing-site-mates).

Proof: the generic comparisonScalarComp lemma expresses this coherence with the
inverse site comparisons. It follows from composition of scalar restriction mates,
exact derived descent, and preservation of horizontal pasting by the mates equivalence.
Cancel the direct comparison on the right and its two inverse-comparison factors;
functoriality and identity cancellation give the displayed equation. No flatness or
boundedness hypothesis is used. -/
theorem tensorCoherence {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (X : Scheme.{u}) (K : Et A X) :
    (TP ψ X).map ((pbcComparisonReduction.{u} X φ).hom.app K) ≫
        (pbcComparisonReduction.{u} X ψ).hom.app ((Etale.scalarExtension φ X).obj K) ≫
        (S C X).map
          ((pbcFixedScalarExtensionComp.{u} X.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app K) =
      (tensorComp φ ψ X).hom.app ((S A X).obj K) ≫
        (pbcComparisonReduction.{u} X (ψ.comp φ)).hom.app K := by
  apply (cancel_mono ((pbcComparisonReduction X (ψ.comp φ)).inv.app K)).1
  simp only [Category.assoc]
  rw [comparisonScalarComp X φ ψ (ψ.comp φ) rfl K]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  erw [(TP ψ X).map_id]
  simp only [Category.id_comp, Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtale.CoefDualizingSiteMates
