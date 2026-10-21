/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.CoordinateGermCohomologyClasses
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # Concentrated supported coordinate transfer
Source: Stacks 09XP and conditional coordinate-model Steps 5--7
(blueprint: lem-pur-concentrated-support-etale-transfer).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
/-- Concentration of the normal complex and every supported zero-section stalk,
with orientations induced on every v by precisely the ordered coordinate class.
No hypothesis of finite type is imposed on the affine base.
Source: Stacks 09XP, conditional coordinate-model Steps 5--7
(blueprint: lem-pur-concentrated-support-etale-transfer). -/
structure TransferConcentration (P : PurityFiniteSetting.{u}) (b : ℕ)
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k)) (r : ℤ) where
  field_vanish : ∀ n : ℤ, n ≠ 2 * (b : ℤ) →
    IsZero ((P.transferH n).obj (P.transferGlobal (transferZero (Spec (.of P.field.k)) b) r))
  field_orientation : P.transferLine (r - b) ≅
    (P.transferH (2 * (b : ℤ))).obj (P.transferGlobal (transferZero (Spec (.of P.field.k)) b) r)
  field_class : ∀ v : P.transferLine (r - b),
    field_orientation.hom v = P.transferClassValue
      (transferZero (Spec (.of P.field.k)) b) (2 * (b : ℤ)) r
      (P.transferTwistedCoordinateClass b r v)
  stalk_vanish : ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ pullback (transferZero (Spec (.of P.field.k)) b)
        (P.transferProjection b aB)) (n : ℤ), n ≠ 2 * (b : ℤ) →
    IsZero ((P.transferH n).obj
      (P.transferStalk (P.transferBaseZero b aB) (x ≫ P.transferBaseZero b aB) r))
  stalk_orientation : ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ pullback (transferZero (Spec (.of P.field.k)) b)
        (P.transferProjection b aB)),
    P.transferLine (r - b) ≅ (P.transferH (2 * (b : ℤ))).obj
      (P.transferStalk (P.transferBaseZero b aB) (x ≫ P.transferBaseZero b aB) r)
  stalk_class : ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ pullback (transferZero (Spec (.of P.field.k)) b)
        (P.transferProjection b aB)) (v : P.transferLine (r - b)),
    (stalk_orientation x).hom v =
      (P.transferH (2 * (b : ℤ))).map
        (P.transferLocalGerm (P.transferBaseZero b aB) (x ≫ P.transferBaseZero b aB)
          (AffineSpace (ULift.{u} (Fin b)) B ↘ B ≫ aB) r)
        (P.transferClassValue (P.transferBaseZero b aB) (2 * (b : ℤ)) r
          (P.transferBaseClass b aB r v))

/-- The good-truncation normalization at any degree, expressed by the literal
truncation arrows and the existing natural single-cohomology comparison.
This is L[-q], represented by the degree-q single functor.
Source: Stacks Homology 0118
(blueprint: lem-pur-concentrated-support-etale-transfer). -/
def TransferTruncation (P : PurityFiniteSetting.{u})
    (K : DerivedCategory.Plus.{u + 1} (ModuleCat.{u + 1} P.Coefficient)) (q : ℤ)
    (L : ModuleCat.{u + 1} P.Coefficient) (uK : L ⟶ (P.transferH q).obj K)
    (aK : K ≅ (DerivedCategory.Plus.singleFunctor _ q).obj L) : Prop :=
  (DerivedCategory.Plus.TStructure.t.truncLTι (q + 1)).app K ≫ aK.hom ≫
      (DerivedCategory.Plus.singleFunctor _ q).map uK =
    (DerivedCategory.Plus.TStructure.t.truncGEπ q).app
        ((DerivedCategory.Plus.TStructure.t.truncLT (q + 1)).obj K) ≫
      (DerivedCategory.Plus.eTruncLTCompETruncGEIso q).hom.app K
  ∧ (P.transferH q).map aK.hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := ModuleCat.{u + 1} P.Coefficient) q).hom.app L ≫ uK = 𝟙 _

/-- The field-to-etale-neighbourhood germ is the coordinate pullback germ followed
by the literal-kernel etale restriction. The existing composition law identifies it
with the direct germ along e followed by projection.
Source: Stacks 09XP (blueprint: lem-pur-concentrated-support-etale-transfer). -/
def transferEtaleGerm (P : PurityFiniteSetting.{u}) (b : ℕ) {B : Scheme.{u}}
    (aB : B ⟶ Spec (.of P.field.k)) {T : Scheme.{u}}
    (e : T ⟶ AffineSpace (ULift.{u} (Fin b)) B) [Etale e]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) (r : ℤ) :
    P.transferField b r ⟶
      P.transferStalk (pullback.snd (P.transferBaseZero b aB) e) t r :=
  P.transferGerm b (P.transferBaseZero b aB) (P.transferProjection b aB)
    (Scheme.Pullback.range_snd _ _) (t ≫ e) r ≫
    P.transferRestriction (P.transferBaseZero b aB)
      (pullback.snd (P.transferBaseZero b aB) e) e (Scheme.Pullback.range_snd _ _) t
      (AffineSpace (ULift.{u} (Fin b)) B ↘ B ≫ aB) r

/-- Identify the two ways of viewing a geometric point of the inverse-image support.
Source: the fibre-product projection equation
(blueprint: lem-pur-concentrated-support-etale-transfer). -/
def transferPointIso (P : PurityFiniteSetting.{u}) (b : ℕ) {B : Scheme.{u}}
    (aB : B ⟶ Spec (.of P.field.k)) {T : Scheme.{u}}
    (e : T ⟶ AffineSpace (ULift.{u} (Fin b)) B)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (z : Spec (.of Ω) ⟶ pullback (P.transferBaseZero b aB) e) (r : ℤ) :
    P.transferStalk (P.transferBaseZero b aB)
        ((z ≫ pullback.fst (P.transferBaseZero b aB) e) ≫ P.transferBaseZero b aB) r ≅
      P.transferStalk (P.transferBaseZero b aB)
        ((z ≫ pullback.snd (P.transferBaseZero b aB) e) ≫ e) r :=
  eqToIso (congrArg (fun t ↦ P.transferStalk (P.transferBaseZero b aB) t r)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f ↦ z ≫ f) (pullback.condition (f := P.transferBaseZero b aB)
        (g := e))).trans (Category.assoc _ _ _).symm)))

/-- The transported orientation map at the actual supported etale stalk. Its
invertibility is a conclusion, not an added concentration hypothesis on T.
Source: Stacks 09XP, restriction of the input orientation
(blueprint: lem-pur-concentrated-support-etale-transfer). -/
def transferStalkOrientation (P : PurityFiniteSetting.{u}) (b : ℕ) {B : Scheme.{u}}
    (aB : B ⟶ Spec (.of P.field.k)) (r : ℤ) (h : P.TransferConcentration b aB r)
    {T : Scheme.{u}} (e : T ⟶ AffineSpace (ULift.{u} (Fin b)) B) [Etale e]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (z : Spec (.of Ω) ⟶ pullback (P.transferBaseZero b aB) e) :
    P.transferLine (r - b) ⟶ (P.transferH (2 * (b : ℤ))).obj
      (P.transferStalk (pullback.snd (P.transferBaseZero b aB) e)
        (z ≫ pullback.snd (P.transferBaseZero b aB) e) r) :=
  (h.stalk_orientation (z ≫ pullback.fst (P.transferBaseZero b aB) e)).hom ≫
    (P.transferH (2 * (b : ℤ))).map (P.transferPointIso b aB e z r).hom ≫
    (P.transferH (2 * (b : ℤ))).map
      (P.transferRestriction (P.transferBaseZero b aB)
        (pullback.snd (P.transferBaseZero b aB) e) e (Scheme.Pullback.range_snd _ _)
        (z ≫ pullback.snd (P.transferBaseZero b aB) e)
        (AffineSpace (ULift.{u} (Fin b)) B ↘ B ≫ aB) r)

/-- Etale transfer of the concentrated coordinate comparison, with exactly its
specified orientation and good-truncation inverse. Source: Stacks 09XP; conditional
coordinate-model Steps 5--7 and Homology 0118
(blueprint: lem-pur-concentrated-support-etale-transfer).
Proof: etale restriction identifies the literal support kernels and preserves
injective resolutions. Thus the supported stalk is the base stalk and inherits its
concentration. The pullback germ sends the ordered Cartier--Kummer product tensor v
to its supported pullback tensor v, by functoriality of cup and the specified signed
twist comparison. The two orientation equations give identity on H^(2b). Good
truncation and its natural single-cohomology comparison therefore give the displayed
normalizations and gamma = aK followed by inverse aD. Their reverse composite is the
inverse. All arguments allow arbitrary affine B and all integers r. -/
theorem concentratedSupportEtaleTransfer (P : PurityFiniteSetting.{u}) (b : ℕ)
    {B : Scheme.{u}} [IsAffine B] (aB : B ⟶ Spec (.of P.field.k)) (r : ℤ)
    (h : P.TransferConcentration b aB r) {T : Scheme.{u}}
    (e : T ⟶ AffineSpace (ULift.{u} (Fin b)) B) [Etale e]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (z : Spec (.of Ω) ⟶ pullback (P.transferBaseZero b aB) e) :
    IsIso (P.transferEtaleGerm b aB e (z ≫ pullback.snd (P.transferBaseZero b aB) e) r) ∧
    IsIso (P.transferStalkOrientation b aB r h e z) ∧
    (h.field_orientation.hom ≫ (P.transferH (2 * (b : ℤ))).map
      (P.transferEtaleGerm b aB e (z ≫ pullback.snd (P.transferBaseZero b aB) e) r) =
        P.transferStalkOrientation b aB r h e z) ∧
    (∀ n : ℤ, n ≠ 2 * (b : ℤ) →
      IsZero ((P.transferH n).obj
        (P.transferStalk (pullback.snd (P.transferBaseZero b aB) e)
          (z ≫ pullback.snd (P.transferBaseZero b aB) e) r))) ∧
    ∃ (aK : P.transferField b r ≅
        (DerivedCategory.Plus.singleFunctor _ (2 * (b : ℤ))).obj
          (P.transferLine (r - b)))
      (aD : P.transferStalk (pullback.snd (P.transferBaseZero b aB) e)
          (z ≫ pullback.snd (P.transferBaseZero b aB) e) r ≅
        (DerivedCategory.Plus.singleFunctor _ (2 * (b : ℤ))).obj
          (P.transferLine (r - b))),
      P.TransferTruncation
        (P.transferGlobal (transferZero (Spec (.of P.field.k)) b) r) (2 * (b : ℤ))
        (P.transferLine (r - b)) h.field_orientation.hom aK ∧
      P.TransferTruncation
        (P.transferStalk (pullback.snd (P.transferBaseZero b aB) e)
          (z ≫ pullback.snd (P.transferBaseZero b aB) e) r) (2 * (b : ℤ))
        (P.transferLine (r - b)) (P.transferStalkOrientation b aB r h e z) aD ∧
      P.transferEtaleGerm b aB e (z ≫ pullback.snd (P.transferBaseZero b aB) e) r =
        aK.hom ≫ aD.inv ∧
      (aD.hom ≫ aK.inv) ≫
        P.transferEtaleGerm b aB e (z ≫ pullback.snd (P.transferBaseZero b aB) e) r = 𝟙 _ ∧
      P.transferEtaleGerm b aB e (z ≫ pullback.snd (P.transferBaseZero b aB) e) r ≫
        (aD.hom ≫ aK.inv) = 𝟙 _ := by
  sorry

/-- Literal-kernel etale exchange and its derived comparison are invertible.
Source: Stacks 09XP and 03S2
(blueprint: lem-pur-concentrated-support-etale-transfer).
Proof: inverse image along an etale map is restriction to the localized site.
On each test object both supported sheaves are the identical complement kernel,
with identical inclusions. Thus the uniquely normalized exchange is invertible.
Restriction is exact and preserves injectives; apply the equality termwise to an
injective resolution to obtain the bounded-below derived isomorphism. -/
theorem transferSupportRestriction_isIso (P : PurityFiniteSetting.{u})
    {C X D Y : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (j : D ⟶ Y) [IsClosedImmersion j] (e : Y ⟶ X) [Etale e]
    (he : Set.range j.base = e.base ⁻¹' Set.range i.base) :
    IsIso (P.transferSupportRestriction i j e he) ∧
      IsIso (P.transferDerivedSupportRestriction i j e he) := by
  sorry

/-- Further etale restriction commutes with the normalized coordinate germ. Taking
an etale open immersion also gives restriction to affine base opens; applying this
twice gives equality on a common refinement of compatible affine neighbourhoods.
Source: Stacks 09XP, conditional transfer Step 6
(blueprint: lem-pur-concentrated-support-etale-transfer).
Proof: the underived germs commute by their kernel-inclusion characterization.
Derive that equation using the fixed inverse-image composition comparison. The
signed-twist pullback comparisons satisfy the same composition law, so cancel them
to obtain the displayed equality. This argument includes identity restrictions. -/
theorem transferGerm_restriction (P : PurityFiniteSetting.{u}) (b : ℕ)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (j : D ⟶ Y) [IsClosedImmersion j] (f : X ⟶ P.transferNormal b)
    (hf : Set.range i.base = f.base ⁻¹'
      Set.range (transferZero (Spec (.of P.field.k)) b).base)
    (e : Y ⟶ X) [Etale e] (he : Set.range j.base = e.base ⁻¹' Set.range i.base)
    (hef : Set.range j.base = (e ≫ f).base ⁻¹'
      Set.range (transferZero (Spec (.of P.field.k)) b).base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y) (r : ℤ) :
    P.transferGerm b i f hf (t ≫ e) r ≫
      P.transferRestriction i j e he t (f ≫ (P.transferNormal b ↘ Spec (.of P.field.k))) r =
        P.transferGerm b j (e ≫ f) hef t r := by
  sorry

/-- Compatibility for every specified coefficient tensor or dual comparison.
The arrows may be those induced by A(r)=A(b) tensor A(r-b), including evaluation
of negative powers. The square is required only on the input orientation lines;
no arbitrary identification of twists is substituted.
Source: Stacks 03PK and Homology 0118, conditional transfer Steps 7--8
(blueprint: lem-pur-concentrated-support-etale-transfer).
Proof: good truncation identifies each concentrated complex with its single
cohomology object, faithfully on morphisms. In these identifications the germ maps
are the identity on the input lines. The assumed coefficient squares therefore
give the stated derived square. This also applies to the specified canonical
restriction maps on a common refinement; the inverse squares follow by cancellation. -/
theorem transferCoefficientCompatibility (P : PurityFiniteSetting.{u}) (q : ℤ)
    {K D K' D' : DerivedCategory.Plus.{u + 1} (ModuleCat.{u + 1} P.Coefficient)}
    {L L' : ModuleCat.{u + 1} P.Coefficient}
    (uK : L ≅ (P.transferH q).obj K) (uD : L ≅ (P.transferH q).obj D)
    (uK' : L' ≅ (P.transferH q).obj K') (uD' : L' ≅ (P.transferH q).obj D')
    (hK : ∀ n : ℤ, n ≠ q → IsZero ((P.transferH n).obj K))
    (hD : ∀ n : ℤ, n ≠ q → IsZero ((P.transferH n).obj D))
    (hK' : ∀ n : ℤ, n ≠ q → IsZero ((P.transferH n).obj K'))
    (hD' : ∀ n : ℤ, n ≠ q → IsZero ((P.transferH n).obj D'))
    (γ : K ⟶ D) (γ' : K' ⟶ D') (a : K ⟶ K') (d : D ⟶ D') (c : L ⟶ L')
    (hγ : uK.hom ≫ (P.transferH q).map γ = uD.hom)
    (hγ' : uK'.hom ≫ (P.transferH q).map γ' = uD'.hom)
    (ha : uK.hom ≫ (P.transferH q).map a = c ≫ uK'.hom)
    (hd : uD.hom ≫ (P.transferH q).map d = c ≫ uD'.hom) :
    γ ≫ d = a ≫ γ' := by
  sorry

end WeilConjectures.PurityFiniteSetting
