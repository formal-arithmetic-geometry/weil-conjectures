/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Sheaf.AlgebraicGeometry.FlatValuationLifting
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Compactification.ValuativeCriterion
import WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring
import WeilConjectures.Mathlib.RingTheory.Valuation.ValuationSubring

/-! # Stacked valuations through a dense open algebraic subspace

Source: Stacks Project, Morphisms of Spaces, Tag 089G,
`lemma-refined-valuative-criterion-universally-closed`, proof from
`equation-start-with` through the construction of C, before assumption (4)
(blueprint: lem-sfb-space-dense-open-stacked-valuation).

All algebraic spaces are over Spec Z. Maps from spectra are Yoneda maps into the
underlying sheaves. The quotient and localization are the actual Mathlib constructions;
the residue-field identification is normalized on C, so all four equalities retain
the original field-valued morphisms rather than only their point classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The usual contravariant spectrum functor, regarded over Spec Z via its unique
structure map. This is just the composite of the existing spectrum and terminal-slice
functors; it introduces no new spectrum or algebraic-space construction.
Source: Stacks, Tag 089G, absolute-base convention
(blueprint: lem-sfb-space-dense-open-stacked-valuation). -/
def stackedValuationSpec : CommRingCat.{u}ᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ))) :=
  Scheme.Spec ⋙ (Over.equivalenceOfIsTerminal specULiftZIsTerminal).inverse

/-- Every valuation diagram admits a stacked valuation whose generic point lies in a
specified dense quasi-compact open subspace. No lifting hypothesis or restriction on p
is assumed. The residue isomorphism is fixed by the quotient map on C, and the field
extension of K is the fraction-field lift of the injective map from A.
Source: Stacks, Tag 089G, proof before invoking assumption (4)
(blueprint: lem-sfb-space-dense-open-stacked-valuation).

Proof:
1. Replace H and V by their reductions, using lem-sfb-space-reduced-closed-support
   and lem-sfb-space-reduced-map-closed-factorization. The field-valued point factors
   through the reduction. Density makes the open schematically dominant: any closed
   factorization has full support, and the identity of the reduced target factors
   through that closed subspace, so it is the whole target.
2. Choose an affine etale chart of X containing the closed image of Spec A. Scheme
   fibre products (lem-trf-space-fibre-products-etale-covers) and flat valuation lifting
   (lem-a1-flat-valuation-lifting) give an injective local extension A to A1 lifting
   the base map to this chart. Schematic-image flat base change
   (lem-sfb-stack-schematic-image-qc), and the etale/flat chart calculus
   (lem-sfb-stack-chartwise-smooth-etale-calculus), preserve schematic dominance.
3. Choose an affine etale chart Spec B of H containing the generic point after a
   common field extension K2. Extend A1 to a valuation ring A2 in K2 dominating it,
   using lemma-nagata-valuation-ring-extension. This preserves the original diagram.
4. Present K2 as a quotient of P = B[T_x | x in K2]. The map Spec P to H is flat
   (lem-nagata-polynomial-projection-flat and the chart calculus). The pullback of V
   is a quasi-compact open scheme W with full schematic image, by the flat-base-change
   theorem. Its closed point defined by the quotient P to K2 has residue field K2.
5. The scheme valuation probe (def-nagata-dense-valuation-probe and
   lemma-nagata-dense-valuation-probe) supplies a valuation D0 centred at this point,
   a generic lift into W and a map Spec D0 to H. The residue map P to F factors
   through the quotient K2, giving an embedding K2 into F. Its induced map to H is
   exactly the original generic map after field extension.
6. Extend A2 to a valuation subring E of F dominating it, with fraction field F
   (lemma-nagata-valuation-ring-extension). Define C inside D0 as the inverse image
   of E under the residue map. The composite-valuation theorem
   (lemma-nagata-composite-valuation-ring) makes C a valuation ring with fraction field
   Frac D0; q is the maximal ideal of D0 inside C and C/q identifies with E.
   The composite A to E is injective and local.
7. Identify C localized at q with D0. Every element outside q is a unit in D0.
   Conversely, write the residue of x in D0 as a/s with a,s in E and s nonzero;
   lift s to t in C outside q. Then tx is in C and x = (tx)/t. This gives the
   localization and its residue identification with Frac E, normalized on C.
8. The base-chart ring R maps into C because its residue lies in E. This defines b.
   Restriction to D gives alpha followed by p; reduction to E is the original base
   map extended along A to E. Step 5 gives both the generic factorization through V
   and the equality of the closed-fibre map with eta after K to Frac E. Transport
   along the quotient, localization and fraction-field identifications yields exactly
   the four displayed morphism equalities. -/
theorem exists_denseOpen_stackedValuation
    {H X V : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))} (p : H ⟶ X) (h : V ⟶ H)
    (hh : IsRepresentableWith (fun _ _ f ↦ IsOpenImmersion f.left) h.hom.hom)
    (hqc : MapIsQuasiCompact h.hom.hom) (hd : Dense (pointImage h.hom.hom))
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (a : yoneda.obj (stackedValuationSpec.obj (op (.of A))) ⟶ X.obj.obj)
    (η : yoneda.obj (stackedValuationSpec.obj (op (.of K))) ⟶ H.obj.obj)
    (hη : η ≫ p.hom.hom =
      yoneda.map (stackedValuationSpec.map (CommRingCat.ofHom (algebraMap A K)).op) ≫ a) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : ValuationRing C)
      (q : Ideal C) (_ : q.IsPrime) (_ : ValuationRing (C ⧸ q))
      (ι : A →+* C ⧸ q) (hι : Function.Injective ι) (_ : IsLocalHom ι)
      (_ : ValuationRing (Localization.AtPrime q))
      (ρ : IsLocalRing.ResidueField (Localization.AtPrime q) ≃+* FractionRing (C ⧸ q)),
      IsFractionRing (Localization.AtPrime q) (FractionRing C) ∧
      (ρ.toRingHom.comp (IsLocalRing.residue (Localization.AtPrime q))).comp
          (algebraMap C (Localization.AtPrime q)) =
        (algebraMap (C ⧸ q) (FractionRing (C ⧸ q))).comp (Ideal.Quotient.mk q) ∧
      ∃ (b : yoneda.obj (stackedValuationSpec.obj (op (.of C))) ⟶ X.obj.obj)
        (α : yoneda.obj (stackedValuationSpec.obj (op (.of (Localization.AtPrime q)))) ⟶
          H.obj.obj)
        (v : yoneda.obj (stackedValuationSpec.obj (op (.of (FractionRing C)))) ⟶ V.obj.obj),
        α ≫ p.hom.hom = yoneda.map (stackedValuationSpec.map
          (CommRingCat.ofHom (algebraMap C (Localization.AtPrime q))).op) ≫ b ∧
        yoneda.map (stackedValuationSpec.map
          (CommRingCat.ofHom (algebraMap (Localization.AtPrime q) (FractionRing C))).op) ≫
            α = v ≫ h.hom.hom ∧
        yoneda.map (stackedValuationSpec.map (CommRingCat.ofHom
          (ρ.toRingHom.comp (IsLocalRing.residue (Localization.AtPrime q)))).op) ≫ α =
          yoneda.map (stackedValuationSpec.map (CommRingCat.ofHom
            (IsFractionRing.lift (A := A) (K := K)
              (g := (algebraMap (C ⧸ q) (FractionRing (C ⧸ q))).comp ι)
              ((IsFractionRing.injective (C ⧸ q) (FractionRing (C ⧸ q))).comp hι))).op) ≫ η ∧
        yoneda.map (stackedValuationSpec.map
          (CommRingCat.ofHom (Ideal.Quotient.mk q)).op) ≫ b =
          yoneda.map (stackedValuationSpec.map (CommRingCat.ofHom ι).op) ≫ a := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
