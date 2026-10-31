/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteProjectionExchangeData

/-! # Refinement compatibility of the first finite projection diamond route -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.FiniteProjectionExchange
variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The left word in the finite diamond intertwines the witnessed refinement maps.
The right word then has the same property by the diamond equality, proved separately.
Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence.
(blueprint: lem-sf-finite-projection-refinement-left).

Proof: write T=K tensor f*L. Pullback preserves L's finite Tor interval and bounded
constructibility; tensoring with K preserves bounded constructibility. Pullback of
arbitrary bounded constructible K preserves its cohomological interval, without a
Tor hypothesis on K. Constructible origin supplies witnesses for T and a*T, and
naturality transports the comparison to each supplied witness e and eT.
For a refinement r, projection compatibility gives PF_c followed by rho_T equal to
rho_K tensor 1 followed by PF_d. Exchange compatibility gives Ex_c followed by the
base-changed rho at a*T equal to g*rho_T followed by Ex_d. Naturality of the
base-changed comparison with respect to the canonical target map identifies this
with rho at a*K tensor f'*g*L. Substitute the projection and exchange equations into
diamondLeft and use functoriality of g*. The intermediate rho_T cancels, leaving
exactly the displayed equality. The comparison cocycle identifies the single-refinement
map with the common-refinement composite in the projection-comparison theorem.
The coefficient hypotheses for arbitrary-K pullback follow from the coefficient DVR:
its residue field and all positive uniformizer quotients are finite, and each quotient
is perfect by its two-term free resolution. No finite Tor hypothesis on K is used. -/
theorem refinement_left (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    letI : TopologicalSpace (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) := ⊥
    letI : DiscreteTopology (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) :=
      discreteTopology_bot _
    ∀ (X Y Y' : SixFunctorSpace D) (f : X ⟶ Y) (g : Y' ⟶ Y)
      [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
      [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
      (X' : Scheme.{u}) (a : X' ⟶ X.obj.left) (f' : X' ⟶ Y'.obj.left)
      (s : IsPullback a f' f.hom.left g.hom.left)
      (K : Dcat (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) X.obj.left)
      (L : Dcat (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) Y.obj.left),
      finiteBC C.l E n hn X.obj.left K → finiteCTF C.l E n hn Y.obj.left L →
      ∀ (c d : Compactification f.hom.left) (r : c.Refinement d)
        (O : EtaleOriginDerivedCategory X.obj.left
          (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
        (e : refinementFixedObject X.obj.left _ O ≅ K)
        (OT : EtaleOriginDerivedCategory X'
          (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
        (eT : refinementFixedObject X' _ OT ≅
          tensor _ X' ((pull _ a).obj K) ((pull _ f').obj ((pull _ g.hom.left).obj L))),
        diamondLeft _ s c K L ≫ (rho _ (baseRefinement s r) _ OT eT).hom =
          (pull _ g.hom.left).map (tensorMap _ (rho _ r K O e).hom (𝟙 L)) ≫
            diamondLeft _ s d K L := by sorry

end AlgebraicGeometry.ProEtale.FiniteProjectionExchange
