/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients

/-!
# Counit normalization of the site-transported closed adjoint

Source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/
lem-coef-finite-dualizing.md, closed-immersion calculation (*); the normalized Hom chain in
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-existence/
thm-sf-ambient-adjoint-class.proof.md
(blueprint: lem-coef-site-closed-counit-transport).

We retain the identity-open compactification in the notation. Its ordinary adjunction is
identified with the closed direct-image adjunction by the canonical identity-open
normalization, and the inverse compact-support comparison is the direct-image mate delta.
Thus the formula below is (*) with these canonical identifications displayed by the
compactification interface, rather than a separately chosen Hom equivalence.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The specified comparison-class adjunction transports the closed counit, and its
adjunct of a transported ordinary morphism is the transported ordinary adjunct.
Source: blueprint lem-coef-finite-dualizing.md, closed-immersion equation (*), and
thm-sf-ambient-adjoint-class.proof.md, displayed normalized Hom chain
(blueprint: lem-coef-site-closed-counit-transport).

Proof: put F = Ri_! for the identity-open compactification, identified canonically with
Ri_*. Its compact-support comparison is delta inverse. By homEquiv_normalized, the
bijection at the identity-open compactification sends g to S_Z beta(eta_F ≫ U_P(g delta)).
For g = delta inverse ≫ S_P(f), unit naturality gives eta_F ≫ U_P(S_P(f)) = f ≫ eta_H.
Target naturality of the ordinary adjunction then gives beta(f ≫ eta_H) =
beta(f) ≫ G(eta_H). Applying S_Z proves the second clause. The isomorphism eta_H
makes G(eta_H) an isomorphism; therefore J S_P H is bounded below of etale origin,
with representative G H and isomorphism alpha. The relative counit E is defined by
C.homEquiv inverse of the identity. Source naturality gives the transpose of
F_pro(alpha) ≫ E as alpha. Specialize the general formula to f = the ordinary counit,
whose transpose is the identity. Injectivity of C.homEquiv and cancellation of delta
inverse give the first clause. This uses only bounded-below H and G H; constructibility
is never used. -/
theorem siteClosedCounitTransport
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (n : ℕ) (_hn : 1 ≤ n)
    [Finite (Padic.coefficientExtensionRing l E n)]
    {Z P : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of D.k)) (aP : P ⟶ Spec (.of D.k))
    [IsSeparated aZ] [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [IsSeparated aP] [LocallyOfFiniteType aP] [QuasiCompact aP]
    (i : Z ⟶ P) [IsClosedImmersion i] (_hi : i ≫ aP = aZ) :
    let Λ := Padic.coefficientExtensionRing l E n
    let A := ModuleCat.{u + 1} Λ
    let c₀ := Compactification.ofIsProper i
    let S := fun T : Scheme.{u} ↦ (comparisonUpperStar A T).mapDerivedCategory
    let U := fun T : Scheme.{u} ↦ (comparisonLowerStar A T).rightDerivedFunctor
    let F := Etale.rightDerivedLowerShriekOfCompactification A c₀
    let Fpro := rightDerivedLowerShriekOfCompactification A c₀
    ∀ (G : _root_.DerivedCategory (Sheaf P.smallEtaleTopology A) ⥤
          _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
      (adj : F ⊣ G)
      (C : ComparisonClassAdjunction Λ i c₀ G adj
        (DerivedCategory.plusEtaleOrigin A Z) _root_.DerivedCategory.TStructure.t.plus)
      (H : DerivedCategory.Plus (Sheaf P.smallEtaleTopology A))
      (hIH : _root_.DerivedCategory.TStructure.t.plus (G.obj H.obj)),
    let J := U P ⋙ G ⋙ S Z
    let α := (S Z).map (G.map ((derivedComparisonAdjunction A P).unit.app H.obj))
    let δ := fun L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ↦
      ((compactSupportSiteComparison Λ c₀).app L).symm
    IsIso α ∧
    ∃ hJ : DerivedCategory.plusEtaleOrigin A Z (J.obj ((S P).obj H.obj)),
      let E := (C.homEquiv c₀ _ hJ _
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj H.property).plus).symm
          (𝟙 (J.obj ((S P).obj H.obj)))
      (δ ⟨G.obj H.obj, hIH⟩).hom ≫ Fpro.map α ≫ E =
        (S P).map (adj.counit.app H.obj) ∧
      ∀ (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A))
        (f : F.obj L.obj ⟶ H.obj),
        C.homEquiv c₀ _
            (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property) _
            (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj H.property).plus
            ((δ L).inv ≫ (S P).map f) =
          (S Z).map (adj.homEquiv L.obj H.obj f) ≫ α := by
  sorry

end AlgebraicGeometry.ProEtale
