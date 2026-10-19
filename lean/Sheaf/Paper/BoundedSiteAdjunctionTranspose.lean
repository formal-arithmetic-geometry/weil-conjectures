/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.AlgebraicGeometry.ProperBasic
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Chosen-compactification normalization of bounded site adjunction transposes

Source: Stacks Project, Tag 0B65, lemma-transformation-between-functors-and-adjoints;
blueprint thm-sf-ambient-adjoint-class, bounded Hom chain
(blueprint: lem-pur-bounded-site-adjunction-transpose).

The comparison is the inverse of `compactSupportSiteComparison`, hence is built from
exact extension by zero and the named proper counit mate. The specified Hom map below
is defined by that comparison and the two existing adjunctions. Its inverse uniquely
defines the relative counit. No adjunction on all pro-etale objects is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The positive finite coefficient quotient is finite, including its standard size lift.
Source: blueprint def-pur-conventions; coefficient finiteness
(blueprint: lem-pur-bounded-site-adjunction-transpose). -/
instance boundedSiteCoefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

section Generic

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
variable (H : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
  DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
variable (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ H)

/-- The specified Hom-chain function, using the identity etale-origin witness and the
same compactification throughout. Source: Stacks Tag 0B65; blueprint bounded Hom chain
(blueprint: lem-pur-bounded-site-adjunction-transpose). -/
def boundedSiteTranspose
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (z : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (D(ν^*(X)[ModuleCat.{u + 1} A]).obj J.obj) ⟶ L) :
    D(ν^*(X)[ModuleCat.{u + 1} A]).obj J.obj ⟶
      D(ν^*(X)[ModuleCat.{u + 1} A]).obj (H.obj ((R(ν_*(Y)[ModuleCat.{u + 1} A])).obj L)) :=
  D(ν^*(X)[ModuleCat.{u + 1} A]).map
    ((adj.homEquiv J.obj _)
      ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ L
        ((compactSupportSiteComparison A c).inv.app J ≫ z)))

/-- The comparison of right-adjoint objects is the image of the actual comparison unit.
Source: Stacks Tag 0B65; blueprint bounded site transpose, rho
(blueprint: lem-pur-bounded-site-adjunction-transpose). -/
def boundedSiteRho
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    D(ν^*(X)[ModuleCat.{u + 1} A]).obj (H.obj K) ⟶
      D(ν^*(X)[ModuleCat.{u + 1} A]).obj
        (H.obj (R(ν_*(Y)[ModuleCat.{u + 1} A]).obj
          (D(ν^*(Y)[ModuleCat.{u + 1} A]).obj K))) :=
  D(ν^*(X)[ModuleCat.{u + 1} A]).map
    (H.map ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app K))

end Generic

/-- The etale intermediate object in the specified bounded Hom chain is bounded below.
Source: Stacks Tag 0B65; blueprint thm-sf-ambient-adjoint-class, Hom chain
(blueprint: lem-pur-bounded-site-adjunction-transpose).

Proof:
1. Exact etale and pro-etale extension by zero (lem-weil-pbc-extension-by-zero-exact,
lem-weil-extension-by-zero-exact) gives the open comparison degreewise. Apply the
named proper counit mate (lem-weil-pbc-comparison-direct-image-canonical-mate) to
its bounded-below input. Their composite is precisely B, natural in every input.
2. thm-sf-ambient-adjoint-class gives boundedness of C_X H U_Y L. Exact comparison
commutes with cohomology (lem-sf-comparison-pullback-exact) and is fully faithful
on sheaves (thm-weil-pbc-site-comparison), hence reflects zero cohomology and the
lower bound of H U_Y L. The canonical B, comparison adjunction, chosen etale
adjunction (thm-amb-etale-exceptional-adjoint), and comparison full faithfulness
therefore make the displayed Hom-chain function bijective on the stated domains.
3. Its inverse at the identity gives the relative counit. Reversing the four
bijections writes it as B inverse, followed by C_Y of the etale counit, followed
by the comparison counit tau. This identifies the actual specified counit.
4. rho is C_X H applied to eta_Y,K, an isomorphism by site comparison. Naturality
of B moves F_p(rho) across it. Naturality of the etale counit then moves eta;
the comparison triangle tau C_Y(eta) = identity proves the counit equation.
5. For compatible a_e and a_p, put b_e = adj_e(a_e). Naturality of B and step 4
show that the inverse pro-etale transpose of C_X(b_e) followed by rho equals a_p.
Injectivity gives the asserted equality of transposes.
6. Precomposition in the Hom chain gives naturality in J; postcomposition and
naturality of eta give naturality in K. All sources have their identity etale
witness, and no ambient unbounded exceptional adjunction is used.
-/
theorem boundedSiteRightAdjoint_plus
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aY = aX) (c : Compactification f) (d : ℕ)
    (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))
    (H : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c ⊣ H)
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    _root_.DerivedCategory.TStructure.t.plus (H.obj ((R(ν_*(Y)[ModuleCat.{u + 1}
      P.Coefficient])).obj L.obj)) := by
  sorry

/-- Bijectivity of the specified Hom-chain function on its bounded etale-origin domains.
Source: Stacks Tag 0B65; blueprint thm-sf-ambient-adjoint-class, Hom chain
(blueprint: lem-pur-bounded-site-adjunction-transpose).

Proof:
1. Exact etale and pro-etale extension by zero (lem-weil-pbc-extension-by-zero-exact,
lem-weil-extension-by-zero-exact) gives the open comparison degreewise. Apply the
named proper counit mate (lem-weil-pbc-comparison-direct-image-canonical-mate) to
its bounded-below input. Their composite is precisely B, natural in every input.
2. thm-sf-ambient-adjoint-class gives boundedness of C_X H U_Y L. Exact comparison
commutes with cohomology (lem-sf-comparison-pullback-exact) and is fully faithful
on sheaves (thm-weil-pbc-site-comparison), hence reflects zero cohomology and the
lower bound of H U_Y L. The canonical B, comparison adjunction, chosen etale
adjunction (thm-amb-etale-exceptional-adjoint), and comparison full faithfulness
therefore make the displayed Hom-chain function bijective on the stated domains.
3. Its inverse at the identity gives the relative counit. Reversing the four
bijections writes it as B inverse, followed by C_Y of the etale counit, followed
by the comparison counit tau. This identifies the actual specified counit.
4. rho is C_X H applied to eta_Y,K, an isomorphism by site comparison. Naturality
of B moves F_p(rho) across it. Naturality of the etale counit then moves eta;
the comparison triangle tau C_Y(eta) = identity proves the counit equation.
5. For compatible a_e and a_p, put b_e = adj_e(a_e). Naturality of B and step 4
show that the inverse pro-etale transpose of C_X(b_e) followed by rho equals a_p.
Injectivity gives the asserted equality of transposes.
6. Precomposition in the Hom chain gives naturality in J; postcomposition and
naturality of eta give naturality in K. All sources have their identity etale
witness, and no ambient unbounded exceptional adjunction is used.
-/
theorem boundedSiteTranspose_bijective
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aY = aX) (c : Compactification f) (d : ℕ)
    (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))
    (H : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c ⊣ H)
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    Function.Bijective (boundedSiteTranspose P.Coefficient c H adj J L.obj) := by
  sorry

/-- The unique equivalence whose forward map is the specified Hom-chain function.
Its inverse is fixed by bijectivity, not chosen independently.
Source: Stacks Tag 0B65; blueprint bounded Hom chain
(blueprint: lem-pur-bounded-site-adjunction-transpose). -/
def boundedSiteHomEquiv
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aY = aX) (c : Compactification f) (d : ℕ)
    (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))
    (H : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c ⊣ H)
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).obj
      (D(ν^*(X)[ModuleCat.{u + 1} P.Coefficient]).obj J.obj) ⟶ L.obj) ≃
      (D(ν^*(X)[ModuleCat.{u + 1} P.Coefficient]).obj J.obj ⟶ D(ν^*(X)[ModuleCat.{u + 1}
      P.Coefficient]).obj (H.obj ((R(ν_*(Y)[ModuleCat.{u + 1} P.Coefficient])).obj L.obj))) :=
  Equiv.ofBijective (boundedSiteTranspose P.Coefficient c H adj J L.obj)
    (boundedSiteTranspose_bijective P aX aY f hf c d hd H adj J L)

/-- The actual bounded etale intermediate object, with its proved lower bound.
Source: blueprint bounded Hom chain
(blueprint: lem-pur-bounded-site-adjunction-transpose). -/
def boundedSiteRightAdjointPlus
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aY = aX) (c : Compactification f) (d : ℕ)
    (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))
    (H : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c ⊣ H)
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1}
      P.Coefficient))) : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      P.Coefficient)) :=
  ⟨H.obj ((R(ν_*(Y)[ModuleCat.{u + 1} P.Coefficient])).obj L.obj),
    boundedSiteRightAdjoint_plus P aX aY f hf c d hd H adj L⟩

/-- The relative counit is the inverse specified transpose of the identity, using
the identity etale-origin witness for the actual right-adjoint object.
Source: Stacks Tag 0B65; blueprint bounded Hom chain
(blueprint: lem-pur-bounded-site-adjunction-transpose). -/
def boundedSiteCounit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aY = aX) (c : Compactification f) (d : ℕ)
    (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))
    (H : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c ⊣ H)
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).obj
      (D(ν^*(X)[ModuleCat.{u + 1} P.Coefficient]).obj (H.obj ((R(ν_*(Y)[ModuleCat.{u + 1}
      P.Coefficient])).obj L.obj))) ⟶ L.obj :=
  (boundedSiteHomEquiv P aX aY f hf c d hd H adj
    (boundedSiteRightAdjointPlus P aX aY f hf c d hd H adj L) L).symm (𝟙 _)

/-- The normalized counit equation and compatibility of all specified transposes.
Source: Stacks Tag 0B65; blueprint thm-sf-ambient-adjoint-class, Hom chain
(blueprint: lem-pur-bounded-site-adjunction-transpose).

Proof:
1. Exact etale and pro-etale extension by zero (lem-weil-pbc-extension-by-zero-exact,
lem-weil-extension-by-zero-exact) gives the open comparison degreewise. Apply the
named proper counit mate (lem-weil-pbc-comparison-direct-image-canonical-mate) to
its bounded-below input. Their composite is precisely B, natural in every input.
2. thm-sf-ambient-adjoint-class gives boundedness of C_X H U_Y L. Exact comparison
commutes with cohomology (lem-sf-comparison-pullback-exact) and is fully faithful
on sheaves (thm-weil-pbc-site-comparison), hence reflects zero cohomology and the
lower bound of H U_Y L. The canonical B, comparison adjunction, chosen etale
adjunction (thm-amb-etale-exceptional-adjoint), and comparison full faithfulness
therefore make the displayed Hom-chain function bijective on the stated domains.
3. Its inverse at the identity gives the relative counit. Reversing the four
bijections writes it as B inverse, followed by C_Y of the etale counit, followed
by the comparison counit tau. This identifies the actual specified counit.
4. rho is C_X H applied to eta_Y,K, an isomorphism by site comparison. Naturality
of B moves F_p(rho) across it. Naturality of the etale counit then moves eta;
the comparison triangle tau C_Y(eta) = identity proves the counit equation.
5. For compatible a_e and a_p, put b_e = adj_e(a_e). Naturality of B and step 4
show that the inverse pro-etale transpose of C_X(b_e) followed by rho equals a_p.
Injectivity gives the asserted equality of transposes.
6. Precomposition in the Hom chain gives naturality in J; postcomposition and
naturality of eta give naturality in K. All sources have their identity etale
witness, and no ambient unbounded exceptional adjunction is used.
-/
theorem boundedSiteAdjunctionTranspose
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aY = aX) (c : Compactification f) (d : ℕ)
    (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))
    (H : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c ⊣ H)
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (hHK : _root_.DerivedCategory.TStructure.t.plus (H.obj K.obj)) :
    IsIso (boundedSiteRho P.Coefficient H K.obj) ∧
    ((compactSupportSiteComparison P.Coefficient c).inv.app ⟨H.obj K.obj, hHK⟩ ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).map
      (boundedSiteRho P.Coefficient H K.obj) ≫
        boundedSiteCounit P aX aY f hf c d hd H adj
          ((siteComparisonDerivedPullbackPlus Y P.Coefficient).obj K) =
      D(ν^*(Y)[ModuleCat.{u + 1} P.Coefficient]).map (adj.counit.app K.obj)) ∧
    (∀ (a_e : (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient)
      c).obj J.obj ⟶ K.obj)
      (a_p : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).obj
      (D(ν^*(X)[ModuleCat.{u + 1} P.Coefficient]).obj J.obj) ⟶ D(ν^*(Y)[ModuleCat.{u + 1}
      P.Coefficient]).obj K.obj),
      (compactSupportSiteComparison P.Coefficient c).inv.app J ≫ a_p = D(ν^*(Y)[ModuleCat.{u + 1}
      P.Coefficient]).map a_e →
      boundedSiteHomEquiv P aX aY f hf c d hd H adj J
          ((siteComparisonDerivedPullbackPlus Y P.Coefficient).obj K) a_p =
        D(ν^*(X)[ModuleCat.{u + 1} P.Coefficient]).map ((adj.homEquiv J.obj K.obj) a_e) ≫
          boundedSiteRho P.Coefficient H K.obj) := by
  sorry

/-- Naturality of the specified transpose in both variables, and of rho in K.
Source: Stacks Tag 0B65; blueprint thm-sf-ambient-adjoint-class, Hom chain
(blueprint: lem-pur-bounded-site-adjunction-transpose).

Proof:
1. Exact etale and pro-etale extension by zero (lem-weil-pbc-extension-by-zero-exact,
lem-weil-extension-by-zero-exact) gives the open comparison degreewise. Apply the
named proper counit mate (lem-weil-pbc-comparison-direct-image-canonical-mate) to
its bounded-below input. Their composite is precisely B, natural in every input.
2. thm-sf-ambient-adjoint-class gives boundedness of C_X H U_Y L. Exact comparison
commutes with cohomology (lem-sf-comparison-pullback-exact) and is fully faithful
on sheaves (thm-weil-pbc-site-comparison), hence reflects zero cohomology and the
lower bound of H U_Y L. The canonical B, comparison adjunction, chosen etale
adjunction (thm-amb-etale-exceptional-adjoint), and comparison full faithfulness
therefore make the displayed Hom-chain function bijective on the stated domains.
3. Its inverse at the identity gives the relative counit. Reversing the four
bijections writes it as B inverse, followed by C_Y of the etale counit, followed
by the comparison counit tau. This identifies the actual specified counit.
4. rho is C_X H applied to eta_Y,K, an isomorphism by site comparison. Naturality
of B moves F_p(rho) across it. Naturality of the etale counit then moves eta;
the comparison triangle tau C_Y(eta) = identity proves the counit equation.
5. For compatible a_e and a_p, put b_e = adj_e(a_e). Naturality of B and step 4
show that the inverse pro-etale transpose of C_X(b_e) followed by rho equals a_p.
Injectivity gives the asserted equality of transposes.
6. Precomposition in the Hom chain gives naturality in J; postcomposition and
naturality of eta give naturality in K. All sources have their identity etale
witness, and no ambient unbounded exceptional adjunction is used.
-/
theorem boundedSiteAdjunctionTranspose_naturality
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aY = aX) (c : Compactification f) (d : ℕ)
    (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))
    (H : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c ⊣ H) :
    (∀ (J J' : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      P.Coefficient))) (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u +
      1} P.Coefficient)))
      (b : J'.obj ⟶ J.obj)
      (z : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).obj
      (D(ν^*(X)[ModuleCat.{u + 1} P.Coefficient]).obj J.obj) ⟶ L.obj),
      boundedSiteTranspose P.Coefficient c H adj J' L.obj
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).map
      (D(ν^*(X)[ModuleCat.{u + 1} P.Coefficient]).map b) ≫ z) =
        D(ν^*(X)[ModuleCat.{u + 1} P.Coefficient]).map b ≫ boundedSiteTranspose P.Coefficient c H
      adj J L.obj z) ∧
    (∀ (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (L L' : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1}
      P.Coefficient)))
      (b : L.obj ⟶ L'.obj)
      (z : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).obj
      (D(ν^*(X)[ModuleCat.{u + 1} P.Coefficient]).obj J.obj) ⟶ L.obj),
      boundedSiteTranspose P.Coefficient c H adj J L'.obj (z ≫ b) =
        boundedSiteTranspose P.Coefficient c H adj J L.obj z ≫
          D(ν^*(X)[ModuleCat.{u + 1} P.Coefficient]).map (H.map ((R(ν_*(Y)[ModuleCat.{u + 1}
      P.Coefficient])).map b))) ∧
    (∀ (K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1}
      P.Coefficient))) (b : K.obj ⟶ K'.obj),
      boundedSiteRho P.Coefficient H K.obj ≫
          D(ν^*(X)[ModuleCat.{u + 1} P.Coefficient]).map (H.map ((R(ν_*(Y)[ModuleCat.{u + 1}
      P.Coefficient])).map (D(ν^*(Y)[ModuleCat.{u + 1} P.Coefficient]).map b))) =
        D(ν^*(X)[ModuleCat.{u + 1} P.Coefficient]).map (H.map b) ≫ boundedSiteRho P.Coefficient H
      K'.obj) := by
  sorry

end AlgebraicGeometry.ProEtale
