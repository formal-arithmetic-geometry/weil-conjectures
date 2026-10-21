/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.AlgebraicGeometry.SupportQuotientFlat
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf

import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.Paper.ComparisonPullbackExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Functorial pullback of constant support quotients

Source: Stacks Project, Tag 03Q1, especially (1) and (3), and the ordinary comparison
in the final paragraph of blueprint `lem-pur-kunneth-supported.proof.md`
(blueprint: lem-pur-support-quotient-pair-pullback).

The quotients and quotient maps are exactly those of `SupportQuotientFlat`. The
fixed-scalar presentation is the same presentation used by that dependency: its canonical
realization identifies it with ordinary modules over the constant ring sheaf. The helper
structures only bundle the schemes, closed immersions and factorization hypotheses.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The input closed pair, including precisely the quasi-compact-complement hypothesis.
Source: support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
structure SupportQuotientPair where
  T : Scheme.{u}
  C : Scheme.{u}
  a : C ⟶ T
  closed : IsClosedImmersion a
  qc : QuasiCompact a.openComplement.ι

attribute [instance] SupportQuotientPair.closed SupportQuotientPair.qc

/-- A scheme morphism carrying the source closed subscheme into the target, with its
scheme-theoretic factorization, rather than merely an inclusion of underlying sets.
Source: support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
structure SupportQuotientPairMap (P Q : SupportQuotientPair.{u}) where
  f : P.T ⟶ Q.T
  s : P.C ⟶ Q.C
  w : s ≫ Q.a = P.a ≫ f

/-- Identity input pair map.
Source: the identity clause of the support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
def SupportQuotientPairMap.id (P : SupportQuotientPair.{u}) : SupportQuotientPairMap P P :=
  ⟨𝟙 P.T, 𝟙 P.C, (Category.id_comp P.a).trans (Category.comp_id P.a).symm⟩

/-- Composite input pair map, using the composite of the supplied factorizations.
Source: the composition clause of the support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
def SupportQuotientPairMap.comp {P Q R : SupportQuotientPair.{u}}
    (g : SupportQuotientPairMap P Q) (f : SupportQuotientPairMap Q R) :
    SupportQuotientPairMap P R :=
  ⟨g.f ≫ f.f, g.s ≫ f.s,
    (Category.assoc g.s f.s R.a).trans
      ((congrArg (fun k ↦ g.s ≫ k) f.w).trans
        ((Category.assoc g.s Q.a f.f).symm.trans
          ((congrArg (fun k ↦ k ≫ f.f) g.w).trans (Category.assoc P.a g.f f.f))))⟩

/-- The ordinary etale pair-map family type; all objects and arrows are the recorded ones.
Source: support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
abbrev EtaleSupportQuotientPairMaps (A : Type u) [CommRing A] [Finite A] :=
  ∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q),
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).obj
      (etaleSupportQuotient A Q.a) ⟶ etaleSupportQuotient A P.a

/-- The ordinary pro-etale pair-map family type, in the same coefficient realization.
Source: support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
abbrev ProEtaleSupportQuotientPairMaps (A : Type u) [CommRing A] [Finite A] :=
  ∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q),
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).obj
      (proEtaleSupportQuotient A Q.a) ⟶ proEtaleSupportQuotient A P.a

/-- The constant etale germ, obtained from constant sections on the final object.
Source: Tag 03Q1 and the normalized stalk clause of `lem-pur-support-quotient-flat`
(blueprint: lem-pur-support-quotient-pair-pullback). -/
def supportQuotientEtaleConstantGerm (A : Type u) [CommRing A] (T : Scheme.{u})
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :=
  (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
    (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))).app
      (op (Etale.mk (𝟙 T))) ≫
    (pointSmallEtale t).toPresheafFiber (Etale.mk (𝟙 T))
      (Over.homMk t (Category.comp_id t))
      ((constantSheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
          (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))).obj

/-- Unique normalized ordinary support-quotient maps, their stalks, Cartesian
isomorphisms, identities, compositions and the normalized etale/pro-etale comparison.
Source: Tag 03Q1 (1), (3), and the final paragraph of the blueprint proof of
`lem-pur-kunneth-supported` (blueprint: lem-pur-support-quotient-pair-pullback).

Proof (the node's eight steps):
1. Exact constant-coefficient etale pullback (`prop-weil-pbc-inverse-image-modules-exact`)
   carries the defining cokernel presentation to a cokernel presentation, with epic
   pulled-back quotient map. Its coefficient identification preserves constant sections.
2. The defining relation maps to zero in the target quotient: on its support the source
   extension-by-zero stalk is zero, by the factorization, inverse-image stalk formula and
   extension-by-zero stalk formula (`lem-weil-pbc-inverse-image-stalk-germ`,
   `lem-weil-pbc-extension-by-zero-stalks`); off the support the target stalk is zero
   (`lem-pur-support-quotient-flat`). Exact stalks and conservativity applied to the image
   give equality to zero as an ordinary module morphism
   (`prop-weil-pbc-geometric-stalks-exact`, `lemma-weil-pbc-geometric-stalk-conservative`).
3. The cokernel universal property gives the unique etale map. Its normalized stalk on
   the closed support is the identity, since both quotient maps preserve the constant
   generator; off the support its target is zero.
4. For a Cartesian closed subscheme the two stalks are simultaneously A or zero; thus
   the etale map is an isomorphism by geometric-stalk conservativity.
5. Naturality of `lem-weil-pbc-comparison-pullback` at every constant section from the
   final sheaf, and finite-product preservation, normalize its component on coefficients.
   Uniqueness of sheafification makes this component the constant-section identity.
   The same argument normalizes identity and composition comparisons; the pro-etale
   coefficient-composition equation is `lem-pur-proetale-constant-ring-composition`.
6. Define the pro-etale map by transporting the etale map through the quotient
   comparisons of `lem-pur-support-quotient-flat` and the pullback comparison. Their
   normalizations give the quotient equation and the comparison square. Exact comparison
   (`lem-sf-comparison-pullback-exact`) preserves the quotient epimorphism, giving uniqueness.
7. In the Cartesian case all factors in this transport are isomorphisms, so is the map.
8. The identity satisfies the quotient equation. The composite of two pair maps also
   satisfies it, using the coefficient-normalized composition comparison and the composed
   factorization. Uniqueness gives both equalities of ordinary sheaf morphisms.
No flatness of a scheme map, reducedness, or pro-etale geometric-stalk conservativity is used.
-/
theorem supportQuotient_pair_pullback (A : Type u) [CommRing A] [Finite A] :
    ∃ (cEt : EtaleSupportQuotientPairMaps A) (cPro : ProEtaleSupportQuotientPairMaps A),
      (∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q),
        (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).map
            (etaleSupportQuotientMap A Q.a) ≫ cEt f =
          (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).hom.app
            (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)) ≫
              etaleSupportQuotientMap A P.a ∧
        ∀ d, (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).map
            (etaleSupportQuotientMap A Q.a) ≫ d =
          (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).hom.app
            (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)) ≫
              etaleSupportQuotientMap A P.a → d = cEt f) ∧
      (∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q),
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).map
            (proEtaleSupportQuotientMap A Q.a) ≫ cPro f =
          proEtaleConstantInverseImageMap f.f
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)) ≫
              proEtaleSupportQuotientMap A P.a ∧
        ∀ d, (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).map
            (proEtaleSupportQuotientMap A Q.a) ≫ d =
          proEtaleConstantInverseImageMap f.f
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)) ≫
              proEtaleSupportQuotientMap A P.a → d = cPro f) ∧
      (∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q)
          (Ω : Type u) [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ P.T),
        (t (IsLocalRing.closedPoint Ω) ∈ Set.range P.a →
          ∃ (eS : (pointSmallEtale t).sheafFiber.obj
              ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).obj
                (etaleSupportQuotient A Q.a)) ≅
              ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))
            (eT : (pointSmallEtale t).sheafFiber.obj (etaleSupportQuotient A P.a) ≅
              ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)),
            supportQuotientEtaleConstantGerm A P.T t ≫
              (pointSmallEtale t).sheafFiber.map
                ((Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).inv.app
                  (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))) ≫
              (pointSmallEtale t).sheafFiber.map
                ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).map
                  (etaleSupportQuotientMap A Q.a)) ≫ eS.hom = 𝟙 _ ∧
            supportQuotientEtaleConstantGerm A P.T t ≫
              (pointSmallEtale t).sheafFiber.map (etaleSupportQuotientMap A P.a) ≫
                eT.hom = 𝟙 _ ∧
            (pointSmallEtale t).sheafFiber.map (cEt f) ≫ eT.hom = eS.hom) ∧
        (t (IsLocalRing.closedPoint Ω) ∉ Set.range P.a →
          IsZero ((pointSmallEtale t).sheafFiber.obj (etaleSupportQuotient A P.a)) ∧
            (pointSmallEtale t).sheafFiber.map (cEt f) = 0)) ∧
      (∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q),
        IsPullback f.s P.a Q.a f.f → IsIso (cEt f) ∧ IsIso (cPro f)) ∧
      (∀ P : SupportQuotientPair.{u},
        cEt (SupportQuotientPairMap.id P) =
          (ProEtale.supportSiteEtaleComparisonId
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) P.T).hom.app
              (etaleSupportQuotient A P.a) ∧
        cPro (SupportQuotientPairMap.id P) =
          (ProEtale.supportSiteProEtaleComparisonId
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) P.T).hom.app
              (proEtaleSupportQuotient A P.a)) ∧
      (∀ {P Q R : SupportQuotientPair.{u}} (g : SupportQuotientPairMap P Q)
          (f : SupportQuotientPairMap Q R),
        cEt (g.comp f) =
          (ProEtale.supportSiteEtaleComparisonComp
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g.f f.f).hom.app
              (etaleSupportQuotient A R.a) ≫
            (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g.f).map (cEt f) ≫
              cEt g ∧
        cPro (g.comp f) =
          (ProEtale.supportSiteProEtaleComparisonComp
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g.f f.f).hom.app
              (proEtaleSupportQuotient A R.a) ≫
            (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g.f).map
              (cPro f) ≫ cPro g) ∧
      (∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q)
          (α : (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Q.T).obj
              (etaleSupportQuotient A Q.a) ≅ proEtaleSupportQuotient A Q.a)
          (α' : (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) P.T).obj
              (etaleSupportQuotient A P.a) ≅ proEtaleSupportQuotient A P.a),
        (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Q.T).map
              (etaleSupportQuotientMap A Q.a) ≫ α.hom =
          supportQuotientConstantComparison A (T := Q.T) ≫
            proEtaleSupportQuotientMap A Q.a →
        (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) P.T).map
              (etaleSupportQuotientMap A P.a) ≫ α'.hom =
          supportQuotientConstantComparison A (T := P.T) ≫
            proEtaleSupportQuotientMap A P.a →
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).map α.hom ≫
            cPro f =
          (ProEtale.supportSiteComparisonCoefficientPullbackIso
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).inv.app
              (etaleSupportQuotient A Q.a) ≫
            (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) P.T).map (cEt f) ≫ α'.hom) := by
  sorry

end AlgebraicGeometry.Scheme
