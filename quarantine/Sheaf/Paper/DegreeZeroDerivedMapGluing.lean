/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.TruncationDescends
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Sites.CoverLifting
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.SfCommonStageWeilCohomology

/-!
# Unique gluing of derived maps locally concentrated in degree zero

Source: Stacks Project, Derived Categories, Tag 06XS; Modules on Sites, Tag 03EM;
Sites, Tag 04TQ; Homology, Tag 0118 (blueprint: lem-pur-degree-zero-derived-map-gluing).

The auxiliary predicates only spell out the conclusion, using the actual exact inverse
images and their canonical composition isomorphisms. They assume no descent property.
Both small sites use fixed-ring module sheaves. For finite coefficients the canonical
coefficient realization identifies this with modules over the constant ring sheaf, as in
`def-weil-pbc-proetale-modules`. No new derived category or restriction is constructed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u uB vB wB wI

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.DegreeZeroMapGluing

section Formulas

variable (B : Scheme.{u} → Type uB) [∀ X, Category.{vB} (B X)]
  [∀ X, Abelian (B X)] [∀ X, HasDerivedCategory.{wB} (B X)]
  (r : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → B Y ⥤ B X)
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (r f).Additive]
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteLimits (r f)]
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteColimits (r f)]
  (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), r (f ≫ g) ≅ r g ⋙ r f)

/-- The canonical comparison for two restrictions, including the equality of the
composite open immersion with the smaller open's immersion. Source: Stacks 04IX and
05RU (blueprint: lem-pur-degree-zero-derived-map-gluing). -/
def openComp (T : Scheme.{u}) {U V : T.Opens} (h : U ≤ V) :
    (r V.ι).mapDerivedCategory ⋙ (r (T.homOfLE h)).mapDerivedCategory ≅
      (r U.ι).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (r V.ι) (r (T.homOfLE h))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((c (T.homOfLE h) V.ι).symm ≪≫
        eqToIso (congrArg (fun f ↦ r f) (Scheme.homOfLE_ι T h)))

/-- Restrict a local map to a smaller open and identify its endpoints with the
restrictions of the global endpoints. Source: Stacks 04IX, 05RU
(blueprint: lem-pur-degree-zero-derived-map-gluing). -/
def onSmallerOpen (T : Scheme.{u}) (M N : DerivedCategory (B T))
    {U V : T.Opens} (h : U ≤ V)
    (a : (r V.ι).mapDerivedCategory.obj M ⟶ (r V.ι).mapDerivedCategory.obj N) :
    (r U.ι).mapDerivedCategory.obj M ⟶ (r U.ι).mapDerivedCategory.obj N :=
  (openComp B r c T h).inv.app M ≫
    (r (T.homOfLE h)).mapDerivedCategory.map a ≫ (openComp B r c T h).hom.app N

/-- The good-truncation identifications on open subschemes of `T`, including `T` itself
via its identity immersion. Their normalization is the explicit roof through `truncLE 0`;
its degree-zero map is cycles modulo boundaries. Naturality and restriction use the
existing single and homology comparisons. Source: Stacks 0118, 05RU and 06XS
(blueprint: lem-pur-degree-zero-derived-map-gluing). -/
def HasCanonicalIdentifications (T : Scheme.{u}) : Prop :=
  ∃ e : ∀ (X : Scheme.{u}) (j : X ⟶ T), IsOpenImmersion j →
      ∀ K : DerivedCategory (B X), DerivedCategory.homologyConcentratedIn 0 0 K →
        (K ≅ (DerivedCategory.singleFunctor (B X) 0).obj
          ((DerivedCategory.homologyFunctor (B X) 0).obj K)),
    (∀ (X : Scheme.{u}) (j : X ⟶ T) (hj : IsOpenImmersion j)
      (K L : DerivedCategory (B X))
      (hK : DerivedCategory.homologyConcentratedIn 0 0 K)
      (hL : DerivedCategory.homologyConcentratedIn 0 0 L) (a : K ⟶ L),
      a ≫ (e X j hj L hL).hom = (e X j hj K hK).hom ≫
        (DerivedCategory.singleFunctor (B X) 0).map
          ((DerivedCategory.homologyFunctor (B X) 0).map a)) ∧
    (∀ (X : Scheme.{u}) (j : X ⟶ T) (hj : IsOpenImmersion j)
      (Y : Scheme.{u}) (f : Y ⟶ X) (_hf : IsOpenImmersion f)
      (hfj : IsOpenImmersion (f ≫ j)) (K : DerivedCategory (B X))
      (hK : DerivedCategory.homologyConcentratedIn 0 0 K)
      (hRK : DerivedCategory.homologyConcentratedIn 0 0 ((r f).mapDerivedCategory.obj K)),
      (r f).mapDerivedCategory.map (e X j hj K hK).hom ≫
        ((r f).mapDerivedCategorySingleFunctor 0).hom.app
          ((DerivedCategory.homologyFunctor (B X) 0).obj K) ≫
        (DerivedCategory.singleFunctor (B Y) 0).map
          (((r f).mapDerivedCategoryHomologyFunctorIso 0).hom.app K) =
      (e Y (f ≫ j) hfj ((r f).mapDerivedCategory.obj K) hRK).hom) ∧
    (∀ (X : Scheme.{u}) (j : X ⟶ T) (hj : IsOpenImmersion j)
      (K : CochainComplex (B X) ℤ)
      (hK : DerivedCategory.homologyConcentratedIn 0 0 (DerivedCategory.Q.obj K)),
      ∃ p : K.truncLE 0 ⟶ (CochainComplex.singleFunctor (B X) 0).obj (K.homology 0),
        (p.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (K.homology 0)).hom =
          (K.truncLEXIsoCycles 0).hom ≫ K.homologyπ 0) ∧
        (∀ a : ℤ, a ≠ 0 → p.f a = 0) ∧
        IsIso (DerivedCategory.Q.map (K.ιTruncLE 0)) ∧ IsIso (DerivedCategory.Q.map p) ∧
        DerivedCategory.Q.map (K.ιTruncLE 0) ≫
            (e X j hj (DerivedCategory.Q.obj K) hK).hom =
          DerivedCategory.Q.map p ≫ (DerivedCategory.singleFunctor (B X) 0).map
            ((DerivedCategory.homologyFunctorFactors (B X) 0).inv.app K))

/-- The full conclusion of degree-zero derived-map gluing, with the restriction bijection
written as compatibility iff a unique preimage exists. Thus no choice of a compatibility
proof is needed to define a map into a subtype. The last two clauses identify this with
sheaf-map gluing through `H⁰` and state the equality test explicitly. Source: Stacks 06XS,
03EM and 04TQ (blueprint: lem-pur-degree-zero-derived-map-gluing). -/
def Conclusion (T : Scheme.{u}) {I : Type wI} (U : I → T.Opens) : Prop :=
  HasCanonicalIdentifications B r T ∧
  ∀ M N : DerivedCategory (B T),
    (∀ i : I, DerivedCategory.homologyConcentratedIn 0 0
      ((r (U i).ι).mapDerivedCategory.obj M) ∧
      DerivedCategory.homologyConcentratedIn 0 0 ((r (U i).ι).mapDerivedCategory.obj N)) →
    DerivedCategory.homologyConcentratedIn 0 0 M ∧
    DerivedCategory.homologyConcentratedIn 0 0 N ∧
    (∀ a : ∀ i : I, (r (U i).ι).mapDerivedCategory.obj M ⟶
        (r (U i).ι).mapDerivedCategory.obj N,
      (∀ i j : I,
        onSmallerOpen B r c T M N (inf_le_left : U i ⊓ U j ≤ U i) (a i) =
          onSmallerOpen B r c T M N (inf_le_right : U i ⊓ U j ≤ U j) (a j)) ↔
      ∃! b : M ⟶ N, ∀ i : I, (r (U i).ι).mapDerivedCategory.map b = a i) ∧
    Function.Bijective (fun a : M ⟶ N ↦ (DerivedCategory.homologyFunctor (B T) 0).map a) ∧
    (∀ (a : M ⟶ N) (i : I),
      (r (U i).ι).map ((DerivedCategory.homologyFunctor (B T) 0).map a) ≫
          ((r (U i).ι).mapDerivedCategoryHomologyFunctorIso 0).hom.app N =
        ((r (U i).ι).mapDerivedCategoryHomologyFunctorIso 0).hom.app M ≫
          (DerivedCategory.homologyFunctor (B (U i).toScheme) 0).map
            ((r (U i).ι).mapDerivedCategory.map a)) ∧
    (∀ a b : M ⟶ N,
      (∀ i : I, (r (U i).ι).mapDerivedCategory.map a =
        (r (U i).ι).mapDerivedCategory.map b) ↔ a = b)

end Formulas

/-- Unique gluing on both small sites for finite commutative coefficients.
Source: Stacks 06XS, 03EM, 04TQ, 0118
(blueprint: lem-pur-degree-zero-derived-map-gluing).

Proof:
1. The etale localization equivalence (lem-weil-pbc-etale-site-localization-open) and
   the pro-etale localization equivalence (lem-weil-proetale-weakly-etale-localization)
   identify open restriction with localized-site restriction. Constant coefficients
   restrict to the same coefficients (lem-weil-pbc-site-constant-restriction). The given
   Zariski cover is a cover on either site; for pro-etale covers refine affine opens by
   affine opens and take finite subcovers (lem-weil-pbc-affine-opens-basis and
   lem-weil-pbc-affine-scheme-qcqs).
2. Restriction is exact (lem-pur-site-restriction-module-adjunction-exact), so it
   induces the termwise derived functor (lem-sf-exact-functor-derived-triangulated).
   Kernels, images and quotients commute with it. Hence so do all cohomology sheaves,
   naturally for maps and inverses of quasi-isomorphisms.
3. A cohomology sheaf vanishing on the cover is zero: its sections over any site
   object inject into the product of its sections on the pulled-back cover. This is
   the sheaf equalizer axiom (def-weil-pbc-sites-and-cohomology), also for an empty cover.
4. For a representing complex K use c : truncLE K 0 → K and p to H⁰(K)[0], with
   p in degree zero the quotient of cycles by boundaries and zero elsewhere. Both
   are quasi-isomorphisms by concentration; the identification is Q(c)⁻¹ Q(p).
5. Kernels and quotient maps are natural; their natural transformations descend
   through localization (lem-weil-pbc-truncation-descends and
   lem-weil-pbc-localization-universal-property). This proves independence of the
   representative, naturality and compatibility with restriction, including iteration.
6. The single functor is fully faithful (lem-weil-pbc-derived-single-fully-faithful).
   Conjugation by the normalized identifications identifies every derived map with
   its H⁰ sheaf map. The single and homology comparisons give the restriction square.
7. Compatible local sheaf maps glue uniquely (lem-pur-sheaf-hom-cover-gluing).
   Transport through step 6 proves the restriction bijection and the equality test.
   For the empty scheme the empty-cover sheaf axiom makes all sheaves zero, and all
   derived objects are zero; both sides of the bijection are singleton sets. -/
theorem degreeZeroDerivedMapGluing (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) {I : Type wI} (U : I → T.Opens) (hU : iSup U = ⊤) :
    Conclusion (fun X : Scheme.{u} ↦ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (fun {_ _} f ↦ Etale.upperStar (ModuleCat.{u + 1} A) f)
      (fun {_ _ _} f g ↦ Etale.upperStarComp (ModuleCat.{u + 1} A) f g) T U ∧
    Conclusion (fun X : Scheme.{u} ↦ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      (fun {_ _} f ↦ ProEtale.upperStar (ModuleCat.{u + 1} A) f)
      (fun {_ _ _} f g ↦ ProEtale.upperStarComp (ModuleCat.{u + 1} A) f g) T U := sorry

end AlgebraicGeometry.DegreeZeroMapGluing
