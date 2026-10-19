/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.SixFunctors.ConnectedEtalePerfectConstant
public import Sheaf.SixFunctors.ProperBaseChangeModules
public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsDerived
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonCounit
import Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquare
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
import Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact
import Sheaf.AlgebraicGeometry.TorsionStalkProEtaleResolutionMap
import Sheaf.CategoryTheory.Adjunction.CoefficientExchange
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Sections at a pro-etale geometric point

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-cor-pbc-torsion-stalk/sk-cor-pbc-torsion-stalk-proetale-point.md
(blueprint: det-pbc-torsion-stalk-proetale-point).

The section comparison is the actual comparison-adjunction unit. The stalk
identification is normalized on every pointed etale neighbourhood. The final
identity compares the actual derived exchange maps through these identifications.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

/-- Evaluation at the final pro-etale object of a geometric point.
Source: blueprint, sections at a pro-etale geometric point, clause 1
(blueprint: det-pbc-torsion-stalk-proetale-point). -/
noncomputable abbrev torsionPointProEtaleSections
    (Ω : Type u) [Field Ω] (Λ : Type (u + 1)) [CommRing Λ] :=
  ProEtale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Scheme.ProEt.mk (𝟙 (Spec (.of Ω))))

/-- The canonical point-section comparison, given by the comparison adjunction's unit
at the final etale object; the comparison direct image is restriction of presheaves.
Source: blueprint, sections at a pro-etale geometric point, clause 2
(blueprint: det-pbc-torsion-stalk-proetale-point). -/
noncomputable def torsionPointSectionsComparison
    (Ω : Type u) [Field Ω] (Λ : Type (u + 1)) [CommRing Λ] :
    Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω)) ⟶
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) (Spec (.of Ω)) ⋙
        torsionPointProEtaleSections Ω Λ where
  app F := ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ)
    (Spec (.of Ω))).unit.app F).hom.app (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))
  naturality F G φ := by
    exact NatTrans.congr_app
      (Sheaf.hom_ext_iff.1
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ)
          (Spec (.of Ω))).unit.naturality φ))
      (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))

/-- A section on a pointed etale neighbourhood pulled back to the geometric point:
apply the inverse-image unit, then restrict along the pointed graph into its pullback.
Source: blueprint, sections at a pro-etale geometric point, clause 3; Stacks 03Q1
(blueprint: det-pbc-torsion-stalk-proetale-point). -/
noncomputable def torsionPointPulledBackSection
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (Λ : Type (u + 1)) [CommRing Λ] {Y : Scheme.{u}}
    (barY : Spec (.of Ω) ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : Y.Etale) (x : (Scheme.pointSmallEtale barY).fiber.obj U) :
    F.obj.obj (op U) ⟶
      (Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) barY).obj F) :=
  ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) barY).unit.app F).hom.app
      (op U) ≫
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) barY).obj F).obj.map
      (MorphismProperty.Over.homMk
        (A := Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
        (B := (MorphismProperty.Over.pullback @Etale ⊤ barY).obj U)
        (pullback.lift x.left (𝟙 (Spec (.of Ω)))
          ((Over.w x).trans (Category.id_comp barY).symm)) (by simp)).op

section Constructions

variable (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (Λ : Type (u + 1)) [CommRing Λ]
  [PreservesFiniteLimits (torsionPointProEtaleSections Ω Λ)]
  [PreservesFiniteColimits (torsionPointProEtaleSections Ω Λ)]
  [(Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).IsEquivalence]

/-- The point comparison extended termwise, using the actual comparison unit.
Source: blueprint, sections at a pro-etale geometric point, clause 2
(blueprint: det-pbc-torsion-stalk-proetale-point). -/
noncomputable def torsionPointDerivedSectionsComparison
    [IsIso (torsionPointSectionsComparison Ω Λ)] :=
  Functor.mapDerivedCategoryNatIso (asIso (torsionPointSectionsComparison Ω Λ)) ≪≫
    Functor.mapDerivedCategoryCompIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) (Spec (.of Ω)))
      (torsionPointProEtaleSections Ω Λ)

/-- The normalized stalk identification, extended termwise and restricted to D+.
Source: blueprint, sections at a pro-etale geometric point, clause 3; Stacks 03Q1
(blueprint: det-pbc-torsion-stalk-proetale-point). -/
noncomputable def torsionPointDerivedStalkSections {Y : Scheme.{u}}
    (barY : Spec (.of Ω) ⟶ Y)
    (s : Etale.upperStar (ModuleCat.{u + 1} Λ) barY ⋙
        Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω)) ≅
      (Scheme.pointSmallEtale barY).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
  letI : ((Scheme.pointSmallEtale barY).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).Additive :=
    (Scheme.pointSmallEtale barY).sheafFiber_additive
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι
    (Functor.mapDerivedCategoryNatIso s.symm ≪≫
      Functor.mapDerivedCategoryCompIso (Etale.upperStar (ModuleCat.{u + 1} Λ) barY)
        (Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω)))) ≪≫
    Functor.isoWhiskerRight
      (Etale.upperStar (ModuleCat.{u + 1} Λ) barY).mapDerivedCategoryPlusCompatibility.symm
      (Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).mapDerivedCategory

/-- Compose exact point sections with pro-etale derived direct image to obtain actual
fibre derived global sections, using the derived composition comparison.
Source: blueprint proof, step 6; Stacks 079P
(blueprint: det-pbc-torsion-stalk-proetale-point). -/
noncomputable def torsionPointProEtaleLerayIso {Z : Scheme.{u}}
    (a : Z ⟶ Spec (.of Ω)) :=
  letI := (ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} Λ) a).preservesKInjectiveComplexes
  Functor.isoWhiskerLeft (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) a).rightDerivedFunctor
      ((torsionPointProEtaleSections Ω Λ).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
        Functor.rightDerivedFunctorNatIso
          (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology (Spec (.of Ω)))
            (ModuleCat.{u + 1} Λ) (Scheme.ProEt.isTerminalMkId (Spec (.of Ω)))).symm) ≪≫
    Functor.rightDerivedFunctorCompIso' (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) a)
      (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of Ω))) (ModuleCat.{u + 1} Λ))
      (ProEtale.globalSectionsLowerStarIso (ModuleCat.{u + 1} Λ) a)

/-- The etale counterpart of the canonical section-composition comparison on D+.
Source: blueprint proof, step 8; Stacks 079P
(blueprint: det-pbc-torsion-stalk-proetale-point). -/
noncomputable def torsionPointEtaleLerayIso {Z : Scheme.{u}}
    (a : Z ⟶ Spec (.of Ω)) :=
  Functor.isoWhiskerLeft (Etale.lowerStar (ModuleCat.{u + 1} Λ) a).rightDerivedFunctorPlus
      (Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        ((Etale.sectionsFunctor (ModuleCat.{u + 1} Λ)
          (Spec (.of Ω))).rightDerivedFunctorIsoMapDerivedCategory.symm)) ≪≫
    Functor.isoWhiskerRight
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) a).rightDerivedFunctorPlusCompatibility
      (Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).rightDerivedFunctor ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (Functor.isoWhiskerLeft (Etale.lowerStar (ModuleCat.{u + 1} Λ) a).rightDerivedFunctor
        (Functor.rightDerivedFunctorNatIso
          (F := Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω)))
          (G := Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
          ((Sheaf.ΓNatIsoSheafSections (Spec (.of Ω)).smallEtaleTopology
            (ModuleCat.{u + 1} Λ) (Scheme.Etale.isTerminalMkId (Spec (.of Ω))) :
              Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ≅
                Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω)))).symm) ≪≫
        Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) a)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
  (barY : Spec (.of Ω) ⟶ Y)
  (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

/-- The first displayed isomorphism, using the normalized stalk and fixed source comparison.
Source: blueprint, sections at a pro-etale geometric point, clause 3, first arrow
(blueprint: det-pbc-torsion-stalk-proetale-point). -/
noncomputable def torsionPointFibreSourceIso
    [IsIso (torsionPointSectionsComparison Ω Λ)]
    (s : Etale.upperStar (ModuleCat.{u + 1} Λ) barY ⋙
        Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω)) ≅
      (Scheme.pointSmallEtale barY).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
  (torsionPointDerivedStalkSections Ω Λ barY s).app
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj K) ≪≫
    (torsionPointDerivedSectionsComparison Ω Λ).app _ ≪≫
    (torsionPointProEtaleSections Ω Λ).mapDerivedCategory.mapIso
      ((ProEtale.baseChangeSourceComparisonIso f barY Λ).app K)

/-- The second displayed arrow: point sections of the specified pro-etale exchange,
followed by the canonical composition with fibre derived global sections.
Source: blueprint, sections at a pro-etale geometric point, clause 3, second arrow
(blueprint: det-pbc-torsion-stalk-proetale-point). -/
noncomputable def torsionPointProEtaleFibreMap :=
  (torsionPointProEtaleSections Ω Λ).mapDerivedCategory.map
      ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback f barY).toCommSq).app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj K))) ≫
    (torsionPointProEtaleLerayIso Ω Λ (pullback.snd f barY)).hom.app _

/-- The etale fibre arrow, conjugated by the normalized stalk and section-composition maps.
Source: blueprint, sections at a pro-etale geometric point, clause 3, final sentence
(blueprint: det-pbc-torsion-stalk-proetale-point). -/
noncomputable def torsionPointEtaleFibreMap
    (s : Etale.upperStar (ModuleCat.{u + 1} Λ) barY ⋙
        Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω)) ≅
      (Scheme.pointSmallEtale barY).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
  ((torsionPointDerivedStalkSections Ω Λ barY s).app
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj K)).hom ≫
    (Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map ((Etale.baseChange (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback f barY).toCommSq).app K)) ≫
    (torsionPointEtaleLerayIso Ω Λ (pullback.snd f barY)).hom.app _

/-- The usual comparison on fibre cohomology, followed by the inverse-image comparison.
Both endpoints are actual derived global sections; the direct-image mate and point unit
fix the intervening comparison.
Source: blueprint proof, step 8, sections at a pro-etale geometric point
(blueprint: det-pbc-torsion-stalk-proetale-point). -/
noncomputable def torsionPointFibreCohomologyComparison
    [IsIso (torsionPointSectionsComparison Ω Λ)] :=
  (torsionPointEtaleLerayIso Ω Λ (pullback.snd f barY)).inv.app
      ((Etale.upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst f barY)).mapDerivedCategoryPlus.obj K) ≫
    (torsionPointDerivedSectionsComparison Ω Λ).hom.app _ ≫
    (torsionPointProEtaleSections Ω Λ).mapDerivedCategory.map
      ((ProEtale.baseChangeTargetComparisonIso
        (pullback.fst f barY) (pullback.snd f barY) Λ).hom.app K) ≫
    (torsionPointProEtaleLerayIso Ω Λ (pullback.snd f barY)).hom.app _

end Constructions

/-- Exact point sections, the canonical point comparison, and compatible torsion fibre
isomorphisms, with actual derived global sections as the fibre endpoints.

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-cor-pbc-torsion-stalk/sk-cor-pbc-torsion-stalk-proetale-point.md
(blueprint: det-pbc-torsion-stalk-proetale-point).

Proof (the eight steps of the node):
1. Spec Ω is a singleton, hence w-local with extremally disconnected component space.
Its sole local ring Ω is henselian: idempotent lifting modulo zero is the identity.
Its residue field is separably closed. Thus Ω is w-contractible by sk-def-pe-wlocal
and def-weil-pbc-henselian-terminology; no ind-etale claim about all weakly etale algebras
is needed.
2. Apply det-pe-wc-sections-exact and det-pe-wc-sections-derived to the terminal affine
point with constant coefficients. Sections are exact, and the canonical derived unit
is invertible, computing sections termwise on every bounded-below representative.
3. By lem-weil-pbc-geometric-point-pullback-stalk, etale point sections are an exact
module equivalence. Apply lem-weil-pbc-comparison-sections to the constant one-object
system P. Its comparison unit gives the point-section isomorphism. Exact inverse image
(lem-weil-pbc-site-pullback-abelian-exact) and exact-functor-bounded-below extend it
termwise to complexes and descend through quasi-isomorphisms.
4. Properness of f and its base change a gives qcqs. Use the fixed pullback comparison
and derived restriction mate for direct image (def-weil-pbc-fixed-derived-comparisons,
prop-weil-pbc-comparison-direct-image). Pulling back the latter and composing with the
former gives the source comparison. The point-pullback-stalk lemma is linear by
naturality under scalar endomorphisms. Its germ normalization yields s; deriving s and
using step 3 gives the first displayed isomorphism, torsionPointFibreSourceIso.
5. The bounded-below comparison and det-pe-classical-derived-equivalence make ν* K
classical. Exactness commutes with cohomology. Write each torsion cohomology sheaf as
the filtered colimit of its n-torsion kernels, ordered by divisibility. The comparison
inverse image preserves this colimit by adjunction and preserves these kernels by
exactness; module-sheaf colimits have the underlying abelian colimits. Thus ν* K is
torsion. Apply sk-thm-properbasechange; exact point sections preserve its exchange iso.
6. Exact inverse image preserves the lower bound. Good truncation gives a bounded-below
representative; lem-sc-bounded-below-injective-resolution gives a K-injective resolution
J. K-injective comparison homotopy equivalences remain so under additive direct image.
Consequently Ra_* is represented by a_*J, and exact point sections give Γ(P,a_*J) =
Γ(X_barY,J). This is natural on resolution maps and gives precisely the canonical
section-composition isomorphism torsionPointProEtaleLerayIso.
7. Put S = p_g β_f ∘ α_g and T = s_a α_i ∘ β_a, using the fixed comparisons of step 4.
Transpose the two sides of E_proet ∘ S = T ∘ ν* E_et under p_a ⊣ s_a. For the right
side, move s_a α_i through the counit and use stage3-proetale-comparison-counit.
For the left side use the exchange mate, move β_f through the square by naturality,
then apply stage3-proetale-comparison-square and the same counit identity for f.
Naturality of α_i leaves both transposes equal to
α_i ∘ ν*(l_i ε_f ∘ θ_et) ∘ α_a inverse. Injectivity of transposition gives the equality.
8. Apply exact point sections to step 7. Represent the etale fibre complex by a
bounded-below injective I, and resolve ν*I by J on the pro-etale fibre. The specified
restriction mate β_a is represented by ν*a_*I → a_*ν*I → a_*J. Its section map is
Γ(X_barY,et,I) → Γ(X_barY,proet,ν*I) → Γ(X_barY,proet,J): the first arrow is inverse
image of sections by the underived mate-counit formula, and the second is the resolution
map. Thus it is the usual cohomology comparison. K-injective homotopy comparison makes
this independent of resolutions. The same I computes the etale section-composition
map. These identify step 7 with the final displayed equality. The fibre comparison and
composite are invertible, hence so is the etale fibre map, for arbitrary Λ.
-/
theorem proEtale_torsion_stalk_point
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (Λ : Type (u + 1)) [CommRing Λ] :
    PreservesFiniteLimits (torsionPointProEtaleSections Ω Λ) ∧
    PreservesFiniteColimits (torsionPointProEtaleSections Ω Λ) ∧
    (Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).IsEquivalence ∧
    (∀ [PreservesFiniteLimits (torsionPointProEtaleSections Ω Λ)]
      [PreservesFiniteColimits (torsionPointProEtaleSections Ω Λ)]
      [(Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).IsEquivalence],
      (∀ M : HomotopyCategory.Plus
          (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) (ModuleCat.{u + 1} Λ)),
        IsIso ((torsionPointProEtaleSections Ω Λ).rightDerivedFunctorUnit.app M.obj)) ∧
      IsIso (torsionPointSectionsComparison Ω Λ) ∧
      (∀ [IsIso (torsionPointSectionsComparison Ω Λ)]
        {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
        (barY : Spec (.of Ω) ⟶ Y)
        (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
        (hK : ∀ n : ℤ, Scheme.IsTorsionAbelianSheaf
          ((DerivedCategory.Plus.homologyFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) n).obj
            ((D+(Etale.moduleAbelianForget Λ X)).obj K))),
        ∃ s : Etale.upperStar (ModuleCat.{u + 1} Λ) barY ⋙
            Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) (Spec (.of Ω)) ≅
          (Scheme.pointSmallEtale barY).sheafFiber (A := ModuleCat.{u + 1} Λ),
          (∀ (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
            (U : Y.Etale) (x : (Scheme.pointSmallEtale barY).fiber.obj U),
            torsionPointPulledBackSection Ω Λ barY F U x ≫ s.hom.app F =
              (Scheme.pointSmallEtale barY).toPresheafFiber U x F.obj) ∧
          IsIso (torsionPointProEtaleFibreMap Ω Λ f barY K) ∧
          IsIso (torsionPointEtaleFibreMap Ω Λ f barY K s) ∧
          IsIso (torsionPointFibreCohomologyComparison Ω Λ f barY K) ∧
          (torsionPointFibreSourceIso Ω Λ f barY K s).hom ≫
              torsionPointProEtaleFibreMap Ω Λ f barY K =
            torsionPointEtaleFibreMap Ω Λ f barY K s ≫
              torsionPointFibreCohomologyComparison Ω Λ f barY K)) := by
  sorry

end AlgebraicGeometry
