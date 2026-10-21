/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.ExactSequence
import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.CategoryTheory.RingedSiteInjectiveMonoRestriction
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The ordinary etale injective support sequence

Source: Stacks Project, Tags 093X, 09XQ, 0A45, 08FI, 070I, 070K, 08BJ and 0152
(blueprint: lem-pur-etale-injective-support-sequence).

The functor `closedUpperShriek (ModuleCat A) i j` is the existing construction
`i^* ker(id → j_*j^*)`. The sequence uses its actual adjunction counit and the actual
open adjunction unit. The derived comparisons below are fixed by the derived-functor
unit and uniqueness of right adjoints, including counit normalization.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u

attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Adjunction.mapHomologicalComplex
  _root_.DerivedCategory.Q _root_.DerivedCategory.Qh

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar closedUpperShriek
  lowerStarClosedUpperShriekAdjunction upperStarLowerStarAdjunction

variable (A : Type (u + 1)) [CommRing A]
  {Z P U : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
  (j : U ⟶ P) [IsOpenImmersion j]
  (hij : Set.range i.base = (Set.range j.base)ᶜ)

/-- The termwise support inclusion, as a natural transformation with its explicit
source and target functors. It is the existing closed adjunction counit on complexes.
Source: Stacks Project, Tags 09XQ and 0A45
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportInclusion :
    (closedUpperShriek (ModuleCat.{u + 1} A) i j).mapHomologicalComplex (.up ℤ) ⋙
      (lowerStar (ModuleCat.{u + 1} A) i).mapHomologicalComplex (.up ℤ) ⟶ 𝟭 _ :=
  ((lowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} A) i j hij).mapHomologicalComplex
    (.up ℤ)).counit

/-- The termwise open restriction map, as a natural transformation with its explicit
source and target functors. It is the existing open adjunction unit on complexes.
Source: Stacks Project, Tags 093X and 0A45
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportRestriction :
    𝟭 (CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) ⟶
      (upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ) ⋙
        (lowerStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).mapHomologicalComplex
    (.up ℤ)).unit

/-- The closed support counit followed by the open unit is zero, termwise.
Source: Stacks Project, Tag 09XQ, the support adjunction
(blueprint: lem-pur-etale-injective-support-sequence).

Proof: the supported kernel restricts to zero on U. Every map out of a closed
pushforward is consequently killed by the open unit, by adjunction and disjointness
(lem-pur-etale-supported-kernel-adjunction). Apply this to the support counit in
each degree; equality of maps of complexes is degreewise equality. -/
theorem etaleSupportSequence_zero
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (etaleSupportInclusion A i j hij).app I ≫
      (etaleSupportRestriction A j).app I = 0 := by
  sorry

/-- The canonical sequence `i_*H_A(I) → I → j_*j^*I`, with H_A the existing
closed supported inverse image, and maps the termwise counit and unit.
Source: Stacks Project, Tag 0A45, proof
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportSequence
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ShortComplex (CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ShortComplex.mk
    ((etaleSupportInclusion A i j hij).app I)
    ((etaleSupportRestriction A j).app I)
    (etaleSupportSequence_zero A i j hij I)

/-- The sequence is functorial on all chain maps, with the prescribed three components.
Source: Stacks Project, Tag 0A45, proof, and Tag 0152, naturality
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportSequenceMap
    {I J : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    (f : I ⟶ J) : etaleSupportSequence A i j hij I ⟶ etaleSupportSequence A i j hij J :=
  ShortComplex.homMk
    (S₁ := etaleSupportSequence A i j hij I)
    (S₂ := etaleSupportSequence A i j hij J)
    (((closedUpperShriek (ModuleCat.{u + 1} A) i j).mapHomologicalComplex (.up ℤ) ⋙
      (lowerStar (ModuleCat.{u + 1} A) i).mapHomologicalComplex (.up ℤ)).map f)
    f
    (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ) ⋙
      (lowerStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).map f)
    ((etaleSupportInclusion A i j hij).naturality f)
    ((etaleSupportRestriction A j).naturality f)

/-- The computation of `Ri_A^!` on a K-injective complex, using the derived unit and
then the unique counit-compatible comparison to the recorded ordinary right adjoint.
Source: Stacks Project, Tags 070K, 08BJ and 09XQ; det-sp-unique-right-adjoint
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportShriekComparison [Finite A]
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective] :
    _root_.DerivedCategory.Q.obj
        (((closedUpperShriek (ModuleCat.{u + 1} A) i j).mapHomologicalComplex (.up ℤ)).obj I) ≅
      (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj
        (_root_.DerivedCategory.Q.obj I) :=
  ((closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctorObjQIso I).symm ≪≫
    ((derivedLowerStarClosedUpperShriekAdjunction (R := A) i j hij).rightAdjointUniq
      (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i)))).app
        (_root_.DerivedCategory.Q.obj I)

/-- The first-term comparison, using exact termwise closed direct image and the
preceding counit-compatible computation of `Ri_A^!`.
Source: Stacks Project, Tags 04CA, 09XQ and 0A45
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportFirstComparison [Finite A]
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective] :
    _root_.DerivedCategory.Q.obj (etaleSupportSequence A i j hij I).X₁ ≅
      (R(lowerStar (ModuleCat.{u + 1} A) i)).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj
          (_root_.DerivedCategory.Q.obj I)) :=
  ((lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryFactors.app
    (((closedUpperShriek (ModuleCat.{u + 1} A) i j).mapHomologicalComplex (.up ℤ)).obj I)).symm ≪≫
    ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorIsoMapDerivedCategory.app
      (_root_.DerivedCategory.Q.obj
        (((closedUpperShriek (ModuleCat.{u + 1} A) i j).mapHomologicalComplex
          (.up ℤ)).obj I))).symm ≪≫
    (R(lowerStar (ModuleCat.{u + 1} A) i)).mapIso
      (etaleSupportShriekComparison A i j hij I)

/-- The third-term comparison is normalized by the right-derived unit and the
exact restriction comparison. The proof argument records K-injectivity on U,
without imposing it as an extra hypothesis of the main statement.
Source: Stacks Project, Tags 08FI, 070K and 0A45
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportThirdComparison
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hJ : CochainComplex.IsKInjective
      (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I)) :
    _root_.DerivedCategory.Q.obj
        (((lowerStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj
          (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I)) ≅
      (R(lowerStar (ModuleCat.{u + 1} A) j)).obj
        ((D(upperStar (ModuleCat.{u + 1} A) j)).obj (_root_.DerivedCategory.Q.obj I)) :=
  letI := hJ
  ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorObjQIso
    (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I)).symm ≪≫
    (R(lowerStar (ModuleCat.{u + 1} A) j)).mapIso
      ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.app I).symm

/-- A degreewise-injective K-injective model gives the short exact support sequence,
and its canonical SES triangle realizes the actual derived counit/unit triangle,
with fixed endpoint comparisons and the representing isomorphism in the middle.
The boundary is one natural transformation on the ordinary unbounded derived category.
Source: Stacks Project, Tags 093X, 09XQ, 0A45, 08FI, 070I, 070K, 08BJ and 0152
(blueprint: lem-pur-etale-injective-support-sequence).

Proof:
1. Form G(M)=ker(eta_j(M)). The closed unit q:G(M)→i_*i^*G(M) is invertible by
   lem-pur-etale-supported-kernel-adjunction and is module-linear. Exact closed
   direct image and full faithfulness identify maps i_*N→M with maps N→i^*G(M);
   the counit is q inverse followed by the kernel inclusion (lem-kun-04ca).
2. Evaluate the open unit on an etale V over P. It is restriction along the
   monomorphism V×_P U→V (lem-weil-pbc-etale-inverse-image-restriction). By
   lem-pur-ringed-site-injective-mono-restriction it is surjective for each
   injective module I^r. Substitute the supported-kernel identification to get
   degreewise short exactness; lem-weil-pbc-cochain-complexes-degreewise-exact
   gives short exactness of complexes. Naturality of unit and counit gives its maps.
3. Module sheaves are Grothendieck abelian (lem-weil-pbc-ring-sheaves-grothendieck),
   hence have degreewise-injective K-injective replacements
   (lem-pur-kinjective-degreewise-existence). The termwise additive H_A acts on
   homotopies, shifts and cones. lem-weil-pbc-kinjective-total-derived computes RH_A
   on I. No bounded-below replacement is made.
4. Since i_* is exact, H_A preserves K-injectives
   (lem-weil-pbc-right-adjoint-preserves-kinjective). The Hom bijections of
   lem-weil-pbc-kinjective-hom-derived and lem-weil-pbc-termwise-adjunction-homotopy
   identify RH_A as the right adjoint of Ri_*=i_*. det-sp-unique-right-adjoint
   identifies it with the ordinary right adjoint, compatibly with the counit.
5. Identify open restriction with slice restriction by
   lem-weil-pbc-etale-site-localization-open and
   lem-weil-pbc-etale-inverse-image-restriction. Then
   lem-pur-kinjective-restrict-localized makes j^*I K-injective. Total derivation
   computes Rj_*j^*QI on j_*j^*I, and the termwise adjunction identifies its map
   from QI with the actual derived open unit.
6. Apply lem-weil-pbc-complex-ses-triangle. Its cone-to-quotient construction fixes
   the boundary, including its sign. Steps 4 and 5 identify the endpoints and the
   first two arrows with the ordinary closed counit and open unit. The natural
   boundary of lem-exc-closed-support-triangle is the transported SES boundary.
7. Derived maps between K-injectives are unique homotopy classes of chain maps
   (lem-weil-pbc-kinjective-hom-derived); quasi-isomorphisms are homotopy equivalences.
   Termwise functors preserve these homotopies. SES boundary naturality therefore
   descends to derived naturality and comparison of representatives. No injectivity
   after scalar restriction or forgetting modules is used. -/
theorem etale_injective_support_sequence [Finite A] :
    ∃ δ : D(upperStar (ModuleCat.{u + 1} A) j) ⋙
        R(lowerStar (ModuleCat.{u + 1} A) j) ⟶
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint ⋙
          R(lowerStar (ModuleCat.{u + 1} A) i)) ⋙
          shiftFunctor (_root_.DerivedCategory
            (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A))) (1 : ℤ),
      (∀ L : _root_.DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)),
        Triangle.mk
          ((Adjunction.ofIsLeftAdjoint
            (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app L)
          ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app L)
          (δ.app L) ∈ distTriang _) ∧
      ∀ (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective] [∀ r : ℤ, Injective (I.X r)]
        (L : _root_.DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (e : _root_.DerivedCategory.Q.obj I ≅ L),
        ∃ (hS : (etaleSupportSequence A i j hij I).ShortExact)
          (hJ : CochainComplex.IsKInjective
            (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I))
          (t : _root_.DerivedCategory.triangleOfSES hS ≅
            Triangle.mk
              ((Adjunction.ofIsLeftAdjoint
                (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app L)
              ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app L)
              (δ.app L)),
          t.hom.hom₁ = (etaleSupportFirstComparison A i j hij I).hom ≫
            (R(lowerStar (ModuleCat.{u + 1} A) i)).map
              ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.map e.hom) ∧
          t.hom.hom₂ = e.hom ∧
          t.hom.hom₃ = (etaleSupportThirdComparison A j I hJ).hom ≫
            (R(lowerStar (ModuleCat.{u + 1} A) j)).map
              ((D(upperStar (ModuleCat.{u + 1} A) j)).map e.hom) := by
  sorry

/-- Naturality of the entire support SES triangle, including its canonical boundary,
for chain maps between degreewise-injective K-injective models.
Source: Stacks Project, Tag 0152, naturality of the canonical delta functor
(blueprint: lem-pur-etale-injective-support-sequence).

Proof: etaleSupportSequenceMap is the termwise diagram induced by the chain map,
using naturality of the closed counit and open unit. Apply
lem-weil-pbc-complex-ses-triangle, specifically triangleOfSESδ_naturality, to this
morphism of short exact sequences. Its third square is exactly the displayed equality.
The other two squares are the two fields of the sequence morphism. -/
theorem etaleSupportSequence_boundary_naturality [Finite A]
    {I J : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    [I.IsKInjective] [J.IsKInjective]
    [∀ r : ℤ, Injective (I.X r)] [∀ r : ℤ, Injective (J.X r)]
    (hI : (etaleSupportSequence A i j hij I).ShortExact)
    (hJ : (etaleSupportSequence A i j hij J).ShortExact) (f : I ⟶ J) :
    _root_.DerivedCategory.triangleOfSESδ hI ≫
        (_root_.DerivedCategory.Q.map (etaleSupportSequenceMap A i j hij f).τ₁)⟦1⟧' =
      _root_.DerivedCategory.Q.map (etaleSupportSequenceMap A i j hij f).τ₃ ≫
        _root_.DerivedCategory.triangleOfSESδ hJ := by
  sorry

end AlgebraicGeometry.Etale
