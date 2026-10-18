/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.SupportLocalizationTriangle
public import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import WeilConjectures.Compactification.Refinement

/-!
# Closed support and the transported exceptional inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
first paragraph of lem-pur-gysin-structure.proof.md; Stacks Tags 001P and 09BM
(blueprint: lem-pur-closed-support-exceptional-comparison).

The compactification is exactly (id_Z,i). The compact-support identification below
uses the identity extension-by-zero adjunction and the unit-normalized exact derived
comparison, so the relative Hom map has the same source as the support Hom map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Identity extension by zero, normalized by its adjunction with identity pullback.
Source: blueprint closed-support comparison, proof step 2
(blueprint: lem-pur-closed-support-exceptional-comparison). -/
def closedSupportIdentityExtension (A : Type (u + 1)) [CommRing A] [Finite A]
    (Z : Scheme.{u}) : openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 Z) ≅ 𝟭 _ :=
  (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 Z)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight (upperStarId (ModuleCat.{u + 1} A) Z).symm)

/-- Compact support at (id_Z,i) is the exact termwise closed direct image on D+.
The isomorphism is constructed from identity extension by zero and the canonical
right-derived/termwise comparison, not supplied as free comparison data.
Source: blueprint closed-support comparison, proof step 2; Stacks Tag 09BM
(blueprint: lem-pur-closed-support-exceptional-comparison). -/
def closedSupportCompactIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X V : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    DerivedCategory.Plus.ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (Compactification.ofIsProper i) ≅
      supportClosedDerivedPlus A i j hPair ⋙ DerivedCategory.Plus.ι :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hPair
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryNatIso (closedSupportIdentityExtension A Z) ≪≫
            Functor.mapDerivedCategoryIdIso _)
          (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor ≪≫
        Functor.leftUnitor _ ≪≫
        (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorIsoMapDerivedCategory) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlusCompatibility.symm

/-- The precise comparison property, in fixed-scalar coordinates. All local instances
are consequences of the given finite coefficient setting and finite-type hypotheses.
The intrinsic constructibility predicate is applied through the existing canonical
constant-scalar realization. The two adjunction data are the data supplied by the
recorded support and comparison-class theorems, quantified to avoid an arbitrary choice.
Under the bounded intrinsic constructibility of the support value, the statement's
sentence "both B₀ and B are bounded below of etale origin" is asserted, not assumed.
The inverse relative Hom bijection is precomposed with closedSupportCompactIso.inv.
Source: blueprint closed-support comparison, statement and proof steps 1--4
(blueprint: lem-pur-closed-support-exceptional-comparison). -/
def closedSupportExceptionalComparisonProperty
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X V : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of P.field.k)) (aX : X ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : V ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) : Prop :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace aZ
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian aZ
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  let c := Compactification.ofIsProper i
  let F := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} P.Coefficient) c
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification P.Coefficient c
  let B := sfFiniteExceptionalAt P.Coefficient c
  let S := supportClosedDerivedPlus P.Coefficient i j hPair
  let R₀ := (finiteClosedUpperShriek P.Coefficient i j).rightDerivedFunctorPlus
  let q := closedSupportCompactIso P.Coefficient i j hPair
  ∀ (adj₀ : S ⊣ R₀)
    (adj : FixedComparisonClassAdjunction P.Coefficient i c
      F.rightAdjoint (Adjunction.ofIsLeftAdjoint F)
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) Z)
      _root_.DerivedCategory.TStructure.t.plus)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))),
    Scheme.intrinsicFiniteTorsionConstructible
      P.coefficients.l P.extension P.level P.level_pos Z
      ((finiteCoefficientIntrinsicRealization Z P.Ring).mapDerivedCategory.obj (R₀.obj K).obj) →
    DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) Z (R₀.obj K).obj ∧
    ∃ hB : DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} P.Coefficient) Z (B.obj K.obj),
      ∃ φ : (R₀.obj K).obj ≅ B.obj K.obj,
          (∀ (T : DerivedCategory.Plus
              (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)))
            (wT : Scheme.FixedEtaleOriginWitness Z P.Coefficient T)
            (f : T.obj ⟶ (R₀.obj K).obj),
            q.inv.app T ≫ (adj.homEquiv c T.obj
              ⟨wT.complex.obj, wT.complex.property, ⟨wT.iso⟩⟩ K.obj K.property).symm
                (f ≫ φ.hom) =
              DerivedCategory.Plus.ι.map
                ((adj₀.homEquiv T K).symm (DerivedCategory.Plus.ι.preimage f))) ∧
          (∀ ψ : (R₀.obj K).obj ≅ B.obj K.obj,
            (∀ (T : DerivedCategory.Plus
                (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)))
              (wT : Scheme.FixedEtaleOriginWitness Z P.Coefficient T)
              (f : T.obj ⟶ (R₀.obj K).obj),
              q.inv.app T ≫ (adj.homEquiv c T.obj
                ⟨wT.complex.obj, wT.complex.property, ⟨wT.iso⟩⟩ K.obj K.property).symm
                  (f ≫ ψ.hom) =
                DerivedCategory.Plus.ι.map
                  ((adj₀.homEquiv T K).symm (DerivedCategory.Plus.ι.preimage f))) → ψ = φ) ∧
          DerivedCategory.Plus.ι.map (S.map (DerivedCategory.Plus.ι.preimage
              (X := R₀.obj K) (Y := ⟨B.obj K.obj, hB.plus⟩) φ.hom)) ≫
              (q.inv.app ⟨B.obj K.obj, hB.plus⟩ ≫
                (adj.homEquiv c (B.obj K.obj) hB K.obj K.property).symm (𝟙 _)) =
            DerivedCategory.Plus.ι.map (adj₀.counit.app K)

/-- Closed support and the finite exceptional inverse image have the unique
Hom-normalized, counit-compatible comparison in the ordinary pro-etale derived category.
No etale-origin hypothesis is imposed on K. Bounded intrinsic constructibility is
assumed only for the support value. The statement asserts that both representing
objects are bounded below of etale origin; these are conclusions, as the citer
lem-pur-gysin-structure uses them.
Source: blueprint main-20261015, first paragraph of lem-pur-gysin-structure.proof.md;
Stacks Tags 001P and 09BM (blueprint: lem-pur-closed-support-exceptional-comparison).

Proof:
1. lem-pur-support-localization-triangle gives the support adjunction and its counit.
2. i is proper (lem-weil-pbc-closed-immersion-proper), so c=(id_Z,i) is a
compactification. Its dimension has a nonnegative finite bound by
lem-kun-dimension-finite-type, including empty Z. The identity extension-by-zero
and exact direct-image comparisons identify P_c with the termwise i_*.
thm-sf-ambient-adjoint-class(2) gives the natural exceptional Hom equivalences.
Both representing objects are in the bounded-below etale-origin class, as the
node's comparison paragraph states. (Node proof steps 2-3 call this "explicitly
assumed"; the node proof does not derive it. For B₀ it follows from the bounded
intrinsic constructibility by lem-weil-pbc-finite-ring-constructible-derived-origin;
for B, the right adjoint of the exact F_c = i_* is left t-exact, so it keeps the
bounded-below R nu_* K bounded below and B is nu^* of it.)
3. On the full bounded-below etale-origin subcategory, apply
lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection (equivalently Yoneda, Tag 001P)
to the natural transformation e_T^{-1} a_T. The reverse transformation gives an
inverse; evaluate naturality on the two identities to obtain both inverse equations.
This proves existence and uniqueness of the Hom-normalized isomorphism.
4. Set T=B₀ and f=id in its defining relation. Naturality of the exceptional
bijection rewrites its left side as i_*(φ) followed by e_B(id), and the support
bijection sends id to its counit. This is exactly the final counit equation. -/
theorem closedSupportExceptionalComparison
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X V : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of P.field.k)) (aX : X ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (i : Z ⟶ X) [IsClosedImmersion i] (_hi : i ≫ aX = aZ)
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    closedSupportExceptionalComparisonProperty P aZ aX i j hPair := by
  sorry

end AlgebraicGeometry.ProEtale
