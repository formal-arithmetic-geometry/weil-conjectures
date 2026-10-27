module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.AlgebraicGeometry.DerivedQCohCompactGeneration
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums
import WeilConjectures.CategoryTheory.BrownRepresentabilityRightAdjoint
import WeilConjectures.AlgebraicGeometry.PseudoCoherentSupportAnnihilation
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.PerfectOpenSupportDetection
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import WeilConjectures.AlgebraicGeometry.PerfectDerivedTensor
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.RightAdjointOpenSupportCriterion
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory
import Sheaf.CategoryTheory.SemisimplicialEvaluationFreeAdjoint
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.CoherentRightAdjointComparisons
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Locality of coherent right adjoints between flat families

Source: Stacks Project, duality.tex, Tags 0A9E and 0A9P (including its Kiehl footnote),
and the arbitrary-base extension in the node's twelve-step proof.
(blueprint: lem-sfb-proper-flat-families-coherent-adjoint-locality).

The auxiliary functors are lifts of existing functors to full subcategories. The open
comparison is the existing explicitly derived sectionwise identity. In particular the
mate does not select an isomorphism from a bare existence assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.ProperFlatFamilies

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The existing derived direct image, restricted to quasi-coherent cohomology.
Source: Stacks, Tags 08D5 and 0A9E
(blueprint: lem-sfb-proper-flat-families-coherent-adjoint-locality). -/
abbrev directImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y :=
  (schemeDerivedQCohProperty Y).lift
    ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (fun K => schemeDerivedDirectImage_preserves_QCoh f K.obj K.property)

/-- The existing exact derived open restriction, on the full quasi-coherent subcategories.
Source: Stacks, Tags 08BV and 08DW
(blueprint: lem-sfb-proper-flat-families-coherent-adjoint-locality). -/
abbrev restriction (X : Scheme.{u}) (V : X.Opens) :
    schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory V.toScheme :=
  (schemeDerivedQCohProperty V.toScheme).lift
    ((schemeDerivedQCohProperty X).ι ⋙ schemeMVDerivedRestriction X V)
    (fun K => (schemeDerivedQCoh_openRestriction_iff X V K.obj).2
      (fun n => letI := K.property n
                SheafOfModules.isQuasicoherent_over _ V))

/-- The canonical direct-image/open-restriction comparison, lifted through the full
subcategory inclusions. The underlying isomorphism is constructed from the sectionwise
identity by `schemeMVOpenRestrictionComparison`, not chosen from `Nonempty`.
Source: Stacks, Tag 08FE
(blueprint: lem-sfb-proper-flat-families-coherent-adjoint-locality). -/
def openComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (V : Y.Opens) :
    directImage f ⋙ restriction Y V ≅
      restriction X (f ⁻¹ᵁ V) ⋙ directImage (f ∣_ V) :=
  NatIso.ofComponents
    (fun K => (schemeDerivedQCohProperty V.toScheme).isoMk
      ((schemeMVOpenRestrictionComparison f V).app K.obj))
    (fun {_K _L} b => (schemeDerivedQCohProperty V.toScheme).hom_ext
      ((schemeMVOpenRestrictionComparison f V).hom.naturality b.hom))

/-- The canonical mate of the inverse sectionwise comparison, under the specified
adjunctions. Its transpose is restriction of the original counit.
Source: Stacks, duality.tex, equation (48.4.1.1), Tags 0A9L and 0A9P
(blueprint: lem-sfb-proper-flat-families-coherent-adjoint-locality). -/
def openMate {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (V : Y.Opens)
    {a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X}
    {aV : schemeDerivedQCohCategory V.toScheme ⥤
      schemeDerivedQCohCategory (f ⁻¹ᵁ V).toScheme}
    (adj : directImage f ⊣ a) (adjV : directImage (f ∣_ V) ⊣ aV) :
    a ⋙ restriction X (f ⁻¹ᵁ V) ⟶ restriction Y V ⋙ aV :=
  (mateEquiv adj adjV
    (TwoSquare.mk _ _ _ _ (openComparison f V).inv)).natTrans

/-- Proper morphisms between flat, locally finitely presented families over an arbitrary
scheme have right adjoints on the full unbounded quasi-coherent derived categories.
Source: Stacks, Tags 0A9E and 0A9P, and the node's arbitrary-scheme Brown argument
(blueprint: lem-sfb-proper-flat-families-coherent-adjoint-locality).

Proof (step 1 of the node): On qcqs schemes compact generation, preservation of sums
and Brown representability give the adjoint. For arbitrary schemes a proper morphism
is still qcqs, so its direct image preserves quasi-coherence and sums. Apply the
single-scheme case of lem-sfb-levelwise-quasicoherent-brown, using ordinary weak-Serre
Brown representability. This gives a global adjoint without asserting that D(QCoh)
is D_QCoh. The same argument applies to each open restriction of the proper map. -/
theorem exists_rightAdjoint {S X Y : Scheme.{u}}
    (pX : X ⟶ S) (pY : Y ⟶ S)
    [Flat pX] [LocallyOfFinitePresentation pX]
    [Flat pY] [LocallyOfFinitePresentation pY]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ pY = pX) :
    (directImage f).IsLeftAdjoint ∧
      ∀ V : Y.Opens, (directImage (f ∣_ V)).IsLeftAdjoint := by
  sorry

/-- The counit-normalized open mate is invertible on every locally bounded-below input.
Its normalization uniquely characterizes its component, including among arbitrary maps.
The quantification over adjunctions permits every choice of right adjoint on the full
unbounded categories. No bound on the right adjoint's output is assumed.
Source: Stacks, Tags 0A9L and 0A9P, with its Kiehl footnote and the node's ordinary
Zariski total-descent extension
(blueprint: lem-sfb-proper-flat-families-coherent-adjoint-locality).

Proof:
1. Existence is exists_rightAdjoint. On qcqs Y and quasi-compact V, a bounded-below
   Q supported off V has right adjoint supported off f-inverse(V): for a perfect P
   and a map P to a(Q), transpose to Rf_*P to Q. Kiehl makes Rf_*P pseudo-coherent
   for a proper map between the given flat families; no flatness of f is needed.
2. Pseudo-coherent support annihilation gives a perfect I to O_Y, invertible on V,
   killing this map after tensoring. Projection formula and adjunction transpose it
   back to Lf^*I tensor P to P to a(Q). It restricts to zero on f-inverse(V).
   The perfect open-support detector implies that a(Q) vanishes there.
3. The right-adjoint open-support criterion gives invertibility on bounded-below K.
   The open direct-image comparison identifies its transpose with the restricted
   counit. Injectivity of the adjunction bijection gives normalization and uniqueness.
4. For a set-indexed open cover use the face-only Cech schemes and their ordinary
   ringed total module categories. Exact free evaluation adjoints imply that
   evaluation preserves K-injectives. Consequently total derived direct image F
   evaluates to Rf_n*. It preserves levelwise quasi-coherence and sums.
5. Ordinary levelwise Brown gives F adjoint to G. The free-evaluation comparison
   F ell_n = ell_n Rf_n* is invertible, as checked by conservative evaluations;
   Hom adjunctions and Yoneda identify e_n G with a_n e_n, preserving counits.
6. The alpha-labelled summand of the free-evaluation counit identifies the transition
   of GN with a_n(theta_N) after the open-square mate. Thus these are transitions
   of an actual total derived object, not a lifted diagram of derived objects.
7. When Y is quasi-separated, choose affine charts. Their finite intersections are
   qcqs, so local boundedness gives a single bound on each intersection. Step 3
   makes the transition mates at the restricted K invertible; G(b^*K) is cartesian.
8. Ordinary Zariski total descent gives H with a^*H = G(b^*K). Total pushforward
   sends a^*M to a cartesian object, and derived pushforward composition gives
   Rb_*F(a^*M) = Rf_*Ra_*a^*M = Rf_*M. Descent and the total Hom adjunction show
   Hom(M,H) = Hom(Rf_*M,K). Yoneda identifies H with a(K), preserving counits.
9. Include any desired affine W as a chart. For arbitrary V cover V by affine W;
   the transpose calculation pastes the Y-to-W mate through the V-to-W mate.
   Invertibility on the cover detects invertibility by cohomology of the cone.
10. For arbitrary Y, intersections of affine charts are open subschemes of affine
    schemes, hence separated, though not necessarily quasi-compact. Apply the
    already proved quasi-separated case on these intersections. Repeat steps 4--8
    to descend the actual cartesian object and recover the global counit.
11. Step 9 now gives locality to every open of arbitrary Y.
12. The mate is natural in K by its construction as a natural transformation.
    Its counit equation follows by inverse transposition. Any component with that
    equation has the same transpose, so injectivity of the adjunction Hom bijection
    proves the asserted uniqueness. -/
theorem coherent_adjoint_locality {S X Y : Scheme.{u}}
    (pX : X ⟶ S) (pY : Y ⟶ S)
    [Flat pX] [LocallyOfFinitePresentation pX]
    [Flat pY] [LocallyOfFinitePresentation pY]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ pY = pX) (V : Y.Opens)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (aV : schemeDerivedQCohCategory V.toScheme ⥤
      schemeDerivedQCohCategory (f ⁻¹ᵁ V).toScheme)
    (adj : directImage f ⊣ a) (adjV : directImage (f ∣_ V) ⊣ aV)
    (K : schemeDerivedQCohCategory Y)
    (hK : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ ∃ b : ℤ, ∀ i : ℤ, i < b →
      IsZero ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) W).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj K.obj))) :
    IsIso ((openMate f V adj adjV).app K) ∧
    ((directImage (f ∣_ V)).map ((openMate f V adj adjV).app K) ≫
      adjV.counit.app ((restriction Y V).obj K) =
        (openComparison f V).inv.app (a.obj K) ≫
          (restriction Y V).map (adj.counit.app K)) ∧
    (∀ b : (restriction X (f ⁻¹ᵁ V)).obj (a.obj K) ⟶
        aV.obj ((restriction Y V).obj K),
      (directImage (f ∣_ V)).map b ≫ adjV.counit.app ((restriction Y V).obj K) =
          (openComparison f V).inv.app (a.obj K) ≫
            (restriction Y V).map (adj.counit.app K) →
        b = (openMate f V adj adjV).app K) := by
  sorry

end AlgebraicGeometry.ProperFlatFamilies
