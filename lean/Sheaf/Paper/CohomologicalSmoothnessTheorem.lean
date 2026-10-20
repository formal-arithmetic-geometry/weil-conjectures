/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import Sheaf.Paper.PurityFiniteSetting
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
import Sheaf.Paper.CohomologicalSmoothComposition
import Sheaf.CategoryTheory.CompositeTensorTranspose
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.FiniteCompactSupportConstructibility
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.Paper.ProjectionFormulaCoefficientCoherence
import Sheaf.Paper.PurityAffineLineOrientationUniqueness
import Sheaf.Paper.SmoothExceptionalBaseChangeStatement

/-!
# Cohomological smoothness for smooth morphisms

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-cohsm/
thm-pur-cohomological-smoothness.proof.md (blueprint: thm-pur-cohomological-smoothness).

This statement records the orientation-free tensor, invertibility, arbitrary base-change,
and composition clauses in the canonical pro-etale comparison coordinates.
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- The compact-support composition comparison, constructed from the compatible
compactifications and the common-refinement comparisons, rather than chosen from a
Nonempty assertion. The compatible compactification is the closure of X in the product
of the chosen compactifications of g and fg.
Source: blueprint thm-pur-cohomological-smoothness, clause 4 and proof Step 9;
thm-sf-comp-composition, triangle construction
(blueprint: thm-pur-cohomological-smoothness). -/
noncomputable def smoothCompactSupportCompIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] :
    Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (f ≫ g) ≅
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g :=
  let c := HasCompactification.compactification g
  let b := (HasCompactification.compactification (f ≫ g)).ofComp c
  (Etale.rightDerivedLowerShriekIso Λ (c.comp b)).symm ≪≫
    (Etale.rightDerivedLowerShriekOfCompactificationCompIso Λ c b).symm ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekIso Λ b.restrict) _ ≪≫
    Functor.isoWhiskerLeft _ (Etale.rightDerivedLowerShriekIso Λ c)

/-- The adjunction-compatible exceptional composition comparison. Its counit is
ε_g followed in adjunction order by g_! ε_f, through the displayed compact-support
comparison, since this is rightAdjointUniq for precisely that composite adjunction.
Source: blueprint thm-pur-cohomological-smoothness, clause 4, proof Step 9
(blueprint: thm-pur-cohomological-smoothness). -/
noncomputable def smoothExceptionalCompIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] :
    Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) (f ≫ g) ≅
      Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) g ⋙
        Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f :=
  Adjunction.rightAdjointUniq
    ((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (f ≫ g)).ofNatIsoLeft
      (smoothCompactSupportCompIso Λ f g))
    ((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).comp
      (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) g))

/-- The specified dualizing comparison q = θ_(f,ω_g) followed by c_Λ⁻¹.
Its invertibility is asserted below; its data use only the existing tensor mate
and the adjunction-induced composition comparison.
Source: blueprint thm-pur-cohomological-smoothness, clause 4, proof Step 9
(blueprint: thm-pur-cohomological-smoothness). -/
noncomputable def smoothDualizingCompMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] :
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj
          (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) g)) ⟶
      Etale.dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g) :=
  Etale.dualizingComplexTensorMap Λ f (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) g) ≫
    (smoothExceptionalCompIso Λ f g).inv.app (𝟙_ _)

/-- Equality of the canonical tensor maps under base change, in comparison coordinates.
The left side is u*θ followed by β_K. The right side uses the monoidal pullback
comparison, b = β_Λ with its unit normalization, the pullback-square comparison,
and θ' at v*K. Applying ν* to the entire equation retains every comparison arrow.
Source: blueprint thm-pur-cohomological-smoothness, clause 3, proof Step 7
(blueprint: thm-pur-cohomological-smoothness). -/
noncomputable def smoothTensorBaseChangeCoherence
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {v : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback u' f' f v)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Prop :=
  (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) u').leftDerivedFunctor.map
          (Etale.dualizingComplexTensorMap Λ f K) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap Λ sq).app K) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map
      ((Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) u'
          (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f)
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K)).hom ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X').map
          (Etale.dualizingComplexBaseChangeMap Λ sq)).app _ ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X').obj
          (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f')).map
          (Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq K) ≫
        Etale.dualizingComplexTensorMap Λ f'
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor.obj K))

/-- The tensor formula under composition: q is invertible and the two specified
arrows agree for every representative of a pro-etale Dctf input. The right side
first reassociates, uses pullback composition and monoidality, pulls back θ_g,
and applies θ_f at g!K. The left side uses q, θ_fg and the exceptional comparison.
Source: blueprint thm-pur-cohomological-smoothness, clause 4, proof Steps 9--10
(blueprint: thm-pur-cohomological-smoothness). -/
noncomputable def smoothTensorCompositionCoherence
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] : Prop :=
  IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
    (smoothDualizingCompMap Λ f g)) ∧
  ∀ K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapDerivedCategory.obj K) →
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
      (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).map
          (smoothDualizingCompMap Λ f g)).app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (f ≫ g)).leftDerivedFunctor.obj K) ≫
        Etale.dualizingComplexTensorMap Λ (f ≫ g) K ≫
        (smoothExceptionalCompIso Λ f g).hom.app K) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
      ((Etale.derivedTensorAssociator (ModuleCat.{u + 1} Λ) X
          (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f)
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj
            (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) g))
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (f ≫ g)).leftDerivedFunctor.obj K)).hom ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f)).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj
                (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) g))).map
              ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g).hom.app K) ≫
            (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f
              (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) g)
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor.obj K)).inv ≫
            (Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.map
              (Etale.dualizingComplexTensorMap Λ g K)) ≫
        Etale.dualizingComplexTensorMap Λ f
          ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) g).obj K))

/-- Arbitrary finite-type base changes in the fixed purity setting, with the
base-changed compactification and every representative of a pro-etale Dctf input.
Source: blueprint thm-pur-cohomological-smoothness, clause 3
(blueprint: thm-pur-cohomological-smoothness). -/
noncomputable def comparedSmoothTensorBaseChangeClause
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] : Prop :=
  ∀ (X' Y' : Scheme.{u}) [X'.Over (Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    (u' : X' ⟶ X) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
    [u'.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [v.IsOver (Spec (.of P.field.k))] (sq : IsPullback u' f' f v),
    letI := ((HasCompactification.compactification f).ofIsPullback sq).hasCompactification
    letI : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
    ∀ K : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Y
        ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K) →
      smoothTensorBaseChangeCoherence P.Coefficient sq K

/-- The base-change equation with the same canonical compactification as the
recorded cohomological-smoothness definition. Nagata supplies it internally.
Source: blueprint thm-pur-cohomological-smoothness, clause 3
(blueprint: thm-pur-cohomological-smoothness). -/
noncomputable def comparedSmoothBaseChangeCoherence
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] : Prop :=
  letI := (P.comparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
  comparedSmoothTensorBaseChangeClause P f

/-- Composition coherence with the canonical Nagata compactifications used by
comparedDualizing; the induced comparison is constructed above from their triangle.
Source: blueprint thm-pur-cohomological-smoothness, clause 4
(blueprint: thm-pur-cohomological-smoothness). -/
noncomputable def comparedSmoothCompositionCoherence
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [Y.Over (Spec (.of P.field.k))] [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] : Prop :=
  letI := (P.comparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
  letI := (P.comparedCompactification g (Z ↘ Spec (.of P.field.k))).hasCompactification
  letI := (P.comparedCompactification (f ≫ g) (Z ↘ Spec (.of P.field.k))).hasCompactification
  smoothTensorCompositionCoherence P.Coefficient f g

/-- Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-cohsm/thm-pur-cohomological-smoothness.proof.md, both paragraphs;
DAG thm-pur-cohomological-smoothness, proof Steps 1--10
(blueprint: thm-pur-cohomological-smoothness).

The four orientation-free assertions for smooth separated f: the canonical tensor
formula, invertibility with a Dctf inverse, arbitrary base change including equality
of tensor maps, and equality of tensor maps under exceptional composition.

Proof, following the ten DAG steps:

1. Work at A = A_(E,n). Finite-type k-schemes are Noetherian
(lem-weil-pbc-finite-type-over-noetherian). Nagata compactifies f; the compactification
is finite-dimensional by lem-kun-dimension-finite-type, with bound zero allowed when
empty. The coefficient quotient is finite and annihilated by l^n, which is invertible
on k since l ≠ p. These verify the hypotheses of thm-asd-smooth-tensor and
thm-sf-ambient-adjoint-class. The ordinary affine-space adjunction and historical
Kummer normalization are cor-amb-affine-space-adjunction and
prop-pur-affine-line-orientation-uniqueness; neither chooses an orientation here.

2. Write V_T = nu_T*. By lem-sf-proetale-constructible-origin choose a bounded
constructible etale H representing K. The unit of thm-weil-pbc-site-comparison
identifies Rnu_* V_Y H with H. The exceptional defining formula then identifies
f!K with V_X f×H and omega_f with V_X W_f, W_f = f×A_Y. Transport the etale counit
through the Hom bijection of thm-sf-ambient-adjoint-class and the compact-support
comparison C of lem-sf-class-compact-support-comparison. Its formula is
ε^P_(V_Y H) = V_Y(ε^F_H) composed with C_(f×H): both counits transpose the same
identity. Naturality makes this independent of the etale antecedent.

3. Apply thm-asd-smooth-tensor: W_f = L[2d] for a locally constant free rank-one
sheaf L, and the canonical theta is invertible. It is the specified inverse
projection/counit transpose, not an arbitrary isomorphism. No trivialization or
identification of L with a Tate twist is chosen.

4. Construct the inverse L^vee[-2d] using def-pur-sheaf-hom. On a trivializing cover
the evaluations are multiplication A tensor A to A with inverse a maps to 1 tensor a.
Their isomorphy follows from lemma-weil-pbc-geometric-stalk-conservative. Both lines
are flat because tensor by a trivial line preserves injections locally; both are
constructible. Their derived evaluations cancel the opposite shifts. Transport by
V_X and lem-weil-pbc-ringed-topoi-derived-tensor-pullback. The pulled-back lines
remain flat and constructible, so the inverse is Dctf as required by the definition.

5. lem-sf-comparison-tor-amplitude reflects the finite Tor interval of K to H.
The line description makes W_f bounded constructible. Apply
lem-pur-projection-comparison-etale-origin to W_f and H: its equation identifies
the actual projection maps through C. Use lem-weil-pbc-comparison-pullback and the
monoidal comparison to identify the tensor sources. Finite Tor is used to keep
these comparisons within their bounded-below domains.

6. Substitute that projection equation and Step 2's counit equation into the
transpose of V_X theta_(f,H). It becomes inverse PF followed by 1 tensor ε and
the unit constraint. fix-prop-projection-formula makes PF invertible here. Tensor
symmetry matches the source order in def-pur-co-smoothness. Injectivity of the
restricted Hom bijection identifies the transported map with the specified
pro-etale theta, proving its isomorphy naturally in K.

7. lem-pur-smb-extraordinary supplies β_K for every Cartesian square in the fixed
setting. At the coefficient unit, the exact constant pullback and unit constraint
give b. prop-asd-smooth-base-change gives the etale equality between u*theta followed
by β_K and theta' following 1 tensor b. Realize it using the pullback and tensor
comparisons of Step 5. thm-cbc-finite-level-proetale identifies the compact-support
exchange; Step 2 identifies both counits. Transposing both exchanges gives the same
v*ε composed with inverse Ex_!, so the realized β is the specified pro-etale one.
Step 6 identifies the two thetas. This proves exactly smoothTensorBaseChangeCoherence,
including all monoidal, square and unit comparisons, without a condition on v.

8. Steps 4, 6 and 7 prove the three clauses of IsCohomologicallySmoothCompared.
Apply the same argument separately to g. lem-pur-co-smooth-composition supplies
the object formula, but equality of canonical tensor maps still needs Steps 9--10.

9. thm-sf-comp-composition and the restricted Hom bijections identify (fg)! with
f!g! by pasting adjunctions. The canonical compact-support comparison is constructed
by compatible compactifications and common refinements, as in smoothCompactSupportCompIso.
Its mate is smoothExceptionalCompIso, with pasted counit ε_g composed with g_!ε_f
by lem-weil-pbc-mate-pasting. The map q is theta_(f,W_g) followed by c_A inverse,
exactly smoothDualizingCompMap. Step 4 makes W_g Dctf, so q is invertible by Step 6.
For Dctf K, the exceptional constructible and Tor preservation gives g!K Dctf too.

10. Apply lem-pur-composite-tensor-transpose to these Hom bijections. Strong
monoidality is lem-pur-derived-pullback-tensor-iso; the projection maps are those of
def-exchange-projection, their coefficient/unit coherence is
lem-pur-projection-formula-coefficient-coherence, and their invertibility is
fix-prop-projection-formula. K, W_g and g!K are in the required finite Tor domains.
The tensor inputs have bounded-below etale-origin witnesses, and compact support
preserves bounded constructibility by prop-finite-compact-support-constructibility
and etale origin by thm-sf-comp-composition. Thus the restricted transposes are
available. The two inverse transposes are the same inverse projection followed by
the same two counits in adjunction order. Injectivity gives the displayed equality
in smoothTensorCompositionCoherence, with its associator, monoidal pullback and
pullback-composition maps. Apply V_X to obtain the pro-etale equation; symmetry
recovers the source's pullback-first ordering. No ambient pro-etale adjunction is used.
-/
theorem isCohomologicallySmooth_of_smooth
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f]
    [LocallyOfFiniteType f]
    [QuasiCompact f]
    (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    IsCohomologicallySmoothCompared P f ∧
      comparedSmoothBaseChangeCoherence P f ∧
      ∀ {Z : Scheme.{u}}
        [Z.Over (Spec (.of P.field.k))]
        [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
        [QuasiCompact (Z ↘ Spec (.of P.field.k))]
        (g : Y ⟶ Z)
        [g.IsOver (Spec (.of P.field.k))]
        [IsSeparated g]
        [LocallyOfFiniteType g]
        [QuasiCompact g]
        (e : ℕ)
        [SmoothOfRelativeDimension e g],
        comparedSmoothCompositionCoherence P f g := by
  sorry

end AlgebraicGeometry.ProEtale
