/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.AlgebraicGeometry.AffineTraceConstruction
public import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
public import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.Paper.EtaleCtfChartDomain
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The ordered coefficient square for a specified compactification

Source: main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
reduction-exceptional proof, Charts, ordered projective-line integration
(blueprint: lem-sp-ordered-compactification-scalar-square).

The ordered functors and the coherent composition comparison are the existing
`affineTraceLeft` and `affineTraceCompactSupportComparison`. Only their coefficient
arrow and their comparison to the specified candidate are assembled here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

open ProEtale.CoefficientCompatibility ProEtale.AdjunctionTransfer

/-- The ordered coefficient arrow B_d, with identity at zero. At the next coordinate
first apply B_d to L_d M, then apply F_{d,B} to the proper/open line coefficient map.
The latter is definitionally the proper counit mate followed by the open tensor map.
Source: blueprint Charts, ordered left coefficient square
(blueprint: lem-sp-ordered-compactification-scalar-square). -/
def orderedAffineCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (S : Scheme.{u}) :
    (d : ℕ) → (M : DerivedCategoryModule A (affineTraceTower S d)) →
      (scalarExtension φ S).obj ((affineTraceLeft A S d).obj M) ⟶
        (affineTraceLeft B S d).obj ((scalarExtension φ (affineTraceTower S d)).obj M)
  | 0, M => 𝟙 ((scalarExtension φ S).obj M)
  | d + 1, M =>
    orderedAffineCoefficientMap φ S d ((affineTraceLineLeft A (affineTraceTower S d)).obj M) ≫
      (affineTraceLeft B S d).map
        (etaleCoefficientMap φ (affineTraceLineCompactification (affineTraceTower S d)) M)

/-- C_{d,R} for an arbitrary specified compactification, on bounded-below inputs.
The middle comparison is the canonical coherent composition of the ordered tower,
followed by the canonical common-refinement comparison to c. Inclusion comparisons
identify its endpoints with the unbounded candidates. At d=0 the tower comparison
is the inverse identity normalization, even when c is not the identity candidate.
Source: blueprint Charts; lem-amb-etale-compact-comparisons
(blueprint: lem-sp-ordered-compactification-scalar-square). -/
def orderedCompactificationComparison
    (R : Type (u + 1)) [CommRing R] [Finite R] (k : Type u) [Field k]
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (d : ℕ) (c : Compactification (affineTraceProjection S d))
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (affineTraceLeft R S d).obj M.obj ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj M.obj :=
  letI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (S ↘ Spec (.of k))
  letI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  letI : IsNoetherian S := ⟨⟩
  ((affineTracePlusCompatibility R S d).app M).symm ≪≫
    _root_.DerivedCategory.Plus.ι.mapIso
      ((affineTraceCompactSupportComparison R S d).app M ≪≫
        (rightDerivedLowerShriekOfCompactificationPlusIso R
          (HasCompactification.compactification (affineTraceProjection S d)) c).app M) ≪≫
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility (ModuleCat.{u + 1} R) c).app M

/-- Compare to c by first comparing to an arbitrary c' and then through any common
refinement e. Refinement arrows need not have Cartesian open squares or be dense.
Source: blueprint Charts, independence of auxiliary refinements
(blueprint: lem-sp-ordered-compactification-scalar-square). -/
def orderedCompactificationComparisonVia
    (R : Type (u + 1)) [CommRing R] [Finite R] (k : Type u) [Field k]
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (d : ℕ) (c c' e : Compactification (affineTraceProjection S d))
    (r : e.Refinement c') (s : e.Refinement c)
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (affineTraceLeft R S d).obj M.obj ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj M.obj :=
  orderedCompactificationComparison R k S d c' M ≪≫
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} R) c').app M).symm ≪≫
    _root_.DerivedCategory.Plus.ι.mapIso
      (((rightDerivedLowerShriekOfCompactificationPlusRefinementIso R r).app M) ≪≫
        ((rightDerivedLowerShriekOfCompactificationPlusRefinementIso R s).app M).symm) ≪≫
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility (ModuleCat.{u + 1} R) c).app M

/-- The canonical comparison to every specified compactification intertwines the
ordered coefficient arrow with its proper/open coefficient arrow. The scalar-extended
input is bounded below, and the same comparison is obtained through every common
refinement, for both coefficients. The coherent composition maps defining C are
associative, so this is independent of their parenthesization as well.
Source: main-20261015, reduction-exceptional proof, Charts
(blueprint: lem-sp-ordered-compactification-scalar-square).

Proof:
1. Finite type over the field makes all standing schemes Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). The affine tower has separated finite-type
   projections (def-amb-affine-trace-tower). By lem-sp-etale-ctf-chart-domain each line
   functor, compact-support candidate and scalar extension preserves Dctf. Thus every
   input to a comparison in the induction is bounded below, without assuming B flat.
2. The line coefficient arrow is exactly the proper map followed by the open tensor
   comparison (lem-sp-et-proet-coefficient-compatibility). At zero the identity
   normalization makes B_0 and the identity candidate's coefficient map identities.
3. Choose intermediate compactifications for p_r by def-asd-compactifiable, with the
   identity at zero. Their binary composition comparisons alpha give D_{r+1} = alpha
   composed with D_r L_r (lem-amb-etale-compact-comparisons).
4. Apply the binary coefficient composition square of
   lem-sp-et-proet-coefficient-compatibility to u_r,p_r. Precompose with T(D_r) and
   substitute the induction hypothesis at L_r M.
5. Naturality of D_{r,B} at the line coefficient arrow moves that arrow across D_r.
   The recursive formulas for B_{r+1} and D_{r+1} give the induction step.
6. Compare the final auxiliary candidate to the specified c. Its coefficient refinement
   square, precomposed with T(D_d), gives the displayed square for C_d. The same argument
   at zero compares the identity candidate to an arbitrary compactification of 1_S.
7. The independent refinement cocycle and associative composition of
   lem-amb-etale-compact-comparisons identify every auxiliary choice with the specified C.
   The coefficient refinement square holds through any common refinement, and its
   identity and composition laws respect these identifications. No flatness or finite
   projective-dimension hypothesis on B/A enters any step. -/
theorem orderedCompactification_scalar_square
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) (n : ℕ)
    (_hA : ((ℓ ^ n : ℕ) : A) = 0) (_hB : ((ℓ ^ n : ℕ) : B) = 0)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (d : ℕ) (c : Compactification (affineTraceProjection S d))
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hM : etaleProperty A (affineTraceTower S d) M.obj) :
    ∃ hMB : _root_.DerivedCategory.TStructure.t.plus
        ((scalarExtension φ (affineTraceTower S d)).obj M.obj),
      ((scalarExtension φ S).map (orderedCompactificationComparison A k S d c M).hom ≫
          etaleCoefficientMap φ c M.obj =
        orderedAffineCoefficientMap φ S d M.obj ≫
          (orderedCompactificationComparison B k S d c
            ⟨(scalarExtension φ (affineTraceTower S d)).obj M.obj, hMB⟩).hom) ∧
      (∀ (c' e : Compactification (affineTraceProjection S d))
        (r : e.Refinement c') (s : e.Refinement c),
        orderedCompactificationComparisonVia A k S d c c' e r s M =
          orderedCompactificationComparison A k S d c M ∧
        orderedCompactificationComparisonVia B k S d c c' e r s
            ⟨(scalarExtension φ (affineTraceTower S d)).obj M.obj, hMB⟩ =
          orderedCompactificationComparison B k S d c
            ⟨(scalarExtension φ (affineTraceTower S d)).obj M.obj, hMB⟩) := by
  sorry

end AlgebraicGeometry.Etale
