/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.FiniteCompactCoefficients.FiniteCoefficientCompactSupportCompatibility
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # The ordered compactification scalar square over the corrected field domain

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: ordered projective-line integration
(blueprint: lem-sp-ordered-compactification-scalar-square).

The ordered coefficient recursion uses ordinary scalar extension and the canonical
proper/open coefficient map, with the coherent comparison to a specified compactification.
The field may be finite or algebraically closed,
including characteristic zero when it is algebraically closed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

open ProEtale.OrdinaryScalarSite ProEtale.FiniteCompactCoefficients

/-- The ordered coefficient arrow for ordinary scalar extension, with identity at zero.
At a successor, apply the preceding coefficient arrow to the last line's output,
then map the standard compactification's proper/open beta through the preceding tower.
Source: latest blueprint, reduction-exceptional proof, Charts
(blueprint: lem-sp-ordered-compactification-scalar-square). -/
def orderedFiniteAffineCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (S : Scheme.{u}) :
    (d : ℕ) → (M : DerivedCategoryModule A (affineTraceTower S d)) →
      (scalar S.smallEtaleTopology φ).obj ((affineTraceLeft A S d).obj M) ⟶
        (affineTraceLeft B S d).obj
          ((scalar (affineTraceTower S d).smallEtaleTopology φ).obj M)
  | 0, M => 𝟙 ((scalar S.smallEtaleTopology φ).obj M)
  | d + 1, M =>
    orderedFiniteAffineCoefficientMap φ S d
        ((affineTraceLineLeft A (affineTraceTower S d)).obj M) ≫
      (affineTraceLeft B S d).map
        ((beta φ (affineTraceLineCompactification (affineTraceTower S d))).app M)

/-- The canonical coherent tower comparison to the specified compactification on D+.
It uses the existing affine composition comparison and canonical pairwise comparison,
transported through the two bounded-below inclusion compatibility isomorphisms.
At zero its tower factor is the inverse identity normalization.
Source: latest blueprint, reduction-exceptional proof, Charts
(blueprint: lem-sp-ordered-compactification-scalar-square). -/
def orderedFiniteCompactificationComparison
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

/-- The comparison through every auxiliary compactification and common refinement.
The two refinement factors are the actual canonical D+ comparison isomorphisms;
no Cartesian-square or density hypothesis is imposed on their refinement arrows.
Source: latest blueprint, reduction-exceptional proof, Charts, refinement independence
(blueprint: lem-sp-ordered-compactification-scalar-square). -/
def orderedFiniteCompactificationComparisonVia
    (R : Type (u + 1)) [CommRing R] [Finite R] (k : Type u) [Field k]
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (d : ℕ) (c c' e : Compactification (affineTraceProjection S d))
    (r : e.Refinement c') (s : e.Refinement c)
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (affineTraceLeft R S d).obj M.obj ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj M.obj :=
  orderedFiniteCompactificationComparison R k S d c' M ≪≫
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} R) c').app M).symm ≪≫
    _root_.DerivedCategory.Plus.ι.mapIso
      (((rightDerivedLowerShriekOfCompactificationPlusRefinementIso R r).app M) ≪≫
        ((rightDerivedLowerShriekOfCompactificationPlusRefinementIso R s).app M).symm) ≪≫
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility (ModuleCat.{u + 1} R) c).app M

/-- The ordered proper/open coefficient recursion agrees with the coefficient map for
any specified compactification. The equality also uses the same canonical comparison
through every common refinement, including arbitrary compactifications at dimension zero.

Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: ordered projective-line integration
(blueprint: lem-sp-ordered-compactification-scalar-square).

Proof:
1. Finite type over a field makes the base Noetherian. The coordinate tower remains
   separated and of finite type. The constructible finite-Tor chart-domain theorem
   gives bounded constructible scalar extension, and hence its lower bound hMB, with
   no flatness or finite projective-dimension assumption on B over A.
2. Identify orderedFiniteAffineCoefficientMap with affineTraceExchangeTower by induction:
   both are identities at zero, and the successor applies the previous map before
   the last line's proper counit mate and canonical open tensor comparison.
3. The affine bounded/unbounded restriction comparison and pairwise compactification
   comparison identify orderedFiniteCompactificationComparison with the unbounded tower
   comparison followed by the comparison to the specified compactification c.
4. Paste the unbounded affine scalar square with the pairwise compactification scalar
   square at M.obj. Functoriality and associativity give the displayed equality.
5. Replace refinement comparisons by canonical pairwise comparisons. The pairwise
   cocycle cancels the intermediate compactification and gives the two Via equalities.
   Identity and composition normalization also give dimension zero for nonidentity c;
   associativity of the existing composition comparison removes parenthesization choices.
-/
theorem orderedCompactification_scalar_square_finiteCoefficients
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (_hk : Finite k ∨ IsAlgClosed k) (_hchar : ringChar k ≠ ℓ)
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (φ : A →+* B) (n : ℕ)
    (_hA : ((ℓ ^ n : ℕ) : A) = 0) (_hB : ((ℓ ^ n : ℕ) : B) = 0)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (d : ℕ) (c : Compactification (affineTraceProjection S d))
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hM : Input A (affineTraceTower S d) M.obj) :
    ∃ hMB : _root_.DerivedCategory.TStructure.t.plus
        ((scalar (affineTraceTower S d).smallEtaleTopology φ).obj M.obj),
      ((scalar S.smallEtaleTopology φ).map
          (orderedFiniteCompactificationComparison A k S d c M).hom ≫
          (beta φ c).app M.obj =
        orderedFiniteAffineCoefficientMap φ S d M.obj ≫
          (orderedFiniteCompactificationComparison B k S d c
            ⟨(scalar (affineTraceTower S d).smallEtaleTopology φ).obj M.obj, hMB⟩).hom) ∧
      (∀ (c' e : Compactification (affineTraceProjection S d))
        (r : e.Refinement c') (s : e.Refinement c),
        orderedFiniteCompactificationComparisonVia A k S d c c' e r s M =
          orderedFiniteCompactificationComparison A k S d c M ∧
        orderedFiniteCompactificationComparisonVia B k S d c c' e r s
            ⟨(scalar (affineTraceTower S d).smallEtaleTopology φ).obj M.obj, hMB⟩ =
          orderedFiniteCompactificationComparison B k S d c
            ⟨(scalar (affineTraceTower S d).smallEtaleTopology φ).obj M.obj, hMB⟩) := by
  sorry

end AlgebraicGeometry.Etale
