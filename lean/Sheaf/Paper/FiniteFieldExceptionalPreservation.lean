/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.Paper.OrgogozoInductionData
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.RightDerivedFunctorUpperBound
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.ConstructibleSheaf.Defs
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Paper.EtaleUnboundedRestrictionComparison
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.AlgebraicGeometry.QuasiExcellentEtaleDirectImageFiniteness

/-!
# Finite-field exceptional preservation and finite-free coefficient comparison

Source: Bhatt--Scholze, The pro-etale topology for schemes, Section 6.7,
Theorem 6.7.1 and Lemma 6.7.18 (blueprint: lem-per-finite-exceptional-preservation).
The categories here are ordinary small-etale derived categories. The existing scalar
extension is identified with derived tensor by its representative-normalized scalarTensorIso.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Ordinary small-etale exceptional adjunction over finite fields, its restriction to
bounded constructible complexes, and finite-free coefficient comparison.
Source: Bhatt--Scholze, Section 6.7, Theorem 6.7.1 and Lemma 6.7.18
(blueprint: lem-per-finite-exceptional-preservation).

Proof:
1. Fix a compactification f = pj. Its middle scheme is Noetherian by
lem-weil-pbc-finite-type-over-noetherian. Finite type over a Noetherian scheme is finite
presentation by lem-weil-pbc-finite-type-noetherian-finite-presentation. Apply proper
finiteness (lem-per-quasi-excellent-etale-direct-image-finiteness) to p. Exact j_! preserves
constructible sheaves by retaining their strata and adding the zero complement; hence
Rp_*j_! preserves bounded constructibility (lem-weil-pbc-extension-by-zero-exact).
2. The ambient adjoint exists by thm-amb-etale-exceptional-adjoint. Proper finiteness gives
one upper cohomological dimension bound. Sheaves are Grothendieck abelian by
lem-weil-pbc-ring-sheaves-grothendieck; lem-etale-derived-functor-upper-amplitude extends
this bound to unbounded complexes. Exact j_! has amplitude zero, so
lem-etale-upper-shriek-bounded-below-from-amplitude restricts the adjoint to D+.
3. Exact inverse image preserves the finite stratifications and constant finite values
(lemma-constructible-pullback-stratification, lemma-constructible-pullback-constant,
prop-weil-pbc-inverse-image-modules-exact). Tensor with the etale Tate line is exact and
preserves them too (lem-asd-etale-finite-twist-pullback). Thus affine-space twisted pullback
preserves bounded constructibility.
4. For a closed immersion i with open complement h, direct-image finiteness makes
Rh_*h^*M bounded constructible. The closed-support triangle
(lem-exc-closed-support-triangle) and thm-constructible-serre give the same for i_*Ri^!M.
The scalar-compatible identity i^*i_* = 1 of lem-kun-04ca and exact inverse image recover
bounded constructibility of Ri^!M. No regularity of i is needed.
5. Choose finitely many affine charts of X mapping to affine charts V of Y and factor
each chart as a closed immersion into affine space over V. These ambient schemes are
excellent by lem-exc-finite-type-localization-excellent. Their compactifications come from
lemma-nagata-relative-affine-space-open-immersion and
lemma-nagata-projective-space-base-change-proper, and those of open and closed immersions.
6. Compact-support composition and open adjunction (lem-amb-etale-compact-comparisons,
lem-amb-etale-adjoint-locality), cor-amb-affine-space-adjunction and
lem-exc-closed-ambient identify the restriction of f^!L on each chart with the closed
exceptional restriction of its twisted affine-space pullback. Yoneda on D+ gives this
identification; steps 3 and 4 prove local bounded constructibility.
7. Take common bounds over the finite chart cover. Refine the local strata successively
by subtracting earlier opens; this gives a finite locally closed constructible partition.
If X is empty, the output is zero. Fullness restricts the ambient adjunction and its Hom
bijections to the two bounded constructible subcategories.
8. A finite field extension C/B has a finite basis. On restriction of scalars, extension
is the corresponding finite direct sum, hence exact and constructibility preserving.
Restriction is exact and reflects isomorphisms. The scalar adjunction, with unit
x maps to 1 tensor x, is lem-pur-sheaf-ring-derived-coefficient-adjunction; its ordinary
constant-coefficient realization is scalarExtension.
9. Restriction commutes with j_! on the underlying sheaves and with Rp_* on D+ by
lem-sbc-canonical-restrict-scalars-functor-comparisons, giving U_Y F_C = F_B U_X.
10. Transpose F_B of the scalar unit followed by this identity to obtain c. In a finite
basis its restriction is the canonical finite-biproduct comparison for additive Rp_*j_!,
so c is invertible. This is the existing proper/open compactSupportMap, normalized by
its scalar and geometric adjunctions; its construction is independent of the basis.
11. Apply the scalar adjunction, exceptional adjunctions, and c to identify naturally
Hom_B(H,U_X G_C N) with Hom_B(H,G_B U_Y N). Yoneda gives a uniquely normalized
isomorphism b: U_X G_C = G_B U_Y.
12. The existing mateMap is the exceptional transpose of c inverse followed by T_Y of
the B-exceptional counit. Under b, each basis-summand inclusion is G_B of that inclusion,
by the triangle identities and step 10. Thus its restriction is the finite-biproduct
comparison for G_B, which is invertible because right adjoints preserve finite products.
Restriction reflects invertibility. Naturality follows from the defining transpose and
retains precisely the displayed exceptional counit normalization. -/
theorem finiteField_exceptional_preservation
    (l : ℕ) [Fact l.Prime]
    (B : Type (u + 1)) [Field B] [Finite B] [CharP B l]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (_hX : Orgogozo.IsExcellentScheme X) (_hY : Orgogozo.IsExcellentScheme Y)
    (_hlX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] :
    HasBoundedBelowUpperShriek (ModuleCat.{u + 1} B) f ∧
    (∀ K : DerivedCategoryModule B X,
      DerivedCategory.isBoundedConstructible B X K →
        DerivedCategory.isBoundedConstructible B Y
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).obj K)) ∧
    (∀ L : DerivedCategoryModule B Y,
      DerivedCategory.isBoundedConstructible B Y L →
        DerivedCategory.isBoundedConstructible B X
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} B) f).obj L)) ∧
    (∃ (F : BoundedConstructibleDerivedCategory B X ⥤
          BoundedConstructibleDerivedCategory B Y)
       (G : BoundedConstructibleDerivedCategory B Y ⥤
          BoundedConstructibleDerivedCategory B X)
       (a : F ⊣ G)
       (eF : F ⋙ (DerivedCategory.isBoundedConstructible B Y).ι ≅
         (DerivedCategory.isBoundedConstructible B X).ι ⋙
           rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)
       (eG : G ⋙ (DerivedCategory.isBoundedConstructible B X).ι ≅
         (DerivedCategory.isBoundedConstructible B Y).ι ⋙
           rightDerivedUpperShriek (ModuleCat.{u + 1} B) f),
      ∀ (K : BoundedConstructibleDerivedCategory B X)
        (L : BoundedConstructibleDerivedCategory B Y) (h : F.obj K ⟶ L),
        (DerivedCategory.isBoundedConstructible B X).ι.map (a.homEquiv K L h) ≫
            eG.hom.app L =
          (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f).homEquiv K.obj L.obj
            (eF.inv.app K ≫ (DerivedCategory.isBoundedConstructible B Y).ι.map h)) ∧
    (∀ (C : Type (u + 1)) [Field C] [Finite C] [Algebra B C],
      ∃ c : _root_.DerivedCategory.Plus.ι ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} B) f ⋙
            scalarExtension (algebraMap B C) Y ≅
        _root_.DerivedCategory.Plus.ι ⋙ scalarExtension (algebraMap B C) X ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} C) f,
        (∀ K : _root_.DerivedCategory.Plus
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
          c.hom.app K = ExceptionalCoefficients.compactSupportMap (algebraMap B C)
            (HasCompactification.compactification f) K.obj) ∧
        ∃ α : (DerivedCategory.isBoundedConstructible B Y).ι ⋙
            rightDerivedUpperShriek (ModuleCat.{u + 1} B) f ⋙
              scalarExtension (algebraMap B C) X ≅
          (DerivedCategory.isBoundedConstructible B Y).ι ⋙
            scalarExtension (algebraMap B C) Y ⋙
              rightDerivedUpperShriek (ModuleCat.{u + 1} C) f,
          (∀ L : BoundedConstructibleDerivedCategory B Y,
            α.hom.app L = ExceptionalCoefficients.mateMap (algebraMap B C) f L.obj) ∧
          ∀ L : BoundedConstructibleDerivedCategory B Y,
            (rightDerivedLowerShriek (ModuleCat.{u + 1} C) f).map (α.hom.app L) ≫
                (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} C) f).counit.app
                  ((scalarExtension (algebraMap B C) Y).obj L.obj) =
              ExceptionalCoefficients.comparisonInverse (algebraMap B C)
                  (HasCompactification.compactification f)
                  ((rightDerivedUpperShriek (ModuleCat.{u + 1} B) f).obj L.obj) ≫
                (scalarExtension (algebraMap B C) Y).map
                  ((rightDerivedUpperShriekAdjunction
                    (ModuleCat.{u + 1} B) f).counit.app L.obj)) := by
  sorry

end AlgebraicGeometry.Etale
