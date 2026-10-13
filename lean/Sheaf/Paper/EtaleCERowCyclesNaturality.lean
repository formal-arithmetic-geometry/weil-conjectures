/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.EtaleCERowOrdinaryComparison
public import Sheaf.Paper.EtaleCECanonicalRowComparison

/-! # CE row cycles under diagonal-compatible total maps

Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-row-cycles-naturality).
-/

@[expose] public section

universe uNatural
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 1000000 in
-- Elaborate the dependent CE and normalized page data together.
/-- The inverse canonical cycle comparison takes related filtered representatives to
related row cycles. This is a degreewise statement, before taking homology; it assumes
no augmentation compatibility and no normalization of higher spectral-sequence pages.
Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-row-cycles-naturality).

Proof. In total degree n=q+p the second filtration is the finite sum of diagonal
summands with complex index at least q. Its quotient by the next step keeps only
the summand with index q, which is the row term in resolution degree p. Project the
equality relating x and y onto that summand. The summand equation for u, transported
through totalSectionsIso_formula and the naturality of ceSectionsUnit, identifies
this projected map with the degree-p component of ceRowSectionsMap f (phi.f q).
The equations for z and zprime identify the same projections with their graded
cycle inclusions. The canonical rowCyclesIso was normalized by diagonal inclusion;
its inverse therefore takes these projections to the corresponding row cycles.
Apply monicity of the target row iCycles to conclude the stated equality of cycle
maps. The construction kills every higher-index summand by the quotient projection;
negative resolution indices vanish by extension by zero. At p=0 the row cycle
kernel calculation is unchanged, and zero rows or empty diagonals give the unique
map from or to a zero object. No ordinary cohomology or derived-functor comparison
is involved. -/
theorem etaleCE_row_cycles_naturality
    {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (D : EtaleTermwiseHypercohomology X K)
    (D' : EtaleTermwiseHypercohomology Y L)
    (φ : (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj D.I ⟶ D'.I)
    (u : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj D.sheafTotal ⟶ D'.sheafTotal)
    (hu : ∀ (m : ℕ) (q n : ℤ) (h : (m : ℤ) + q = n),
        (upperStar AddCommGrpCat.{uNatural + 1} f).map
            ((HomologicalComplex.extendXIso
              (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) ≫ u.f n =
          (φ.f q).f m ≫
            (HomologicalComplex.extendXIso
              (((𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D'.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D'.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) :
      let b := D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv
      ∀ (A : AddCommGrpCat.{uNatural + 1}) (p : ℕ) (q : ℤ)
        (x : A ⟶ (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
          (q + (p : ℤ)))
        (y : A ⟶ (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
          (q + (p : ℤ)))
        (z : A ⟶ (D.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1}))
        (z' : A ⟶ (D'.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1})),
        x ≫ (D.L.step q).arrow.f (q + (p : ℤ)) ≫ b.f (q + (p : ℤ)) =
          y ≫ (D'.L.step q).arrow.f (q + (p : ℤ)) →
        z ≫ (D.L.complexCycles q (q + (p : ℤ)) 1).arrow =
          x ≫ (D.L.complexQuotientπ q (q + 1) (by omega)).f (q + (p : ℤ)) →
        z' ≫ (D'.L.complexCycles q (q + (p : ℤ)) 1).arrow =
          y ≫ (D'.L.complexQuotientπ q (q + 1) (by omega)).f (q + (p : ℤ)) →
        z ≫ (D.rowCyclesIso p q).inv ≫ HomologicalComplex.cyclesMap
            (ceRowSectionsMap f (φ.f q)) p =
          z' ≫ (D'.rowCyclesIso p q).inv := by sorry

end AlgebraicGeometry.Etale
