/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.ProperBaseChangeFourArrows
import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CondensedAmbientExchange
import Sheaf.Paper.FourArrows
import Sheaf.Paper.FourCorners
import Sheaf.Paper.PerfectProjectionFormula

/-!
# Finite-level exchange rectangle

Source: blueprint, node `lem-weil-pbc-finite-level-rectangle`, order 1344;
Stacks Project, Tags 0E48, 0B56 and 07A7
(blueprint: lem-weil-pbc-finite-level-rectangle).

The arrows are the specified finite projection and exchange maps, with their
quotient-coefficient actions retained. Index n denotes the positive exponent n+1.
-/

@[expose] public section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A]
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The canonical four-arrow exchange rectangle commutes at every positive level.
Source: blueprint order 1344; Stacks Remark 21.50.2, Tag 0E48, with the maps of
Tags 0B56 and 07A7 (blueprint: lem-weil-pbc-finite-level-rectangle).
Proof: (1) The four-corner coefficient identifications commute with quotient
projections, so ordinary uncompleted pullback identifies the pulled quotient
with the quotient at the source. The canonical K-flat comparison identifies
E tensor P_n with E_n, retaining its finite scalar action. Perfect projection
formula identifies the two horizontal arrows with the specified projection
isomorphisms. The right vertical arrow is the canonical finite exchange itself;
its witness only certifies invertibility. (2) Apply the Cartesian-square clause
of projection-formula/base-change naturality to K and P_n. Under exactly the
corner and arrow identifications, its first route is h_n followed by v'_n and
its second is v_n followed by h'_n. The resulting equality is the displayed
one; no independent finite-level base-change isomorphism is chosen. -/
theorem properBaseChangeFiniteLevelRectangle
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (d : ProEtaleAdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : fourCornerDerived X (adicDatumRing X d))
    (C : CochainComplex (proEtaleRingModules X (adicDatumRing X d)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K)
    (hK : IsCompletedIntrinsicallyDerivedComplete X d r a ha C eC)
    (W : ∀ n : ℕ, ProEtale.FiniteCoefficientDerivedCategoryPlus X (fourArrowQuotient d n))
    (w : ∀ n : ℕ, ProEtale.EtaleOriginWitness X (fourArrowQuotient d n) (W n))
    (e : ∀ n : ℕ, (fourArrowOriginTransport X d n).obj (W n).obj ≅
      (adicDatumReduction X d n).obj K) (n : ℕ) :
    (properBaseChangeFourArrows sq d r a ha K C eC hK W w e n).1.hom ≫
        (properBaseChangeFourArrows sq d r a ha K C eC hK W w e n).2.2.2.hom =
      (properBaseChangeFourArrows sq d r a ha K C eC hK W w e n).2.2.1 ≫
        (properBaseChangeFourArrows sq d r a ha K C eC hK W w e n).2.1.hom := by
  sorry

end AlgebraicGeometry.Scheme
