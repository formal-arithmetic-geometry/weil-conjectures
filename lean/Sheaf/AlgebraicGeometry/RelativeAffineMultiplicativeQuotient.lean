module

public import Sheaf.AlgebraicGeometry.RelativeMultiplicativeType
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

import Sheaf.AlgebraicGeometry.FppfSheafRepresentabilityDescentData
import Sheaf.AlgebraicGeometry.FppfFamilyAffineEffectivityReduction
import WeilConjectures.AlgebraicGeometry.AffineFpqcDescent
import Sheaf.AlgebraicGeometry.FpqcAffineDescent
import WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.Smooth.Basic

/-! # Relative affine quotients by normal multiplicative type subgroups

Source: Conrad, Reductive group schemes, Lemma 3.3.2, quotient discussion,
printed pp.97--98; Stacks, Tags 03C5, 0245, 02W3 and 05B5
(blueprint: lem-sfb-relative-affine-multiplicative-quotient).

The quotient predicate specifies the actual fppf sheafification map, its
scheme-theoretic kernel and its torsor isomorphism with both projection formulas.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonObj

namespace AlgebraicGeometry

/-- A smooth affine group with connected geometric fibres has an affine quotient
by a closed normal subgroup of multiplicative type. Every conclusion is retained
by the actual pullback along an arbitrary base morphism, including sheafification.

Source: Conrad, Reductive group schemes, Lemma 3.3.2, quotient discussion,
printed pp.97--98, and Definition B.1.1, printed p.280; Stacks, Tags 03C5,
0245, 02W3 and 05B5 (blueprint: lem-sfb-relative-affine-multiplicative-quotient).

Proof plan, following the eight accepted steps:
1. Choose affine fppf charts splitting N as D_R(M). Right translation gives a
   group-algebra coaction on A = Gamma(H,O_H). The coaction-grading lemma
   (lem-sfb-group-algebra-coaction-grading) gives A = direct sum A_m. Put B = A_0.
2. The map (h,n) to (h,hn) into H times H is a closed immersion, by the closed
   immersion base-change and affine-cover criteria. Its coordinate-ring map is
   surjective. Lifting each basis element and extracting homogeneous coefficients
   gives expressions 1 = sum a_(-m) b_m. Use the affine tensor-product description
   (lem-weil-pbc-fibre-product-affine-spectra).
3. The strong-grading torsor algebra theorem gives Spec B, a faithfully flat finitely
   presented quotient map, and the torsor identity. After an fppf-local lift every
   quotient section comes from H; two lifts differ uniquely by N. Representable fpqc
   descent, fppf-to-fpqc comparison and covering base change identify the orbit
   presheaf's sheafification, after any base change (Stacks 03C5).
4. The local representatives of this sheaf give descent data by Yoneda. Apply the
   fppf-sheaf representability/descent-data lemma, the affine-family effectivity
   reduction, and effective affine fpqc descent. Affine permanence and fpqc descent
   of affineness give an affine global representative and glue the quotient maps.
5. Use fpqc descent of flatness and local finite presentation. Surjectivity descends
   through the covering, and affineness supplies quasi-compactness and
   quasi-separatedness. The local torsor inverses glue by representable descent.
6. Normality makes products of local lifts independent of the choices, since
   (h n_1)(k n_2) = hk (k^(-1) n_1 k) n_2. Identity and inverse descend too.
   Yoneda gives the group diagrams. Local membership in N glues uniquely, proving
   the scheme-theoretic kernel square (representable fpqc descent).
7. Smooth flat-surjective source descent makes the quotient smooth; affineness
   makes it finitely presented. Each geometric fibre is the surjective image of
   a connected nonempty fibre, hence connected (Stacks 05B5).
8. An arbitrary base change retains the fppf cover and the same torsor formulas.
   The local-lift argument again identifies the sheafification. Group operations
   and the kernel square pull back. Smooth ring-map base change, affine permanence
   and qcqs permanence retain all remaining properties. No reductivity of H or
   smoothness of N is used. -/
theorem relative_affine_multiplicative_quotient
    {S : Scheme.{u}} (N H : Grp (Over S)) (i : N ⟶ H)
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom]
    [QuasiSeparated H.X.hom] [GeometricallyConnected H.X.hom]
    [IsClosedImmersion i.hom.hom.left]
    (hN : IsRelativeMultiplicativeType N)
    (hnormal : ∀ T : Over S, (IsMonHom.monoidHom i.hom.hom T).range.Normal) :
    ∃ (J : Grp (Over S)) (q : H ⟶ J),
      Smooth J.X.hom ∧ IsAffineHom J.X.hom ∧
      LocallyOfFinitePresentation J.X.hom ∧ QuasiCompact J.X.hom ∧
      QuasiSeparated J.X.hom ∧ GeometricallyConnected J.X.hom ∧
      Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
      LocallyOfFinitePresentation q.hom.hom.left ∧ QuasiCompact q.hom.hom.left ∧
      QuasiSeparated q.hom.hom.left ∧ IsFppfGroupQuotient i q ∧
      ∀ (S' : Scheme.{u}) (f : S' ⟶ S),
        Smooth ((Over.pullback f).mapGrp.obj J).X.hom ∧
        IsAffineHom ((Over.pullback f).mapGrp.obj J).X.hom ∧
        LocallyOfFinitePresentation ((Over.pullback f).mapGrp.obj J).X.hom ∧
        QuasiCompact ((Over.pullback f).mapGrp.obj J).X.hom ∧
        QuasiSeparated ((Over.pullback f).mapGrp.obj J).X.hom ∧
        GeometricallyConnected ((Over.pullback f).mapGrp.obj J).X.hom ∧
        Flat ((Over.pullback f).mapGrp.map q).hom.hom.left ∧
        Surjective ((Over.pullback f).mapGrp.map q).hom.hom.left ∧
        LocallyOfFinitePresentation ((Over.pullback f).mapGrp.map q).hom.hom.left ∧
        QuasiCompact ((Over.pullback f).mapGrp.map q).hom.hom.left ∧
        QuasiSeparated ((Over.pullback f).mapGrp.map q).hom.hom.left ∧
        IsFppfGroupQuotient ((Over.pullback f).mapGrp.map i)
          ((Over.pullback f).mapGrp.map q) := by
  sorry

end AlgebraicGeometry
