module

public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme

@[expose] public section

/-!
# Nonzero relative differential gives a smooth hypersurface point

Source: Stacks Project, Algebra, Tag 00T7.
(blueprint: lem-zl-hypersurface-nonzero-relative-differential).
-/

open CategoryTheory Limits Opposite TopologicalSpace PresheafOfModules
open AlgebraicGeometry
open scoped AlgebraicGeometry Scheme.Modules

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/-- The value at `z` of the relative differential of a local equation `a`, rendered as
`d a (z) ⊗ 1` in `Ω¹_{X/S,z} ⊗_{𝒪_{X,z}} κ(z)` is nonzero.

Source: Stacks Project, Morphisms, Tag 01UM (universal relative derivation), and
Algebra, Tag 00T7 (the differential basis on a standard smooth chart).
(blueprint: lem-zl-hypersurface-nonzero-relative-differential). -/
noncomputable def relativeDifferentialValue {X S : Scheme.{u}} (p : X ⟶ S)
    (U : X.Opens) (z : X) (hz : z ∈ U) (a : Γ(X, U)) : Prop := by
  letI : Module (X.presheaf.stalk z) (X.residueField z) :=
    Module.compHom (X.residueField z) (X.residue z).hom
  let v := TensorProduct.tmul (X.presheaf.stalk z)
    (TopCat.Presheaf.germ (p.relativeDifferentials.val.presheaf) U z hz
      ((p.relativeDifferentialsDerivation.app (op U)).toFun a)) (1 : X.residueField z)
  exact v ≠ 0

/-- **Nonzero relative differential gives a smooth hypersurface point.**

Source: Stacks Project, Algebra, Tag 00T7, applied to a standard smooth chart after adjoining
one equation with a nonzero Jacobian row.
(blueprint: lem-zl-hypersurface-nonzero-relative-differential).
Proof, following the six steps of the node:

1. Restrict the smooth ambient morphism to the trivializing open by
   `lem-pc-open-immersion-smooth-composition`. By
   `lem-weil-pbc-smooth-locally-standard-smooth`, choose a standard smooth affine chart
   `A = R[x₁,...,xₙ]/(g₁,...,g꜀)` inside it. By `lem-pc-zero-scheme-properties`,
   the zero scheme there is `Spec B`, where `B = A/(a)`. The prime of the point contains `a`.
   The first `c` columns of the Jacobian form an invertible square matrix `J`, by
   `def-weil-pbc-standard-smooth-algebra`.
2. By `def-sc-relative-differential-sheaf`,
   `lem-weil-pbc-spec-tilde-stalk-localization`, and
   `lem-weil-pbc-affine-open-stalk-localization`, the residue differential is `da ⊗ 1`
   in the affine differential module tensored with the residue field. By
   `lem-weil-pbc-standard-smooth-kahler-basis`, the differentials of the last `n-c`
   coordinates form a basis. Nonvanishing gives a coefficient `bⱼ` outside the prime,
   with `j > c`; in particular `n > c`.
3. Lift `a` to a polynomial `h`. The polynomial derivation rules of
   `def-weil-pbc-kahler-differentials` give `dG = Σᵢ ∂ᵢG dxᵢ`. Eliminating the first
   `c` differentials using `J` yields `bᵢ = ∂ᵢh - u J⁻¹ kᵢ`, where `u` is the first
   `c` partials of `h` and `kᵢ` is the column of partials of the `g` equations.
4. Adjoin the row of partials of `h` and column `j`. Subtract `u J⁻¹` times the
   first rows from the last row: the enlarged determinant is `det(J) bⱼ`. Its image
   `δ` in `B` is outside the point's prime, so its principal open contains the point.
   This includes `c = 0`, with empty determinant one.
5. By `def-weil-ring-localization-away`, `C = B[1/δ]` has presentation
   `R[x₁,...,xₙ,t]/(g₁,...,g꜀,h,tΔ-1)`. The two presentation maps fix all generators.
   The minor in columns `1,...,c,j,t` has determinant `Δ²`, a unit in `C`, so this
   presentation is standard smooth. The required inequality follows from `n > c`.
6. Apply `lem-weil-pbc-standard-smooth-is-smooth` and
   `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`. By
   `lem-weil-pbc-principal-localization-open-immersion`, `Spec C` is an open
   neighbourhood in the zero scheme. Its map to the original base is smooth:
   the same affine target chart checks local finite presentation, and every affine
   first-order thickening over the base factors through that target open whenever
   its reduction does. The formal lift over the chart is thus a lift over the base,
   as in `def-sbc-smooth-morphisms`. No flatness of the zero scheme is assumed.
-/
theorem smooth_zeroLocus_of_relativeDifferentialValue
    {X S : Scheme.{u}} (p : X ⟶ S) [Smooth p] (M : X.Modules) [M.IsInvertible]
    (s : M.sections)
    (z : (Scheme.Modules.Hom.zeroLocus (M.unitHomEquiv.symm s)).subscheme)
    (U : X.Opens) (hz : (Scheme.Modules.Hom.zeroLocus
      (M.unitHomEquiv.symm s)).subschemeι z ∈ U)
    (e : Γ(M, U)) (he : Scheme.Modules.IsFreeGenerator e) (a : Γ(X, U))
    (ha : ((M.unitHomEquiv.symm s).val.app (op U)) (1 : Γ(X, U)) = a • e)
    (hda : relativeDifferentialValue p U
      ((Scheme.Modules.Hom.zeroLocus (M.unitHomEquiv.symm s)).subschemeι z) hz a) :
    ∃ V : (Scheme.Modules.Hom.zeroLocus (M.unitHomEquiv.symm s)).subscheme.Opens,
      z ∈ V ∧ Smooth (V.ι ≫
        (Scheme.Modules.Hom.zeroLocus (M.unitHomEquiv.symm s)).subschemeι ≫ p) := by
  sorry

end Scheme.Hom
end AlgebraicGeometry
