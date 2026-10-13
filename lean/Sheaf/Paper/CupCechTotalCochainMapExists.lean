module
public import Sheaf.Paper.CupCechPairCochain
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct
noncomputable section
/-- The total Alexander--Whitney map with its formula on every tensor of row summands.
Source: Stacks Project, Remark 20.25.3, equation 07MB.
(blueprint: new-cup-cech-total-cochain-map)

Proof: restrict the front i-face and the back j-face to their common intersection
and apply D.pair r s. Local bilinearity and scalar restriction make this formula
bilinear over the ring of global sections. Multiply by (-1)^(i*s). Extend by the
tensor universal property, and by the coproduct universal property over the
finite diagonals, to define each total-degree component. D.leibniz verifies the
resolution part of the cochain identity: shifting r contributes no extra sign,
while shifting s changes the Koszul factor by (-1)^i. In the Cech part, expand
the omitted-vertex sums. The terms before the common vertex come from the first
input, those after it from the second, and the two terms at the common vertex
cancel. D.restriction identifies composite restrictions. With the total
convention d_res + (-1)^r d_Cech, both parts give the differential of the tensor
complex. Pure tensors in the diagonal summands generate the source, so this
proves the cochain identity everywhere. The defining component formula yields
the displayed equality. For an empty index type all row terms are zero; for
zero degrees the same formula uses singleton tuples and sign one. -/
theorem exists_cupCech_total_cochain_map {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G) :
    let A := (cupCechDouble U D.left.K).total (ComplexShape.up ℕ)
    let B := (cupCechDouble U D.right.K).total (ComplexShape.up ℕ)
    let C := (cupCechDouble U D.target.K).total (ComplexShape.up ℕ)
    ∃ h : HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{u} Γ(X, ⊤)))
        (ComplexShape.up ℕ) ⟶ C,
      ∀ (r s i j m n : ℕ) (hm : r + i = m) (hn : s + j = n)
        (a : ((cupCechDouble U D.left.K).X r).X i)
        (b : ((cupCechDouble U D.right.K).X s).X j),
        h.f (m + n)
          (HomologicalComplex.ιMapBifunctor A B
            (curriedTensor (ModuleCat.{u} Γ(X, ⊤))) (ComplexShape.up ℕ)
            m n (m + n) rfl
            (((cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ)
                r i m (by simpa using hm) a) ⊗ₜ[Γ(X, ⊤)]
              ((cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ)
                s j n (by simpa using hn) b))) =
          (-1 : ℤ) ^ (i * s) •
            (cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ)
              (r + s) (i + j) (m + n) (by dsimp; omega)
              (cupCechPairCochain U D r s i j a b) := by sorry
end
end AlgebraicGeometry.Scheme.Modules
