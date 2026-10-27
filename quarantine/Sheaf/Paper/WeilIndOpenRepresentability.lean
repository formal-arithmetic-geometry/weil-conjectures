/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q9
-/
module

public import Sheaf.Paper.WeilIndSheafCategory

/-! # Open extension on represented ind-sheaves

Source: SGA 4, XVII, §5; Bhatt--Scholze, §6.7--6.8.
(blueprint: lem-zl-ind-open-representability).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Exact open extension preserves represented constructible Weil sheaves.
Source: SGA 4, XVII, 5.1 (extension by zero); Bhatt--Scholze, 6.7.6--6.8.11
(blueprint: lem-zl-ind-open-representability).

Proof: on the underlying constructible heart, extension by zero along the geometric
base change of j₀ is exact and preserves constructibility. The schemes are finite type
over a field and hence Noetherian; in particular the open immersion is quasi-compact.
At each finite coefficient field use the integral extension-by-zero functor, rationalize,
and pass to common stages using its normalized coefficient comparisons. Its left-adjoint
Hom bijection with inverse image restricts to the hearts. Transport through AsSmall and
extend by filtered colimits. The Yoneda Kan unit identifies this extension on represented
objects with the original extension by zero. Its Frobenius comparison is the left mate
of the prescribed inverse-image square, so this identification is equivariant.
The lifted adjunction on fixed pairs identifies this functor with the chosen ambient
left adjoint zlIndWeilOpenShriek by uniqueness of left adjoints. Apply that comparison
to the represented F. This includes the empty open, identity open and zero sheaf. -/
theorem zlIndWeilOpenShriek_representable {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left]
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    ∃ G : sfCommonStageWeilSheaf D l hl Y₀ Ω,
      Nonempty ((zlWeilIndEmbedding D l hl Ω Y₀).obj G ≅
        (zlIndWeilOpenShriek D l hl Ω j₀).obj
          ((zlWeilIndEmbedding D l hl Ω X₀).obj F)) := by
  sorry

end WeilConjectures
