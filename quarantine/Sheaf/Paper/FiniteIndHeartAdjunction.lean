/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.WeilIndSheafCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.Paper.ZlFiniteAdicDirectImage
import Sheaf.Paper.DlConstructibleFibresExact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # The exact ind adjunction for finite ordinary direct image

Source: Stacks 09A8; Bhatt--Scholze 6.8.14--6.8.15;
blueprint main-20261015, lem-zl-quasi-finite.proof.md, clause (1).
(blueprint: lem-zl-finite-ind-heart-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- Finite ordinary direct image is an exact right adjoint on ind-objects of the
underlying constructible hearts, before a Weil structure is introduced.

Source: Stacks 09A8; Bhatt--Scholze 6.8.14--6.8.15; blueprint main-20261015,
`lem-zl-quasi-finite.proof.md`, clause (1), exact finite ordinary direct image.
(blueprint: lem-zl-finite-ind-heart-adjunction).

Proof: on an affine target chart the finite source is affine. The finite-adic
direct-image theorem supplies an exact heart functor and its normalized
inverse-image adjunction at finite coefficient stages. Its scalar comparison
is the mate of the inverse-image comparison, so these adjunctions descend to
common stages. Restrict the t-exact adjunction to the hearts, then transport it
through AsSmall. Thus heart direct image is an exact right adjoint to the
specified small-heart pullback, with the original counit.

Extend this adjunction to ind-objects. For a representable A and a filtered
presentation B=colim B_j, compactness of representables and the heart adjunction
give Hom(L A,B)=colim Hom(L A,B_j)=colim Hom(A,R B_j).
For a filtered presentation of A, take the limit of these Hom bijections.
Their naturality gives the ind adjunction. Simultaneous filtered presentations
of finite diagrams and exactness of filtered colimits show that the ind image
preserves finite colimits; its finite-limit preservation follows from being a
right adjoint. Comparisons on chart intersections respect units and counits
and agree by uniqueness of adjoints. The conservative restriction functors and
the open-cover exactness criterion therefore glue the adjunction and detect
its global exactness, without absolute separatedness. This statement concerns
ordinary underlying heart objects only; it assumes no Frobenius or Weil pair.
The empty source, identity maps and nonreduced finite fibres are included. -/
theorem sfFiniteIndHeartAdjunction
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsFinite f₀.left] :
    ∃ R : Ind (zlSmallHeart D l Ω hl X₀) ⥤ Ind (zlSmallHeart D l Ω hl Y₀),
      Nonempty (zlIndMap (zlSmallPull D l hl Ω f₀) ⊣ R) ∧
        PreservesFiniteColimits R := by
  sorry

end WeilConjectures
