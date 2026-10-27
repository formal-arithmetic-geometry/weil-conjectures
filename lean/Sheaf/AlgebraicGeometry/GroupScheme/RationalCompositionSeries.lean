module

public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
public import Mathlib.LinearAlgebra.Quotient.Defs

/-! # Composition series of rational group-scheme modules

Source: Milne, Algebraic Groups (2017), Sections 4a--4b; the finite rational-submodule
filtrations used in Jantzen, Representations of Algebraic Groups, II.2 and II.6.
(blueprint: def-sfb-rational-composition-series)

The factors are actual subspace quotients. The inclusion and quotient squares uniquely
specify the restricted and descended coactions; no arbitrary factor representation is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.RationalHighestWeight

variable {F : Type u} [Field F]
variable {G : Grp (Over (Spec (.of F)))} [IsAffine G.X.left]
variable {V : Type v} [AddCommGroup V] [Module F V]

/-- The actual successive quotient N_(i+1)/(N_i intersect N_(i+1)). In a strictly
increasing filtration the intersection is precisely N_i, viewed inside N_(i+1).
Source: Milne, Sections 4a--4b; Jantzen, II.2
(blueprint: def-sfb-rational-composition-series). -/
abbrev FiltrationFactor {n : ℕ} (N : Fin (n + 1) → Submodule F V) (i : Fin n) :=
  (N i.succ) ⧸ (N i.castSucc).comap (N i.succ).subtype

/-- A finite strictly increasing rational filtration from zero to V, with nonzero
simple canonical successive quotients. Restriction and descent are pinned by their
canonical inclusion and quotient maps. All coactions satisfy both rationality identities.
Source: Milne, Sections 4a--4b; Jantzen, II.2 and II.6
(blueprint: def-sfb-rational-composition-series). -/
structure RationalCompositionSeries (c : V →ₗ[F] V ⊗[F] coordinateAlgebra G) where
  /-- Number of simple factors; zero is allowed for the zero module. -/
  length : ℕ
  /-- The actual rational subspaces of V. -/
  space : Fin (length + 1) → Submodule F V
  /-- No repeated filtration steps. -/
  strictMono : StrictMono space
  /-- The first subspace is zero. -/
  head : space 0 = ⊥
  /-- The last subspace is V. -/
  last : space (Fin.last length) = ⊤
  /-- The restricted coaction on each subspace. -/
  restriction (i : Fin (length + 1)) :
    space i →ₗ[F] space i ⊗[F] coordinateAlgebra G
  /-- The inclusion is equivariant, uniquely specifying restriction. -/
  restriction_eq (i : Fin (length + 1)) :
    (space i).subtype.rTensor (coordinateAlgebra G) ∘ₗ restriction i =
      c ∘ₗ (space i).subtype
  /-- Restriction is coassociative. -/
  restriction_coassoc (i : Fin (length + 1)) :
    HopfAction.Coassociative F (coordinateAlgebra G) (space i) (restriction i)
  /-- Restriction is counital. -/
  restriction_counit (i : Fin (length + 1)) :
    HopfAction.Counital F (coordinateAlgebra G) (space i) (restriction i)
  /-- The descended coaction on the actual successive quotient. -/
  factorCoaction (i : Fin length) :
    FiltrationFactor space i →ₗ[F] FiltrationFactor space i ⊗[F] coordinateAlgebra G
  /-- The quotient projection is equivariant, uniquely specifying descent. -/
  factor_eq (i : Fin length) :
    ((space i.castSucc).comap (space i.succ).subtype).mkQ.rTensor (coordinateAlgebra G) ∘ₗ
        restriction i.succ =
      factorCoaction i ∘ₗ ((space i.castSucc).comap (space i.succ).subtype).mkQ
  /-- The quotient coaction is coassociative. -/
  factor_coassoc (i : Fin length) :
    HopfAction.Coassociative F (coordinateAlgebra G)
      (FiltrationFactor space i) (factorCoaction i)
  /-- The quotient coaction is counital. -/
  factor_counit (i : Fin length) :
    HopfAction.Counital F (coordinateAlgebra G)
      (FiltrationFactor space i) (factorCoaction i)
  /-- Every quotient is nonzero and has no proper nonzero rational subspace. -/
  factor_simple (i : Fin length) : IsSimple (factorCoaction i)

end AlgebraicGeometry.RationalHighestWeight
