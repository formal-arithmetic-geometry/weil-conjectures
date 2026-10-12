/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Etale.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Generic algebra of a finite etale open cover

Source: Stacks Project, Tags 02GL and 081I.
(blueprint: lem-sbc-finite-etale-open-generic-algebra)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Sections of a finite etale open cover embed into a finite etale generic algebra.

Source: Stacks Project, Tag 02GL (lemma-etale-over-field), and Tag 081I
(flat base change of scheme-theoretic images).
(blueprint: lem-sbc-finite-etale-open-generic-algebra)

Proof: Put A = Gamma(X,V) and K = Frac(A). If U is empty, its finite cover and
section ring are empty and zero respectively; use the zero K-algebra. Otherwise U
contains the generic point of X, and the fraction field of A identifies with the
stalk there. Let alpha: Spec K -> U be this generic map and let D be the sections
of the pullback of P along alpha. Finite and etale morphisms are preserved by base
change; a finite scheme over Spec K is affine. Thus D is finite etale over K.
The map alpha is quasi-compact because Spec K has one point (every inverse image
of an open is empty or the full compact space). Its image is the generic point,
so it is dominant, and since U is reduced it is scheme-theoretically dominant.
The finite etale map P -> U is flat. By 081I its base change makes the projection
from the generic fibre to P quasi-compact and scheme-theoretically dominant.
Its section map on the inverse image of V is therefore injective. That open
pulls back to the full generic fibre, since V contains the generic point of X.
Identify its sections with D to obtain e. The pullback square and the affine
chart identification of the generic stalk with Frac(A) show e commutes with A.
This constructs the generic algebra, rather than presupposing finiteness of any
integral closure. Empty covers and the zero generic algebra are included. -/
theorem exists_finiteEtale_open_generic_algebra {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) (P : U.toScheme.FiniteEtale) (V : X.Opens) [Nonempty V]
    (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, V) Γ(P.obj.left, (P.obj.hom ≫ U.ι) ⁻¹ᵁ V) :=
      ((P.obj.hom ≫ U.ι).app V).hom.toAlgebra
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra (FractionRing Γ(X, V)) D),
      Module.Finite (FractionRing Γ(X, V)) D ∧
      Algebra.FormallyEtale (FractionRing Γ(X, V)) D ∧
      letI : Algebra Γ(X, V) D :=
        Algebra.compHom D (algebraMap Γ(X, V) (FractionRing Γ(X, V)))
      ∃ e : Γ(P.obj.left, (P.obj.hom ≫ U.ι) ⁻¹ᵁ V) →ₐ[Γ(X, V)] D,
        Function.Injective e := by sorry

end AlgebraicGeometry.Scheme
