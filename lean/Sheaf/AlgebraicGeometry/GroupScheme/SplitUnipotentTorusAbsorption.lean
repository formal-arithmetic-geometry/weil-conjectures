module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentSeries
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Absorbing a split torus into a torus complement

Source: Milne, Algebraic Groups (2017), Proposition 16.54, p.344,
and Summary 16.29(d), p.334 (blueprint: lem-sfb-split-unipotent-torus-absorption).

The semidirect product is specified by its product-scheme coordinates and its exact
multiplication law. The conclusion is an identity of scheme morphisms, so it gives
containment over every algebra, including nonreduced algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A closed split torus of U semidirect D is conjugate into D by a point of U(k).
The action identities and the multiplication formula specify the semidirect product
in any product-scheme presentation e; they do not assume conjugacy or a splitting theorem.
Smooth connected group schemes over a field are geometrically connected: apply the
rational-identity-point criterion. Thus the connected terms in SplitUnipotentLength
are precisely the geometrically connected terms required in the split series.

Source: Milne, Algebraic Groups (2017), Proposition 16.54, p.344,
Summary 16.29(d), p.334, Theorem 16.27(a), p.333, and Proposition 15.3, pp.305--306
(blueprint: lem-sfb-split-unipotent-torus-absorption).

Proof plan:
1. In the coordinates e, write the inclusion as t ↦ (c(t),a(t)). Its homomorphism
   identity gives c(tt') = c(t)(a(t) · c(t')). Projection a is a homomorphism.
2. Apply lem-sfb-split-unipotent-torus-stable-series for the induced T-action on U.
   Obtain stable terms V_i and additive quotients q_i with monomial characters chi_i.
   The tail at V_{i+1} is itself a split additive series.
3. A crossed homomorphism f from a split torus to G_a of weight n is a Laurent
   polynomial. Comparing coefficients of Y^a in f(XY)=f(X)+X^n f(Y) shows that
   only exponents 0 and n occur. Since f(1)=0, f=b(1-X^n). For n=0 take b=0.
4. The fibre of q_i above b is a V_{i+1}-torsor by
   lem-sfb-affine-normal-quotient-geometry. Its fppf and finite-presentation
   properties survive base change by lem-trf-fppf-covering-base-change and
   lem-weil-pbc-qcqs-morphism-permanence. Apply
   lem-sfb-split-unipotent-affine-torsor-section over Spec k to lift b to v in V_i(k).
5. Inductively remove the component q_i(c_i)=b-chi_i*b by conjugation:
   c_{i+1}(t)=v⁻¹*c_i(t)*(a(t)·v). Its q_i-image is zero, so it factors through
   V_{i+1} scheme-theoretically. The accumulated conjugation is by w_i⁻¹.
6. At the final trivial term the U-coordinate is 1. Take u=w_m⁻¹ and let v be
   the resulting homomorphism T → D. The morphism equality below is the asserted
   inclusion on every algebra. The zero-length series and rank-zero tori are included.
-/
theorem split_unipotent_torus_absorption
    {k : Type u} [Field k] (U D H T : Grp (Over (Spec (.of k))))
    (_hU : SolvableGroupStructure.IsAlgebraic U)
    (_hunip : SolvableGroupStructure.IsUnipotent U)
    (_hgeo : GeometricallyConnected U.X.hom)
    (_hsplit : ∃ m : ℕ, SplitUnipotentLength U m)
    (_hD : ∃ r : ℕ, Nonempty (D ≅ MultiplicativeType.splitTorus k r))
    (act : D.X ⊗ U.X ⟶ U.X)
    (_hunit : ∀ (X : Over (Spec (.of k))) (x : X ⟶ U.X), lift 1 x ≫ act = x)
    (_haction : ∀ (X : Over (Spec (.of k))) (d e : X ⟶ D.X) (x : X ⟶ U.X),
      lift (d * e) x ≫ act = lift d (lift e x ≫ act) ≫ act)
    (_haut : ∀ (X : Over (Spec (.of k))) (d : X ⟶ D.X) (x y : X ⟶ U.X),
      lift d (x * y) ≫ act = (lift d x ≫ act) * (lift d y ≫ act))
    (e : H.X ≅ U.X ⊗ D.X)
    (_hmul : ∀ (X : Over (Spec (.of k))) (x y : X ⟶ H.X),
      (x * y) ≫ e.hom =
        lift ((x ≫ e.hom ≫ fst U.X D.X) *
          (lift (x ≫ e.hom ≫ snd U.X D.X) (y ≫ e.hom ≫ fst U.X D.X) ≫ act))
          ((x ≫ e.hom ≫ snd U.X D.X) * (y ≫ e.hom ≫ snd U.X D.X)))
    (i : T ⟶ H) [IsClosedSubgroupScheme i.hom.hom]
    (_hT : ∃ s : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k s)) :
    ∃ (u : 𝟙_ (Over (Spec (.of k))) ⟶ U.X) (v : T ⟶ D),
      (toUnit T.X ≫ lift u 1 ≫ e.inv) * i.hom.hom *
        (toUnit T.X ≫ lift u 1 ≫ e.inv)⁻¹ = lift 1 v.hom.hom ≫ e.inv := by
  sorry

end AlgebraicGeometry
