module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Splitting an integral monoid over a finite free sharpening group

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VI, 3.7(a), printed p. 75,
and Exposé VIII, 3.1.1--3.1.2, printed p. 98; the DAG's algebraic generalization allowing
arbitrary torsion units (blueprint: lem-trf-integral-monoid-free-sharpening-splitting).

We use multiplicative notation: `Associates R` is `B = R/U`, `Rˣ` is the unit group,
`GrothendieckGroup` is group completion, and the direct sum is the Cartesian product.
The canonical group map is written using `GrothendieckGroup.lift`, not chosen as data.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra

/-- An integral commutative monoid splits as its sharpening times its units when the
sharpening's group completion admits a finite integer basis. No finite generation or
saturation of the original monoid and no torsion-freeness of its units are required.
The kernel clause identifies the kernel with the embedded unit group. The two equations
for `e.symm` specify the inverse's quotient coordinate and its unit coordinate in the
ambient group, where the latter is computed by division (additively, subtraction).

Source: ILO, Exposé VI, 3.7(a), exact sequence (3.a) and its splitting, printed p. 75;
Exposé VIII, 3.1.1--3.1.2, printed p. 98; agent algebraic generalization
(blueprint: lem-trf-integral-monoid-free-sharpening-splitting).

Proof:
1. Apply lem-trf-integral-sharpening-group-exactness. The unit group embeds in the
   completion `G`. Two elements have equal sharpening classes exactly when they differ
   by a unit, so `B` embeds in `G/U`. Its canonical group-completion map is therefore
   injective. The induced group map `G → B^gp` is surjective and has kernel `U`.
2. Apply lem-trf-group-section-monoid-product to the surjective quotient `R → B`.
   Both monoids are integral by the hypothesis and step 1. Lift each vector of a finite
   integer basis of `B^gp` to `G` and extend by integer linear combinations. This gives
   a group section `t`, including in rank zero. Given `b ∈ B`, choose a representative
   `r ∈ R`. The difference `t(b)-r` belongs to `U`, so `t(b)` belongs to `R`. Restrict
   `t` to obtain `j : B → R` with `qj = id`.
3. The product map is `(b,u) ↦ j(b)+u`; its inverse is
   `r ↦ (q(r), r-j(q(r)))`. The kernel calculation puts the second coordinate in `U`.
   Direct substitution checks both inverse identities and additivity. These are
   exactly the maps from lem-trf-group-section-monoid-product. Neither cited lemma
   assumes finite generation, saturation, or torsion-freeness of `G` or `U`. -/
theorem integral_monoid_free_sharpening_splitting
    (R : Type u) [CommMonoid R]
    (hR : Function.Injective (GrothendieckGroup.of (M := R)))
    (hfree : ∃ n : ℕ,
      Nonempty (Module.Basis (Fin n) ℤ (Additive (GrothendieckGroup (Associates R))))) :
    Function.Injective (GrothendieckGroup.of (M := Associates R)) ∧
      Function.Surjective
        (GrothendieckGroup.lift (GrothendieckGroup.of.comp
          (Associates.mkMonoidHom : R →* Associates R))) ∧
      (∀ g : GrothendieckGroup R,
        GrothendieckGroup.lift (GrothendieckGroup.of.comp
          (Associates.mkMonoidHom : R →* Associates R)) g = 1 ↔
            ∃ u : Rˣ, GrothendieckGroup.of (u : R) = g) ∧
      ∃ t : GrothendieckGroup (Associates R) →* GrothendieckGroup R,
        (GrothendieckGroup.lift (GrothendieckGroup.of.comp
          (Associates.mkMonoidHom : R →* Associates R))).comp t =
            MonoidHom.id (GrothendieckGroup (Associates R)) ∧
        (∀ b : Associates R, ∃ r : R,
          GrothendieckGroup.of r = t (GrothendieckGroup.of b)) ∧
        ∃ j : Associates R →* R,
          (∀ b : Associates R,
            GrothendieckGroup.of (j b) = t (GrothendieckGroup.of b)) ∧
          (Associates.mkMonoidHom.comp j = MonoidHom.id (Associates R)) ∧
          ∃ e : (Associates R × Rˣ) ≃* R,
            (∀ (b : Associates R) (u : Rˣ), e (b, u) = j b * (u : R)) ∧
            (∀ r : R,
              (e.symm r).1 = Associates.mk r ∧
              GrothendieckGroup.of ((e.symm r).2 : R) =
                GrothendieckGroup.of r / GrothendieckGroup.of (j (Associates.mk r))) := by
  sorry

end Algebra
