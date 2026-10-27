module

public import WeilConjectures.AlgebraicGeometry.DensePoints
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso
import Sheaf.LinearAlgebra.CommonLinearKernelFieldExtension
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Density of a specified family of rational points after field extension

Source: EGA IV₃, Corollaire (11.10.7), printed p. 172, applied to the family
`Spec k → X` indexed by the specified subset of rational points
(blueprint: lem-sfb-rational-density-field-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A specified dense set of `k`-rational points remains dense after every field extension.
No finite type, reducedness, irreducibility, separatedness or separability is assumed.
The empty scheme and the empty set of rational points are allowed.

Source: EGA IV₃, Corollaire (11.10.7), printed p. 172; compare BLR, §5.3,
proof of Lemma 6, printed pp. 125–126
(blueprint: lem-sfb-rational-density-field-extension).

Proof plan:
1. On an affine open `U = Spec A`, take the members `E` of `D` whose images lie in `U`.
   They are dense in `U` and give `k`-algebra evaluations `u_d : A → k`.
   By lem-weil-pbc-affine-chart-base-change-iso, the inverse image of `U` in `X_L`
   is `Spec (L ⊗[k] A)`, or equivalently `Spec (A ⊗[k] L)` after interchanging factors.
   By lem-weil-pbc-algebra-tensor-pushout-universal-property, the induced point evaluates
   `a ⊗ λ` as `u_d(a)λ`; its prime ideal is the kernel of that evaluation.
2. The common kernel `K` of the `u_d` is the nilradical of `A`.
   Indeed, if `a` vanishes at all members of `E`, the basic open `D(a)` misses this dense
   family, hence is empty (lem-weil-pbc-basic-open-function). Thus `a` belongs to every
   prime and is nilpotent (lem-weil-pbc-zero-locus-eq-iff-radical-eq). Conversely a
   nilpotent maps to zero in each field `k`. This does not require `A` to be reduced.
3. By lem-sfb-common-linear-kernel-field-extension, a function vanishing at all the
   induced points is a finite sum `∑ a_i ⊗ λ_i` with `a_i ∈ K`. That lemma allows
   arbitrary vector spaces, index sets and field extensions, including empty families.
4. Each term is nilpotent by the multiplication formula of
   lem-weil-pbc-algebra-tensor-pushout-universal-property. If `a_i ^ n_i = 0`, choose
   `N = 1 + ∑ (n_i - 1)`. In every monomial of the expansion of the `N`th power of
   the finite sum, some term occurs at least `n_i` times, so the monomial is zero.
   An empty sum is zero, with exponent one. Hence the vanishing function is nilpotent.
5. A closed subset `V(J)` of this affine chart containing all the induced points has
   every element of `J` nilpotent, so `J` lies in every prime and `V(J)` is the whole
   chart (def-weil-affine-spectrum). Thus the induced points are dense on each chart.
   These inverse-image charts cover `X_L`; any nonempty open meets one and therefore
   contains an induced point from `D`. If `D` is empty, its density already forces
   `X` empty; zero rings and empty charts are permitted throughout. -/
theorem Hom.denseRange_baseChangeFieldPoint_of_dense
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (D : Set (f.fieldPoints k))
    (hD : DenseRange (fun d : D ↦ d.1.1.base default))
    (L : Type u) [Field L] [Algebra k L] :
    DenseRange (fun d : D ↦ (f.baseChangeFieldPoint L d.1).1.base default) := by
  sorry

end AlgebraicGeometry.Scheme
