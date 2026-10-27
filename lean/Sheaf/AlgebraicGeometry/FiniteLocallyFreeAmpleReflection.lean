module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen

/-! # Finite locally free surjections reflect ampleness

Source: Stacks Project, Divisors, Tags 0BD2, 0BCY and the proof of 0BD0,
using clopen constant-rank strata from Morphisms, Tag 04MH
(blueprint: lem-sfb-finite-locally-free-ample-reflection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module is ample if its tensor pullback along a finite locally free
surjection is ample, in the absolute sense.

Source: Stacks Project, Divisors, Tags 0BD2 (finite locally free norm), 0BCY
(norm of a pulled-back line), and the proof of 0BD0 (norm preserves ampleness);
Morphisms, Tag 04MH (clopen constant-rank strata)
(blueprint: lem-sfb-finite-locally-free-ample-reflection).

Proof:
1. Put `M = f^*L`. The definition `def-weil-pbc-ample-invertible-module` makes `Y`
   quasi-compact. Pull back an open cover of `X`, take a finite subcover on `Y`, and
   use surjectivity (`def-weil-surjective-morphism`) to see that `X` is quasi-compact.
   If `X` is empty, the remaining affine-section condition is vacuous.
2. For `x` in `X`, use `lem-weil-pbc-finite-flat-rank-iso` to take the clopen rank
   stratum `U` through `x`, of rank `d`. Surjectivity makes `d` positive: the fibre
   algebra maps unitally to the nonzero residue field of a point over `x`, so its
   dimension cannot be zero. Restricting `f` over `U` preserves finite local freeness
   and gives constant degree `d` (`def-pc-finite-locally-free`). Choose an affine open
   neighbourhood `V` of `x` contained in `U`, using `def-pc-scheme`.
3. The fibre `E` over `x` is finite by `lem-weil-pbc-finite-closed-map-finite-fibres`.
   Apply `lem-sc-ample-finite-principal-affine` to `M` on all of `Y` and the open
   inverse image of `V`: obtain `n > 0` and a global section `s` of `M^{tensor n}`
   with `E` contained in `Y_s` and `Y_s` contained in that inverse image. Restrict
   to the inverse image of `U`; `lem-weil-pbc-invertible-pullback-tensor` identifies
   the restricted line with the pullback of `L|U` and respects tensor sections.
   Apply `lem-sfb-finite-locally-free-pullback-section-norm` to obtain a section
   `t_U` of `(L|U)^{tensor (d*n)}` whose nonvanishing locus consists of points whose
   whole fibre lies in `Y_s`. This locus contains `x` and lies in `V`: lift any point
   of the locus along the surjection and use `Y_s` contained in the inverse image of `V`.
4. Glue `t_U` with zero on the disjoint clopen complement of `U`, using the sheaf
   axiom (`def-weil-sheaf-of-modules-category`). This produces a global section `t`
   of `L^{tensor (d*n)}` with the same nonvanishing locus. That locus is contained
   in `V`, hence affine by `lem-sc-affine-cap-section-open`. Since `d*n > 0`, it
   supplies the positive-power affine-section witness at `x`. Together with step 1,
   these witnesses are exactly `def-weil-pbc-ample-invertible-module` for `L`.
-/
theorem isAmple_of_tensorPullback_finiteLocallyFree_surjective
    {X Y : Scheme.{u}} (f : Y ⟶ X) [f.IsFiniteLocallyFree] [Surjective f]
    (L : X.Modules) [L.IsInvertible]
    (hL : @IsAmple Y ((tensorPullback f).obj L) ((invertible_pullback_tensor f).1 L).2) :
    IsAmple X L := by
  sorry

end AlgebraicGeometry.Scheme.Modules
