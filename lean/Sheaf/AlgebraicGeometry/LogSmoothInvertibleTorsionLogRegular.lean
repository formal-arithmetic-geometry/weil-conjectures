/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Torsion

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.FiniteType
import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks
import Sheaf.AlgebraicGeometry.LogSmoothLogRegular

/-!
# Log regularity under log smoothness with invertible chart torsion

Source: Illusie--Laszlo--Orgogozo, Exposé VI 1.8, p.70, and Exposé XVI 3.6.3, p.252
(blueprint: lem-per-log-smooth-invertible-torsion-log-regular).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The compatible fs charts occurring in the chart criterion of log smoothness.
The group map is injective, and the torsion subgroup of its actual quotient cokernel
is finite with order invertible on the source neighbourhood. The maps `y` and `x`
are fixed by the chart monomials; the two projection equations fix the comparison
uniquely. No torsion-freeness or sharpness is imposed on either chart or cokernel.
Source: ILO XVI 3.6.3, p.252, and the chart interpretation of VI 1.8, p.70
(blueprint: lem-per-log-smooth-invertible-torsion-log-regular). -/
structure InvertibleTorsionFSLogChart (X Y : FineSaturatedLogScheme.{u})
    (f : EtaleLogHom X Y) where
  W : Y.scheme.Etale
  V : X.scheme.Etale
  P : Type u
  Q : Type u
  instP : CommMonoid P
  instQ : CommMonoid Q
  fineP : @IsFineSaturatedMonoid P instP
  fineQ : @IsFineSaturatedMonoid Q instQ
  chartY : P →* Y.logStructure.monoidSheaf.obj.obj (op W)
  chartX : Q →* X.logStructure.monoidSheaf.obj.obj (op V)
  g : P →* Q
  chartY_isChart : Y.logStructure.IsChart W chartY
  chartX_isChart : X.logStructure.IsChart V chartX
  map : V.left ⟶ W.left
  map_over : map ≫ W.hom = V.hom ≫ f.base
  chart_compatibility : ∀ p : P,
    f.sectionMap W V map map_over (chartY p) = chartX (g p)
  y : W.left ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of (MonoidAlgebra ℤ P)))
  x : V.left ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of (MonoidAlgebra ℤ Q)))
  y_chart : ∀ p : P,
    y.appTop ((Scheme.ΓSpecIso
      (CommRingCat.of (MonoidAlgebra ℤ P))).inv (MonoidAlgebra.single p 1)) =
      Y.logStructure.alpha.app (op W) (chartY p)
  x_chart : ∀ q : Q,
    x.appTop ((Scheme.ΓSpecIso
      (CommRingCat.of (MonoidAlgebra ℤ Q))).inv (MonoidAlgebra.single q 1)) =
      X.logStructure.alpha.app (op V) (chartX q)
  comparison : V.left ⟶
    pullback y (Scheme.Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ g)).op)
  comparison_fst : comparison ≫ pullback.fst y
      (Scheme.Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ g)).op) = map
  comparison_snd : comparison ≫ pullback.snd y
      (Scheme.Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ g)).op) = x
  gp_injective :
    Function.Injective
      (Algebra.GrothendieckGroup.lift ((Algebra.GrothendieckGroup.of (M := Q)).comp g))
  torsion_finite : Finite (CommGroup.torsion
    (Algebra.GrothendieckGroup Q ⧸
      (Algebra.GrothendieckGroup.lift
        ((Algebra.GrothendieckGroup.of (M := Q)).comp g)).range))
  torsion_order_invertible : IsUnit
    (Nat.card (CommGroup.torsion
      (Algebra.GrothendieckGroup Q ⧸
        (Algebra.GrothendieckGroup.lift
          ((Algebra.GrothendieckGroup.of (M := Q)).comp g)).range)) : Γ(V.left, ⊤))

/-- A log-smooth morphism with injective chart group maps and finite invertible
cokernel torsion preserves log regularity. Source: ILO VI 1.8, p.70; the chart
interpretation is ILO XVI 3.6.3, p.252
(blueprint: lem-per-log-smooth-invertible-torsion-log-regular).

Proof (the four steps of the DAG node):

1. Fix a geometric source point and compatible étale chart neighbourhoods P → Q.
Let n be the order of the torsion subgroup of the group cokernel. Its invertibility
on the source implies invertibility in the residue field of the image point on the
base. Shrink the base to the open invertibility locus of n and restrict the source.
Log regularity is unchanged at the chosen geometric points under these restrictions
and étale neighbourhoods, since their strict local rings and log stalks agree.

2. Apply lem-per-fs-chart-torsion-factorization. The explicit root saturation
R = {q in Q : some positive power of q lies in the image of P} is fs and factors
P → Q as P → R → Q. The first map is Kummer with injective group map and finite
cokernel of order n, and the second has injective group map and torsion-free
cokernel. This construction also allows torsion in the chart group completions.

3. Form Y_R = Y ×_{Spec Z[P]} Spec Z[R]. On affine charts its coordinate ring is
D ⊗_{Z[P]} Z[R], a quotient of a polynomial ring over D because R is finitely
generated. It is locally Noetherian by lem-weil-pbc-finite-type-algebra-noetherian
and lem-weil-pbc-fibre-product-affine-spectra. Give it the log structure associated
to the canonical R-monomials. The associated-log universal property and stalk
formula of lem-trf-associated-log-universal-stalks make it fs, identify R as its
chart, and give the log morphism Y_R → Y with chart P → R. Its comparison is the
identity, hence étale. The integer n is invertible on the restricted base, so
lem-per-invertible-kummer-chart-log-regular gives log regularity of Y_R.

4. The Q-chart induces X → Y_R, with log map induced by R → Q using the same
associated-log universal property. The comparison target is canonically
(Y ×_{Spec Z[P]} Spec Z[R]) ×_{Spec Z[R]} Spec Z[Q]
≅ Y ×_{Spec Z[P]} Spec Z[Q]: both universal properties specify exactly a map to Y
and a compatible map to Spec Z[Q]. This identifies the new comparison with the
given smooth comparison. The group cokernel of R → Q is torsion-free, so
lem-trf-log-smooth-log-regular applies and gives log regularity at the chosen
source point. The chart neighbourhoods cover all geometric source points, hence
X is log regular. For the empty source the same pointwise assertion is vacuous.
-/
theorem logSmooth_invertibleTorsion_logRegular
    (X Y : FineSaturatedLogScheme.{u}) (f : EtaleLogHom X Y)
    (hY : Y.IsLogRegular)
    (hcharts : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X.scheme),
      ∃ c : InvertibleTorsionFSLogChart X Y f,
        Nonempty ((Scheme.pointSmallEtale t).fiber.obj c.V) ∧ Smooth c.comparison) :
    X.IsLogRegular := by
  sorry

end AlgebraicGeometry
