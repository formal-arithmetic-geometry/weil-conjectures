/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.GeometricTowerData

/-! # Compactification and finite scalar squares for condensed towers
Source: blueprint sk-prop-sp-tower-geometric, compact support and finite evaluation.
(blueprint: lem-sp-condensed-geometric-support)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Compactification on actual section-ring systems, its uniform constructible bounds,
finite adjunctions, and the scalar square induced by its transitions.
Source: blueprint sk-prop-sp-tower-geometric, opening paragraph; det-sp-tower-shriek-levels
and det-sp-tower-bound-uniform; final reduction paragraph.
Proof: apply extension by zero to the underlying abelian sheaves at every level and
use the pulled-back coefficient action to give it the required scalar module structure.
The proper leg is the corresponding levelwise direct image on section modules. Both
constructions preserve every quotient-semilinear transition, its identity and its
composition, as well as morphisms. Extension by zero is exact; direct image is additive.
Right derive the latter on the ringed sequence site. The normalized derived singleton
extensions and derived evaluation comparisons identify the evaluated proper construction
with the finite proper derived image. Evaluation of the exact open-extension construction
then identifies finite compact support. Scalar extension is derived, not assumed exact.
The finite compactification estimate bounds cohomology and Tor amplitude by
the input intervals enlarged by the common geometric fibre bound. Constructibility is
preserved by the finite proper and open operations. Restrict the resulting functor to
the uniform finite-Tor subcategories. At every level the finite smooth construction gives
the right adjoint. Derived scalar extension preserves these categories and its usual
projection comparison gives the finite support square. On K-flat representatives this
square is the actual quotient transition; localizing that equality gives supportReduction,
including the identity level, with the chosen normalized scalar models.
For the integral comparison, tensor the ordinary compactification construction with
all quotient rings simultaneously before localization. The proper comparison is
adjoint to the actual scalar/pullback map, and the open comparison is normalized by
its unit. Their composite is sectionSupportCoefficientMap. Proper base change and
exact open scalar extension make it invertible on constructible reductions. The
normalized tower reconstruction gives the resulting whole-tower isomorphism;
evaluating its construction, rather than choosing independent level maps, gives
integralComparison. For finiteMateIso, apply sk-lem-sp-reduction to each actual
ell-power quotient map. Transport its canonical support comparison through the
identity-on-sections equivalences. Its counit identity identifies the resulting
exceptional comparison with finite.mate, by injectivity of the finite adjunction
Hom bijection. Thus it is invertible, including the identity transition.
(blueprint: lem-sp-condensed-geometric-support) -/
theorem geometric_support_exists
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    Nonempty (GeometricSupport l E (model l E X) (model l E Y)
      (fieldCompactification k X Y f)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
