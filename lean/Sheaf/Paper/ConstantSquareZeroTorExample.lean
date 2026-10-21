/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4 -/
module

public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Mathlib.Topology.Instances.ZMod

/-! # The constant square-zero residue and its two-term truncation example -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory Limits
open scoped CategoryTheory.Obj MonoidalCategory
namespace AlgebraicGeometry.ProEtale

/-- The constant square-zero residue has infinite Tor amplitude; its finite-free
presentation cone is bounded constructible of finite Tor amplitude and its upper
truncation is not of finite Tor amplitude.

Source: blueprint main-20261015, localizing-closure ctf-equals-bc proof, Examples
(blueprint: lem-sfb-constant-square-zero-tor-example).

Proof: set A = Z/ell^2 and F = A/(ell). Since ell is prime, multiplication by ell
on A has kernel ell A and square zero. The augmented complex with A in every
nonpositive degree and multiplication by ell as differential is a free resolution
of F. Tensoring it with F kills every differential, giving F in every nonpositive
cohomological degree. Constant sheafification is exact and monoidal. Its coefficient
comparison with continuous A-valued functions is an isomorphism because A is finite
discrete, and the monoidal inverse image to Spec k preserves this resolution and
its tensor calculation. Its degree-zero quotient is exactly the cokernel used in
the statement, since these functors preserve cokernels and the regular module.
The constant F is nonzero: on the nonempty scheme Spec k, constant sections inject
into the constant sheaf. Thus no finite Tor interval can contain all its tensor
cohomology. The same cokernel is finitely presented over the condensed coefficient
ring, and its pullback is a finite constant model; the one-stratum stratification
proves constructibility. Finally take the cone of multiplication by ell between
regular modules in degree zero. It is a two-term finite-free complex, hence has
Tor amplitude [-1,0]. Its two cohomology modules are constant F, so its cohomology
is bounded and constructible. Its truncation in degrees at least zero is F[0],
whose infinite Tor amplitude was just proved. This also handles ell = 2 and
arbitrary characteristic of k. Finally transport the construction along the given
coefficient isomorphism; scalar multiplication, regular modules, cokernels and the
exact monoidal derived equivalence preserve every assertion. -/
theorem constant_square_zero_tor_example (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{0}) Ab.{1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Nonempty (Mon.mk Λ ≅
      Mon.mk (Profinite.continuousCoefficientRingObj.{0} (ZMod (ℓ ^ 2)))))
    (k : Type) [Field k] [IsSepClosed k] :
    let X : Scheme.{0} := Scheme.Spec.obj (Opposite.op (CommRingCat.of k))
    let C := Mod (Sheaf (coherentTopology Profinite.{0}) Ab.{1}) Λ
    let P := cokernel ((ℓ : ℕ) • (𝟙 (𝟙_ C)))
    let Cₓ := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{1}) (condensedRingObj Λ X)
    let M : Cₓ := ((upperStarFromPoint X).mapMod Λ).obj P
    IsConstantModelConstructible Λ X M ∧
    ¬ _root_.DerivedCategory.finiteTorAmplitude Cₓ
      ((_root_.DerivedCategory.singleFunctor Cₓ 0).obj M) ∧
    ∃ K : DerivedCategory Cₓ,
      (constantModelBoundedConstructible Λ X ⊓
        _root_.DerivedCategory.finiteTorAmplitude Cₓ) K ∧
      ¬ _root_.DerivedCategory.finiteTorAmplitude Cₓ
        ((_root_.DerivedCategory.TStructure.t.truncGE 0).obj K) := by sorry

end AlgebraicGeometry.ProEtale
