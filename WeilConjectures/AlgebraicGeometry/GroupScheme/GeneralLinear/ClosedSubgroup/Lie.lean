/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.Mathlib.Algebra.Lie.Semisimple.Lemmas

/-!
# The Lie algebras of the closed subgroup schemes of `GL_n`

Let `V(I)` be the closed subgroup scheme of `𝔾𝕃(n; k)` cut out by a Hopf ideal `I` of the
coordinate ring `k[GL_n]` (`AlgebraicGeometry.GeneralLinearGroup.subgroupScheme`). This file
specialises the general theory of `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie` and
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie` to these groups, in the language
of Hopf ideals used by the weight arguments: the differentials `Lie(V(J)) → Lie(V(I))` of the
closed immersions, the Lie algebra clauses of Cartier's theorem for the *reduced* identity
component `V(identityComponent I)`, the group–Lie comparison for invariant subspaces on the
matrices `zeroLocus I k`, and the Lie algebra of the *reduced* centre `V(center I)`.

Everything that holds for an arbitrary group scheme is stated there, for an arbitrary group scheme;
what remains here is specific to the reduced identity component and the reduced centre, which this
development only has in Hopf-ideal form, and to the matrix description of the points of `V(I)`.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup.lieAlgebraMap`: the differential of the closed immersion
  `V(J) ⟶ V(I)` of closed subgroup schemes of `GL_n`.

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.lie_mem_range_lieAlgebraMap`,
  `AlgebraicGeometry.GeneralLinearGroup.lie_mem_range_lieAlgebraMap_identityComponent`: if the
  closed subgroup `V(J) ⊆ V(I)` contains the commutators of `V(I)`, then the Lie algebra of `V(J)`,
  and of its identity component, contains the brackets of the Lie algebra of `V(I)`, respectively of
  its identity component.
- `AlgebraicGeometry.GeneralLinearGroup.surjective_mulCenterIdentityComponent`,
  `AlgebraicGeometry.GeneralLinearGroup.exists_mul_eq_of_containsCommutators`: the
  central–geometric product `G° = Z(G°)° H°` for such a pair with `G°` acting semisimply on `kⁿ`,
  as a morphism of group schemes and on `k`-points.
- `AlgebraicGeometry.GeneralLinearGroup.lieAlgebraMap_identityComponent_bijective`,
  `AlgebraicGeometry.GeneralLinearGroup.finrank_lie_eq_ringKrullDim`: the Lie algebra only sees
  the reduced identity component and has the dimension of the group (Cartier's theorem).
- `AlgebraicGeometry.GeneralLinearGroup.invariant_iff_differential_invariant`,
  `AlgebraicGeometry.GeneralLinearGroup.range_lieAlgebraMap_center`: the group–Lie comparison.

## Blueprint

- `sk-d-tangent`: the Lie algebra of an algebraic group as its tangent space at the identity.
- `sk-i-cartier`: the Lie algebra clauses of Cartier's theorem.
- `sk-p-comparison`: invariant subspaces and the centre, for the group and for its Lie algebra.
- `sk-i-restriction`, `sk-p-product`: pairs `V(J) ⊆ V(I)` with `⁅V(I), V(I)⁆ ⊆ V(J)`, and the
  central–geometric product.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory TrivSqZeroExt
open scoped MonObj Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace AlgebraicGeometry.GeneralLinearGroup

open Matrix.GeneralLinearGroup

section ClosedSubgroup

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [CommRing k]
  {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]

/-- The differential `Lie(V(J)) → Lie(V(I))` of the closed immersion `V(J) ⟶ V(I)`, an injective
homomorphism of Lie algebras. (blueprint: `sk-d-tangent`) -/
noncomputable abbrev lieAlgebraMap (h : I ≤ J) :
    GrpObj.Lie (subgroupScheme J) →ₗ⁅k⁆ GrpObj.Lie (subgroupScheme I) :=
  GrpObj.differential (subgroupSchemeHom h)

theorem lieAlgebraMap_injective (h : I ≤ J) : Function.Injective (lieAlgebraMap h) :=
  GrpObj.differential_injective _

/-- If the closed subgroup `V(J) ⊆ V(I)` contains the commutators of `V(I)`, then the bracket of two
tangent vectors of `V(I)` is a tangent vector of `V(J)`: the bracket is the mixed term of the
commutator of the points `1 + εX` and `1 + δY` over `k[ε, δ]/(ε², δ²)`.
(blueprint: `sk-i-restriction`) -/
theorem lie_mem_range_lieAlgebraMap (h : I ≤ J) [IsMonHom.ContainsCommutators (subgroupSchemeHom h)]
    (X Y : GrpObj.Lie (subgroupScheme I)) : ⁅X, Y⁆ ∈ (lieAlgebraMap h).range :=
  GrpObj.lie_mem_range_differential_of_containsCommutators (subgroupSchemeHom h) X Y

end ClosedSubgroup

section Cartier

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- In characteristic zero, every tangent vector of `G = V(I)` is tangent to the reduced identity
component `V(identityComponent I)`: the differential `Lie(G°) → Lie(G)` is bijective.

`CharZero` is needed because `identityComponent I` is the ideal of the *reduced* identity
component. Proof sketch (not formalised): by Cartier's theorem
(`AlgebraicGeometry.GrpObj.isReduced_of_charZero`) `V(I)` is reduced, so the open identity
component `AlgebraicGeometry.GrpObj.identityComponent (subgroupScheme I)`, whose differential is
bijective by `AlgebraicGeometry.GrpObj.differential_identityComponentι_bijective`, is the reduced
closed subscheme on the connected component of the identity, that is `V(identityComponent I)`
(`range_subgroupSchemeHom_le_identityComponent`). (blueprint: `sk-i-cartier`) -/
theorem lieAlgebraMap_identityComponent_bijective [IsAlgClosed k] [CharZero k] :
    Function.Bijective (lieAlgebraMap (le_identityComponent I)) := by
  sorry

/-- Over an algebraically closed field of characteristic zero, the Lie algebra of an algebraic
group is the Lie algebra of its reduced identity component. (blueprint: `sk-i-cartier`) -/
noncomputable def lieAlgebraEquivIdentityComponent [IsAlgClosed k] [CharZero k] :
    GrpObj.Lie (subgroupScheme (identityComponent I)) ≃ₗ⁅k⁆ GrpObj.Lie (subgroupScheme I) :=
  LieEquiv.ofBijective _ (lieAlgebraMap_identityComponent_bijective I)

/-- Cartier's theorem, Lie algebra form: over a field of characteristic zero, the Lie algebra of
a closed subgroup scheme `V(I)` has dimension the Krull dimension of its coordinate ring. This is
`AlgebraicGeometry.GrpObj.finrank_lie_eq_topologicalKrullDim` for the affine scheme
`V(I) = Spec (k[GL_n] ⧸ I)`. (blueprint: `sk-i-cartier`) -/
theorem finrank_lie_eq_ringKrullDim [CharZero k] :
    (Module.finrank k (GrpObj.Lie (subgroupScheme I)) : WithBot ℕ∞) =
      ringKrullDim (CoordinateRing n k ⧸ I) :=
  (GrpObj.finrank_lie_eq_topologicalKrullDim (subgroupScheme I)).trans
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (CoordinateRing n k ⧸ I))

end Cartier

section Comparison

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] {m : Type u} [Fintype m] [DecidableEq m]

/-- The group–Lie comparison for invariant subspaces, for a connected closed subgroup `V(I)` of
`GL_n` over an algebraically closed field of characteristic zero, on the matrices of
`zeroLocus I k`: a subspace is stable under `V(I)(k)` acting by a rational representation `r` if
and only if it is stable under the differential of `r`. This is
`AlgebraicGeometry.GeneralLinearGroup.RationalHom.invariant_iff_differential_invariant` for
`V(I)`, which is reduced and connected since `I` is connected. (blueprint: `sk-p-comparison`) -/
theorem invariant_iff_differential_invariant [IsAlgClosed k] [CharZero k] (hconn : IsConnected I)
    (r : RationalHom (subgroupScheme I) m) [IsMonHom r] (U : Submodule k (m → k)) :
    (∀ g : zeroLocus I k,
        U ≤ U.comap (Matrix.toLin' (r.points k (zeroLocusMulEquiv I k g)))) ↔
      ∀ X : GrpObj.Lie (subgroupScheme I), U ≤ U.comap (Matrix.toLin' (r.differential X)) :=
  haveI := isReduced_subgroupScheme I hconn.isRadical
  haveI := connectedSpace_subgroupScheme I hconn
  (zeroLocusMulEquiv I k).surjective.forall.symm.trans
    (r.invariant_iff_differential_invariant U)

/-- The Lie algebra of the reduced centre of a reduced `G = V(I)` over an algebraically closed
field is contained in the centre of the Lie algebra of `G`: the reduced centre is central
scheme-theoretically (`central_subgroupSchemeHom_le_center`), so this is
`AlgebraicGeometry.GrpObj.range_differential_le_center`. (blueprint: `sk-p-comparison`) -/
theorem range_lieAlgebraMap_center_le [IsAlgClosed k] (hI : I.IsRadical) :
    (lieAlgebraMap (le_center I)).range ≤
      (LieAlgebra.center k (GrpObj.Lie (subgroupScheme I)) : LieSubalgebra k _) :=
  GrpObj.range_differential_le_center _ fun _ a b ↦ central_subgroupSchemeHom_le_center I hI a b

/-- In characteristic zero, the centre of the Lie algebra of a connected group `G = V(I)` is
contained in the Lie algebra of the reduced centre `V(center I)`.

Proof sketch (not formalised): the centre of a connected `G` is the kernel of the adjoint
representation `Ad : G → GL(Lie G)`, whose differential is `ad`; in characteristic zero the Lie
algebra of the kernel is the kernel `𝔷(Lie G)` of the differential, and the scheme-theoretic
centre is reduced, hence is `V(center I)`. (blueprint: `sk-p-comparison`) -/
theorem le_range_lieAlgebraMap_center [IsAlgClosed k] [CharZero k] (_hconn : IsConnected I) :
    (LieAlgebra.center k (GrpObj.Lie (subgroupScheme I)) : LieSubalgebra k _) ≤
      (lieAlgebraMap (le_center I)).range := by
  sorry

/-- The group–Lie comparison for the centre: over an algebraically closed field of characteristic
zero, the Lie algebra of the centre of a connected algebraic group is the centre of its Lie
algebra. (blueprint: `sk-p-comparison`) -/
theorem range_lieAlgebraMap_center [IsAlgClosed k] [CharZero k] (hconn : IsConnected I) :
    (lieAlgebraMap (le_center I)).range =
      (LieAlgebra.center k (GrpObj.Lie (subgroupScheme I)) : LieSubalgebra k _) :=
  le_antisymm (range_lieAlgebraMap_center_le hconn.isRadical) (le_range_lieAlgebraMap_center hconn)

/-- The Lie algebra of the identity component of the centre of a connected algebraic group is the
centre of its Lie algebra, in characteristic zero: the differential of `Z(G)° ⟶ G` has as range the
centre of `Lie(G)`. (blueprint: `sk-p-comparison`) -/
theorem range_lieAlgebraMap_identityComponent_center [IsAlgClosed k] [CharZero k]
    (hconn : IsConnected I) :
    (lieAlgebraMap ((le_center I).trans (le_identityComponent (center I)))).range =
      (LieAlgebra.center k (GrpObj.Lie (subgroupScheme I)) : LieSubalgebra k _) := by
  sorry

end Comparison

/-! ### Pairs of closed subgroup schemes with commutative quotient

Let `H = V(J) ⊆ G = V(I)` be closed subgroup schemes of `GL_n`, `I ≤ J`, such that the inclusion
`H ⟶ G` contains the commutators of `G` (`AlgebraicGeometry.IsMonHom.ContainsCommutators`), the
scheme-theoretic form of `⁅G, G⁆ ⊆ H`; then `H` is normal in `G`
(`AlgebraicGeometry.IsMonHom.Normal.of_containsCommutators`). The arithmetic and geometric
monodromy groups of a represented degree datum are such a pair, and the statements of the blueprint
about them are instances of the statements of this section. -/

section Pair

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k] [J.IsHopfIdeal k]

/-- The brackets of the Lie algebra of `G° = V(identityComponent I)` lie in the Lie algebra of
`H° = V(identityComponent J)`, when `H = V(J) ⊆ G = V(I)` contains the commutators of `G`: in
characteristic zero the identity components have the same Lie algebras as `G` and `H`
(`lieAlgebraEquivIdentityComponent`), and the differentials of `H° ⟶ G° ⟶ G` and `H° ⟶ H ⟶ G`
agree. (blueprint: `sk-i-restriction`) -/
theorem lie_mem_range_lieAlgebraMap_identityComponent [IsAlgClosed k] [CharZero k] (h : I ≤ J)
    [IsMonHom.ContainsCommutators (subgroupSchemeHom h)]
    (X Y : GrpObj.Lie (subgroupScheme (identityComponent I))) :
    ⁅X, Y⁆ ∈ (lieAlgebraMap (identityComponent_mono I h)).range := by
  sorry

/-- The standard representation of the `k`-points of `V(I)` on `kⁿ`: a point `Spec k ⟶ V(I)` acts
through its image in `GL_n(k)` under the closed immersion `V(I) ⟶ GL_n`.
(blueprint: `sk-d-monodromy`) -/
noncomputable def standardRepresentation (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k] :
    Representation k (points (subgroupScheme I) k) (n → k) where
  toFun g := Matrix.toLinAlgEquiv' (RationalHom.points (subgroupSchemeι I) k g : Matrix n n k)
  map_one' := by simp
  map_mul' x y := by simp

variable [IsAlgClosed k]

/-- The multiplication morphism `Z(G°)° × H° ⟶ G°` of group schemes, for closed subgroups
`H = V(J) ⊆ G = V(I)` of `GL_n`: the composite of the closed immersions of the two factors into
`G°` with the multiplication of `G°`. (blueprint: `sk-p-product`) -/
noncomputable def mulCenterIdentityComponent (h : I ≤ J) :
    subgroupScheme (identityComponent (center (identityComponent I))) ⊗
        subgroupScheme (identityComponent J) ⟶
      subgroupScheme (identityComponent I) :=
  (subgroupSchemeHom ((le_center _).trans (le_identityComponent _)) ⊗ₘ
      subgroupSchemeHom (identityComponent_mono I h)) ≫
    μ[subgroupScheme (identityComponent I)]

/-- The multiplication morphism `Z(G°)° × H° ⟶ G°` sends a point `a` to the product of its two
components. -/
theorem comp_mulCenterIdentityComponent (h : I ≤ J) {X : Over (Spec (.of k))}
    (a : X ⟶ subgroupScheme (identityComponent (center (identityComponent I))) ⊗
        subgroupScheme (identityComponent J)) :
    a ≫ mulCenterIdentityComponent h =
      a ≫ fst _ _ ≫ subgroupSchemeHom ((le_center _).trans (le_identityComponent _)) *
        a ≫ snd _ _ ≫ subgroupSchemeHom (identityComponent_mono I h) := by
  rw [mulCenterIdentityComponent, ← lift_fst_comp_snd_comp, comp_lift_assoc, Hom.mul_def]

/-- The points of `Z(G°)°` commute with the points of `G°`. -/
theorem commute_comp_subgroupSchemeHom_identityComponent_center {X : Over (Spec (.of k))}
    (t : X ⟶ subgroupScheme (identityComponent (center (identityComponent I))))
    (g : X ⟶ subgroupScheme (identityComponent I)) :
    Commute (t ≫ subgroupSchemeHom ((le_center _).trans (le_identityComponent _))) g := by
  rw [← subgroupSchemeHom_comp (le_center _) (le_identityComponent _), ← Category.assoc]
  exact central_subgroupSchemeHom_le_center _ (isRadical_identityComponent I) _ g

/-- The multiplication morphism `Z(G°)° × H° ⟶ G°` is a homomorphism of group schemes, since
`Z(G°)°` is central in `G°`. -/
instance (h : I ≤ J) : IsMonHom (mulCenterIdentityComponent h) where
  one_hom := by
    have e {M : Over (Spec (.of k))} [MonObj M] : η[M] = (1 : 𝟙_ _ ⟶ M) := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [e, e, comp_mulCenterIdentityComponent]
    simp only [MonObj.one_comp, mul_one]
  mul_hom := by
    have e {M : Over (Spec (.of k))} [MonObj M] : μ[M] = fst M M * snd M M := by
      rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    let Z := subgroupScheme (identityComponent (center (identityComponent I)))
    let H := subgroupScheme (identityComponent J)
    have hc := commute_comp_subgroupSchemeHom_identityComponent_center
      (snd (Z ⊗ H) (Z ⊗ H) ≫ fst Z H)
      (fst (Z ⊗ H) (Z ⊗ H) ≫ snd Z H ≫ subgroupSchemeHom (identityComponent_mono I h))
    rw [Category.assoc] at hc
    rw [e (M := Z ⊗ H), ← lift_fst_comp_snd_comp, ← Hom.mul_def, comp_mulCenterIdentityComponent,
      comp_mulCenterIdentityComponent, comp_mulCenterIdentityComponent, MonObj.mul_comp,
      MonObj.mul_comp, hc.symm.mul_mul_mul_comm]

/-- The multiplication morphism `Z(G°)° × H° ⟶ G°` sends the `k`-point `(t, x)` to the matrix
`t x`. -/
theorem homMulEquiv_lift_comp_mulCenterIdentityComponent (h : I ≤ J)
    (t : zeroLocus (identityComponent (center (identityComponent I))) k)
    (x : zeroLocus (identityComponent J) k) :
    GeneralLinearGroup.homMulEquiv n k k
      ((lift (zeroLocusMulEquiv _ k t) (zeroLocusMulEquiv _ k x) ≫
        mulCenterIdentityComponent h) ≫ subgroupSchemeι (identityComponent I)) =
      (t : GL n k) * (x : GL n k) := by
  rw [comp_mulCenterIdentityComponent, MonObj.mul_comp, lift_fst_assoc, lift_snd_assoc,
    Category.assoc, Category.assoc, subgroupSchemeHom_comp_subgroupSchemeι,
    subgroupSchemeHom_comp_subgroupSchemeι, map_mul, homMulEquiv_zeroLocusMulEquiv_comp,
    homMulEquiv_zeroLocusMulEquiv_comp]

/-- The product `t x` of a point `t` of `Z(G°)°(k)` and a point `x` of `H°(k)` lies in the image
of the multiplication morphism `Z(G°)° × H° ⟶ G°`, read in `Spec k[GL_n]`. -/
theorem toPrimeSpectrum_mul_mem_image_range_mulCenterIdentityComponent (h : I ≤ J)
    (t : zeroLocus (identityComponent (center (identityComponent I))) k)
    (x : zeroLocus (identityComponent J) k) :
    toPrimeSpectrum ((t : GL n k) * (x : GL n k)) ∈
      (subgroupSchemeι (identityComponent I)).left.base ''
        Set.range (mulCenterIdentityComponent h).left.base := by
  obtain ⟨s⟩ : Nonempty (Spec (.of k)) := inferInstance
  have e := left_base_eq_toPrimeSpectrum
    ((lift (zeroLocusMulEquiv _ k t) (zeroLocusMulEquiv _ k x) ≫ mulCenterIdentityComponent h) ≫
      subgroupSchemeι (identityComponent I)) s
  rw [homMulEquiv_lift_comp_mulCenterIdentityComponent, Over.comp_left, Over.comp_left,
    Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e
  exact ⟨_, Set.mem_range_self _, e⟩

variable [CharZero k]

/-- The Lie algebra of `G° = V(identityComponent I)` is the sum of its centre and its derived
subalgebra when `G°` acts semisimply on `kⁿ`: through the faithful representation
`Lie G° ⊆ gl_n`, whose Lie submodules are the `G°`-stable subspaces by the group–Lie comparison,
`Lie G°` has central radical. (blueprint: `sk-p-product`) -/
theorem center_sup_derivedSeries_lie_identityComponent_eq_top
    [Representation.IsSemisimpleRepresentation (standardRepresentation (identityComponent I))] :
    LieAlgebra.center k (GrpObj.Lie (subgroupScheme (identityComponent I))) ⊔
      LieAlgebra.derivedSeries k (GrpObj.Lie (subgroupScheme (identityComponent I))) 1 = ⊤ := by
  have := connectedSpace_subgroupScheme _ (isConnected_identityComponent I)
  let r := subgroupSchemeι (identityComponent I)
  let φ : GrpObj.Lie (subgroupScheme (identityComponent I)) →ₗ⁅k⁆ Module.End k (n → k) :=
    (lieEquivMatrix' (R := k) (n := n)).symm.toLieHom.comp (RationalHom.differential r)
  have hφ : Function.Injective φ :=
    (lieEquivMatrix' (R := k) (n := n)).symm.injective.comp
      ((lieAlgebraEquivMatrix n k).injective.comp (GrpObj.differential_injective r))
  let := LieRingModule.compLieHom (n → k) φ
  have := LieModule.compLieHom (R := k) (n → k) φ
  have : Module.Finite k (GrpObj.Lie (subgroupScheme (identityComponent I))) :=
    Module.Finite.of_injective (φ : _ →ₗ[k] Module.End k (n → k)) hφ
  have : LieModule.IsFaithful k (GrpObj.Lie (subgroupScheme (identityComponent I))) (n → k) :=
    ⟨fun x y hxy ↦ hφ (LinearMap.ext fun v ↦ LinearMap.congr_fun hxy v)⟩
  have hcomp := RationalHom.invariant_iff_differential_invariant r
  have hbr (X : GrpObj.Lie (subgroupScheme (identityComponent I))) (w : n → k) :
      ⁅X, w⁆ = Matrix.toLin' (RationalHom.differential r X) w :=
    rfl
  let e : LieSubmodule k (GrpObj.Lie (subgroupScheme (identityComponent I))) (n → k) ≃o
      Subrepresentation (standardRepresentation (identityComponent I)) :=
    { toFun N := ⟨N.toSubmodule, fun g v hv ↦ (hcomp N.toSubmodule).2
        (fun X w hw ↦ Submodule.mem_comap.2 (hbr X w ▸ N.lie_mem (x := X) hw)) g hv⟩
      invFun W := { W.toSubmodule with
        lie_mem := fun {X} {w} hw ↦ (hbr X w).symm ▸
          (hcomp W.toSubmodule).1 (fun g u hu ↦ W.apply_mem_toSubmodule g hu) X hw }
      left_inv _ := rfl
      right_inv _ := rfl
      map_rel_iff' := Iff.rfl }
  have : LieModule.IsSemisimple k (GrpObj.Lie (subgroupScheme (identityComponent I))) (n → k) :=
    e.complementedLattice_iff.2 inferInstance
  have := LieAlgebra.hasCentralRadical_of_isFaithful k
    (GrpObj.Lie (subgroupScheme (identityComponent I))) (n → k)
  exact LieAlgebra.center_sup_derivedSeries_eq_top k _

/-- **The central–geometric product.** Let `H = V(J) ⊆ G = V(I)` be closed subgroups of `GL_n` over
an algebraically closed field of characteristic zero such that `H` contains the commutators of `G`
and `G°` acts semisimply on `kⁿ`. Then `G° = Z(G°)° H°`: the multiplication morphism
`Z(G°)° × H° ⟶ G°` is surjective.

Proof: the Lie algebra `𝔤 = Lie G° ⊆ 𝔤𝔩_n` is a faithful semisimple Lie
representation, so `𝔤 = 𝔷(𝔤) + [𝔤, 𝔤]`; the brackets lie in `Lie H°`
(`lie_mem_range_lieAlgebraMap_identityComponent`) and `𝔷(𝔤) = Lie Z(G°)°`
(`range_lieAlgebraMap_identityComponent_center`), so `𝔤 = Lie Z(G°)° + Lie H°`. The multiplication
morphism is a homomorphism because `Z(G°)°` is central, so its image is closed
(`AlgebraicGeometry.isClosed_range_of_isMonHom`) and connected, and its Lie algebra is `𝔤`; by
Cartier's theorem it has the dimension of `G°`, hence is all of `G°`
(`AlgebraicGeometry.isIso_left_of_topologicalKrullDim_eq`). (blueprint: `sk-p-product`) -/
theorem surjective_mulCenterIdentityComponent (h : I ≤ J)
    [IsMonHom.ContainsCommutators (subgroupSchemeHom h)]
    [Representation.IsSemisimpleRepresentation (standardRepresentation (identityComponent I))] :
    Function.Surjective (mulCenterIdentityComponent h).left.base := by
  -- The subgroup `Γ = Z(G°)°(k) H°(k)` of `GL n k` and its Zariski closure `V(L)`.
  have hZ : zeroLocus (identityComponent (center (identityComponent I))) k ≤
      zeroLocus (center (identityComponent I)) k :=
    zeroLocus_anti (le_identityComponent _)
  have hH : zeroLocus (identityComponent J) k ≤ zeroLocus (identityComponent I) k :=
    zeroLocus_anti (identityComponent_mono I h)
  have hcomm (t : zeroLocus (identityComponent (center (identityComponent I))) k)
      (x : zeroLocus (identityComponent J) k) : Commute (t : GL n k) x :=
    ((mem_zeroLocus_center_iff _).1 (hZ t.2)).2 _ (hH x.2)
  let Γ : Subgroup (GL n k) :=
    (MonoidHom.noncommCoprod (Subgroup.subtype _) (Subgroup.subtype _) hcomm).range
  have hΓ : (Γ : Set (GL n k)) ⊆ zeroLocus (identityComponent I) k := by
    rintro _ ⟨⟨t, x⟩, rfl⟩
    exact mul_mem ((mem_zeroLocus_center_iff _).1 (hZ t.2)).1 (hH x.2)
  have hIL : identityComponent I ≤ vanishingIdeal (Γ : Set (GL n k)) :=
    (le_vanishingIdeal_zeroLocus _).trans (vanishingIdeal_anti hΓ)
  have hLZ : vanishingIdeal (Γ : Set (GL n k)) ≤ identityComponent (center (identityComponent I)) :=
    (vanishingIdeal_anti fun t ht ↦ MonoidHom.mem_range.2 ⟨(⟨t, ht⟩, 1), by simp⟩).trans
      (vanishingIdeal_zeroLocus_le_of_isRadical _ (isRadical_identityComponent _))
  have hLH : vanishingIdeal (Γ : Set (GL n k)) ≤ identityComponent J :=
    (vanishingIdeal_anti fun x hx ↦ MonoidHom.mem_range.2 ⟨(1, ⟨x, hx⟩), by simp⟩).trans
      (vanishingIdeal_zeroLocus_le_of_isRadical _ (isRadical_identityComponent _))
  -- The Lie algebra of `V(L)` is all of `Lie G°`.
  have hrange {K : Ideal (CoordinateRing n k)} [K.IsHopfIdeal k] (hK : identityComponent I ≤ K)
      (hLK : vanishingIdeal (Γ : Set (GL n k)) ≤ K) :
      (lieAlgebraMap hK).range ≤ (lieAlgebraMap hIL).range := by
    rintro _ ⟨y, rfl⟩
    refine ⟨lieAlgebraMap hLK y, ?_⟩
    rw [lieAlgebraMap, lieAlgebraMap, lieAlgebraMap,
      GrpObj.differential_congr (subgroupSchemeHom_comp hIL hLK).symm, GrpObj.differential_comp]
    rfl
  have htop (X : GrpObj.Lie (subgroupScheme (identityComponent I))) :
      X ∈ (lieAlgebraMap hIL).range := by
    have hX : X ∈ LieAlgebra.center k (GrpObj.Lie (subgroupScheme (identityComponent I))) ⊔
        LieAlgebra.derivedSeries k (GrpObj.Lie (subgroupScheme (identityComponent I))) 1 := by
      rw [center_sup_derivedSeries_lie_identityComponent_eq_top]
      exact LieSubmodule.mem_top X
    obtain ⟨Y, hY, Z, hZ, rfl⟩ := LieSubmodule.mem_sup _ _ _ |>.1 hX
    refine add_mem (hrange ((le_center _).trans (le_identityComponent _)) hLZ ?_) ?_
    · rw [range_lieAlgebraMap_identityComponent_center (isConnected_identityComponent I)]
      exact hY
    · rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
        LieAlgebra.derivedSeriesOfIdeal_zero, ← LieSubmodule.mem_toSubmodule,
        LieSubmodule.lieIdeal_oper_eq_linear_span'] at hZ
      refine (Submodule.span_le (p := (lieAlgebraMap hIL).range.toSubmodule)).2 ?_ hZ
      rintro _ ⟨X, -, Y, -, rfl⟩
      exact hrange (identityComponent_mono I h) hLH
        (lie_mem_range_lieAlgebraMap_identityComponent h X Y)
  -- Hence `V(L) = G°` by Cartier's theorem.
  have hbij : Function.Bijective (lieAlgebraMap hIL) :=
    ⟨lieAlgebraMap_injective hIL, fun X ↦ (htop X)⟩
  have hdim : topologicalKrullDim (subgroupScheme (vanishingIdeal (Γ : Set (GL n k)))).left =
      topologicalKrullDim (subgroupScheme (identityComponent I)).left := by
    rw [← GrpObj.finrank_lie_eq_topologicalKrullDim, ← GrpObj.finrank_lie_eq_topologicalKrullDim,
      (LinearEquiv.ofBijective (lieAlgebraMap hIL).toLinearMap hbij).finrank_eq]
  have := isReduced_subgroupScheme _ (isRadical_vanishingIdeal (Γ : Set (GL n k)))
  have := isReduced_subgroupScheme _ (isRadical_identityComponent I)
  have := connectedSpace_subgroupScheme _ (isConnected_identityComponent I)
  have := isIso_left_of_topologicalKrullDim_eq (subgroupSchemeHom hIL) hdim
  -- The image of the multiplication is closed and contains `Γ`, hence contains `V(L) = G°`.
  have hι := (subgroupSchemeι (identityComponent I)).left.isClosedEmbedding
  have hΓR (γ : GL n k) (hγ : γ ∈ Γ) : toPrimeSpectrum γ ∈
      (subgroupSchemeι (identityComponent I)).left.base ''
        Set.range (mulCenterIdentityComponent h).left.base := by
    obtain ⟨⟨t, x⟩, rfl⟩ := hγ
    exact toPrimeSpectrum_mul_mem_image_range_mulCenterIdentityComponent h t x
  have hcl : PrimeSpectrum.zeroLocus (vanishingIdeal (Γ : Set (GL n k)) :
      Set (CoordinateRing n k)) ⊆ (subgroupSchemeι (identityComponent I)).left.base ''
        Set.range (mulCenterIdentityComponent h).left.base := by
    have e : vanishingIdeal (Γ : Set (GL n k)) =
        PrimeSpectrum.vanishingIdeal (toPrimeSpectrum '' (Γ : Set (GL n k))) := by
      ext a
      simp [mem_vanishingIdeal, PrimeSpectrum.mem_vanishingIdeal, toPrimeSpectrum]
    rw [e, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact closure_minimal (by rintro _ ⟨γ, hγ, rfl⟩; exact hΓR γ hγ)
      (hι.isClosedMap _ (isClosed_range_of_isMonHom (mulCenterIdentityComponent h)))
  intro p
  obtain ⟨q, rfl⟩ := (subgroupSchemeHom hIL).left.homeomorph.surjective p
  have hq : (subgroupSchemeι (identityComponent I)).left.base
      ((subgroupSchemeHom hIL).left.base q) ∈
        PrimeSpectrum.zeroLocus (vanishingIdeal (Γ : Set (GL n k)) : Set (CoordinateRing n k)) := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, subgroupSchemeHom_comp_subgroupSchemeι]
    exact left_base_subgroupSchemeι_mem_zeroLocus _ q
  obtain ⟨_, hr, e⟩ := hcl hq
  exact hι.injective e ▸ hr

/-- The central–geometric product on `k`-points: every point of `G°` is a product `t h` of a point
`t` of `Z(G°)°` and a point `h` of `H°`. Proof: a `k`-point of `G°` lifts
along the surjective multiplication morphism to a `k`-point of `Z(G°)° × H°`
(`AlgebraicGeometry.exists_points_comp_eq_of_surjective`), whose two projections are `t` and `h`.
(blueprint: `sk-p-product`) -/
theorem exists_mul_eq_of_containsCommutators (h : I ≤ J)
    [IsMonHom.ContainsCommutators (subgroupSchemeHom h)]
    [Representation.IsSemisimpleRepresentation (standardRepresentation (identityComponent I))]
    (g : points (subgroupScheme (identityComponent I)) k) :
    ∃ (t : points (subgroupScheme (identityComponent (center (identityComponent I)))) k)
      (x : points (subgroupScheme (identityComponent J)) k),
      t ≫ subgroupSchemeHom ((le_center _).trans (le_identityComponent _)) *
        x ≫ subgroupSchemeHom (identityComponent_mono I h) = g := by
  obtain ⟨p, hp⟩ := exists_points_comp_eq_of_surjective _
    (surjective_mulCenterIdentityComponent h) g
  refine ⟨p ≫ fst _ _, p ≫ snd _ _, ?_⟩
  rw [← hp, comp_mulCenterIdentityComponent, Category.assoc, Category.assoc]

end Pair

end AlgebraicGeometry.GeneralLinearGroup
