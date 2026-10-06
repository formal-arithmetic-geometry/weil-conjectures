/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.AlgebraicGeometry.DualNumbers
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.TangentSpace

/-!
# The Lie algebra of a group scheme

Let `G` be a group scheme over a scheme `S`, with structure morphism `f : G ⟶ S`, identity
section `e : S ⟶ G` and multiplication `m : G ×_S G ⟶ G`. Set `ω_{G/S} = e^*Ω¹_{G/S}`. The *Lie
algebra sheaf* of `G/S` is the `𝒪_S`-module

$$
\operatorname{Lie}(G/S) = \mathcal{H}om_{\mathcal O_S}(\omega_{G/S}, \mathcal O_S),
$$

the sheaf of relative tangent vectors along the identity section, and the *Lie algebra*
`Lie(G) = Hom_{𝒪_S}(ω_{G/S}, 𝒪_S)` is its module of global sections. When `G ⟶ S` is smooth,
`ω_{G/S}` is locally free and `Lie(G/S) ≅ e^*T_{G/S}` is the pullback of the tangent sheaf; for an
arbitrary group scheme the dual-of-cotangent definition is the right one.

## Infinitesimal points

The dual-number thickening `S[ε]` of the base (`AlgebraicGeometry.Scheme.dualNumbers`) is a scheme
over `S` through the projection `p : S[ε] ⟶ S`, and the closed immersion `i : S ⟶ S[ε]`, `ε ↦ 0`,
is a section of `p`. The *infinitesimal points* of `G` are the points `v : S[ε] ⟶ G` over `S` with
`i ≫ v = e`; they form a normal subgroup `infPoints G` of the group `G(S[ε])`, whose group law is
the addition of tangent vectors. A point `v` has the same underlying map as `e`, and on functions
`v^♯(a) = e^♯(a) + ε d_v(a)`; the `ε`-coefficient `d_v` is a derivation `𝒪_G → e_*𝒪_S` over
`f⁻¹𝒪_S`, that is a morphism `Ω¹_{G/S} ⟶ e_*𝒪_S`, that is an element of
`Lie(G) = Hom(e^*Ω¹_{G/S}, 𝒪_S)`. This is the bridge `GrpObj.toLie : infPoints G → Lie G`, a
bijection (`GrpObj.lieEquiv`).

## The bracket

Over the two-parameter thickening `S[ε][δ]`, a point `v : S[ε] ⟶ G` gives `v_ε` and `v_δ` by the
two projections. The commutator `c(v, w) = v_ε w_δ v_ε⁻¹ w_δ⁻¹` reduces to the identity both for
`ε = 0` and for `δ = 0`, and the points of `G` over `S[ε][δ]` with this property are in bijection
with `infPoints G` through `η ↦ εδ` (`GrpObj.mixedEquiv`). The Lie bracket is the mixed term of the
commutator,

$$
[v, w] = \mu^{-1}(v_ε w_δ v_ε^{-1} w_δ^{-1}),
$$

transported to `Lie(G)` along the bridge. This is the restriction to the identity of the commutator
`[ṽ, w̃]` of the left-invariant vector fields `ṽ(g, d) = g v(d)` extending `v` and `w`: the
pullback of right multiplication by `v_ε` on the functions of `G[ε]` is `1 + ε D_v`, so that of
`c(v, w)` is `1 + εδ (D_v D_w - D_w D_v)`. For an affine `G = Spec A` it is the convolution
commutator `(v ⊗ w - w ⊗ v) ∘ Δ` of point derivations at the counit. For `G = GL_n`, where the
infinitesimal points are the matrices `1 + εX`, it is the matrix commutator, and
`Lie(GL_n) = gl_n`; see `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie`, and
`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie` for the Lie
algebras of the closed subgroup schemes of `GL_n`.

## Main definitions

- `AlgebraicGeometry.GrpObj.unitSection`, `AlgebraicGeometry.GrpObj.omega`,
  `AlgebraicGeometry.GrpObj.lieAlgebraSheaf`: the identity section, `ω_{G/S}` and `Lie(G/S)`.
- `AlgebraicGeometry.GrpObj.Lie`: the Lie algebra `Lie(G) = Hom(ω_{G/S}, 𝒪_S)`, a module over
  `Γ(S, 𝒪_S)`, and over `R` when `S = Spec R`, with its `LieRing` and `LieAlgebra` structures.
- `AlgebraicGeometry.GrpObj.infPoints`: the infinitesimal points `ker(G(S[ε]) → G(S))`, and the
  bridge `AlgebraicGeometry.GrpObj.lieEquiv : infPoints G ≃ Lie G`.
- `AlgebraicGeometry.GrpObj.differential`: the differential `Lie(G) →ₗ⁅R⁆ Lie(H)` of a
  homomorphism of group schemes over `R`.
- `AlgebraicGeometry.tangentGroup`, `AlgebraicGeometry.GrpObj.infPointsEquivTangentGroup`: for `G`
  over `Spec R`, the infinitesimal points are the points with values in the ring of dual numbers
  `R[ε]` reducing to the identity.
- `AlgebraicGeometry.GrpObj.lieEquivIdentityComponent`: `Lie(G°) = Lie(G)` for a group scheme of
  finite type over a field.

## Main results

- `AlgebraicGeometry.GrpObj.lieAlgebraSheaf_iso_pullback_tangentSheaf`: for smooth `G ⟶ S`,
  `Lie(G/S) ≅ e^*T_{G/S}`.
- `AlgebraicGeometry.GrpObj.differential_injective`: a monomorphism of group schemes has an
  injective differential; `AlgebraicGeometry.GrpObj.differential_bijective_of_isOpenImmersion`: an
  open immersion of group schemes has a bijective differential.
- `AlgebraicGeometry.GrpObj.lie_mem_range_differential_of_commutator_mem`: if the commutators of
  `H` factor through a subgroup scheme `G ⟶ H`, then the brackets of tangent vectors of `H` are
  tangent to `G`.
- `AlgebraicGeometry.GrpObj.range_differential_le_center`: the tangent vectors of a central
  subgroup scheme are central in the Lie algebra.
- `AlgebraicGeometry.GrpObj.finrank_lie_eq_topologicalKrullDim`: in characteristic zero the Lie
  algebra has the dimension of the group (Cartier's theorem).

## Implementation notes

All constructions are genuine definitions; the proofs that are still missing (the sheaf and local
conditions of the thickening, the bijectivity of the bridge and of the mixed-term map, the Lie
algebra axioms, and the functoriality of the bracket) are recorded as `sorry`. The base ring of a
group scheme over an affine base is written `R`; `k` is reserved for a field.

## Blueprint

- `sk-d-tangent`: the Lie algebra of an algebraic group as its tangent space at the identity.
- `sk-i-cartier`: the Lie algebra clauses of Cartier's theorem.
- `sk-p-comparison`: the Lie algebra of a central subgroup scheme.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry

/-! ### The Lie algebra sheaf and the Lie algebra over a general base -/

namespace GrpObj

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- The identity section `e : S ⟶ G` of a group scheme `G` over `S`: the unit `η : 𝟙 ⟶ G` of the
group object, as a morphism of schemes. -/
noncomputable def unitSection : S ⟶ G.left :=
  η[G].left

/-- The identity section is a section of the structure morphism. -/
theorem unitSection_comp_hom : unitSection G ≫ G.hom = 𝟙 S :=
  Over.w η[G]

/-- The `𝒪_S`-module `ω_{G/S} = e^*Ω¹_{G/S}`: the cotangent sheaf of `G/S` pulled back along the
identity section. For smooth `G` it is locally free, and `Lie(G/S)` is its dual.
(blueprint: `sk-d-tangent`) -/
noncomputable def omega : S.Modules :=
  (Scheme.Modules.pullback (unitSection G)).obj G.hom.cotangentSheaf

/-- The Lie algebra sheaf `Lie(G/S) = ℋom_{𝒪_S}(ω_{G/S}, 𝒪_S)` of a group scheme `G` over `S`: the
sheaf of relative tangent vectors along the identity section. (blueprint: `sk-d-tangent`) -/
noncomputable def lieAlgebraSheaf : S.Modules :=
  Scheme.Modules.dual (omega G)

theorem lieAlgebraSheaf_eq_tangentSheafAlong :
    lieAlgebraSheaf G = G.hom.tangentSheafAlong (unitSection G) :=
  rfl

/-- For a smooth group scheme, the Lie algebra sheaf is the pullback `e^*T_{G/S}` of the tangent
sheaf along the identity section. -/
theorem lieAlgebraSheaf_iso_pullback_tangentSheaf [Smooth G.hom] :
    Nonempty (lieAlgebraSheaf G ≅
      (Scheme.Modules.pullback (unitSection G)).obj G.hom.tangentSheaf) :=
  G.hom.tangentSheafAlong_iso_pullback_tangentSheaf (unitSection G) (unitSection_comp_hom G)

/-- The Lie algebra `Lie(G) = Hom_{𝒪_S}(ω_{G/S}, 𝒪_S)` of a group scheme `G` over `S`: the global
sections of the Lie algebra sheaf, the module of relative tangent vectors at the identity. Its Lie
bracket is constructed below. (blueprint: `sk-d-tangent`) -/
def Lie : Type u :=
  omega G ⟶ Scheme.Modules.unitModule S

noncomputable instance : AddCommGroup (Lie G) :=
  inferInstanceAs (AddCommGroup (omega G ⟶ Scheme.Modules.unitModule S))

noncomputable instance : Module Γ(S, ⊤) (Lie G) :=
  inferInstanceAs (Module Γ(S, ⊤) (omega G ⟶ Scheme.Modules.unitModule S))

/-- The Lie algebra is the module of global sections of the Lie algebra sheaf. -/
theorem nonempty_lie_equiv_sections : Nonempty (Lie G ≃+ Γ(lieAlgebraSheaf G, ⊤)) := by
  sorry

end GrpObj

/-! ### Infinitesimal points -/

section InfPoints

variable (S : Scheme.{u})

/-- The thickening `S[ε]` as a scheme over `S`, through the projection `p : S[ε] ⟶ S`. -/
noncomputable def dualNumbersOver : Over S :=
  Over.mk S.dualNumbersProj

/-- The two-parameter thickening `S[ε][δ]` as a scheme over `S`. -/
noncomputable def dualNumbers₂Over : Over S :=
  Over.mk (S.dualNumbers.dualNumbersProj ≫ S.dualNumbersProj)

/-- The closed immersion `i : S ⟶ S[ε]`, `ε ↦ 0`, as a morphism over `S`. -/
noncomputable def dualNumbersιOver : Over.mk (𝟙 S) ⟶ dualNumbersOver S :=
  Over.homMk S.dualNumbersι

/-- The projection `S[ε][δ] ⟶ S[ε]` forgetting `δ`, as a morphism over `S`. -/
noncomputable def dualNumbersProjεOver : dualNumbers₂Over S ⟶ dualNumbersOver S :=
  Over.homMk S.dualNumbers.dualNumbersProj

/-- The projection `S[ε][δ] ⟶ S[δ]` forgetting `ε`, as a morphism over `S`. -/
noncomputable def dualNumbersProjδOver : dualNumbers₂Over S ⟶ dualNumbersOver S :=
  Over.homMk S.dualNumbersProj.dualNumbers (by simp [dualNumbers₂Over, dualNumbersOver])

/-- The closed immersion `S[ε] ⟶ S[ε][δ]`, `δ ↦ 0`, as a morphism over `S`. -/
noncomputable def dualNumbersιεOver : dualNumbersOver S ⟶ dualNumbers₂Over S :=
  Over.homMk S.dualNumbers.dualNumbersι (by simp [dualNumbers₂Over, dualNumbersOver])

/-- The closed immersion `S[δ] ⟶ S[ε][δ]`, `ε ↦ 0`, as a morphism over `S`. -/
noncomputable def dualNumbersιδOver : dualNumbersOver S ⟶ dualNumbers₂Over S :=
  Over.homMk S.dualNumbersι.dualNumbers (by simp [dualNumbers₂Over, dualNumbersOver])

/-- The map `S[ε][δ] ⟶ S[η]`, `η ↦ εδ`, as a morphism over `S`. -/
noncomputable def dualNumbersMulOver : dualNumbers₂Over S ⟶ dualNumbersOver S :=
  Over.homMk S.dualNumbersMul (by simp [dualNumbers₂Over, dualNumbersOver])

variable {S} (G : Over S) [GrpObj G]

/-- Precomposition with a morphism `f : X ⟶ Y` over `S`, as a group homomorphism
`G(Y) →* G(X)` on points of a group scheme. -/
noncomputable def pointsPrecomp {X Y : Over S} (f : X ⟶ Y) : (Y ⟶ G) →* (X ⟶ G) where
  toFun y := f ≫ y
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

@[simp]
theorem pointsPrecomp_apply {X Y : Over S} (f : X ⟶ Y) (y : Y ⟶ G) :
    pointsPrecomp G f y = f ≫ y :=
  rfl

namespace GrpObj

/-- The infinitesimal points of a group scheme `G` over `S`: the points `v : S[ε] ⟶ G` over `S`
reducing to the identity along `i : S ⟶ S[ε]`, the kernel of `G(S[ε]) → G(S)`. Its group law is
the addition of tangent vectors, and it is in bijection with `Lie(G)` (`lieEquiv`).
(blueprint: `sk-d-tangent`) -/
noncomputable def infPoints : Subgroup (dualNumbersOver S ⟶ G) :=
  (pointsPrecomp G (dualNumbersιOver S)).ker

theorem mem_infPoints {v : dualNumbersOver S ⟶ G} :
    v ∈ infPoints G ↔ dualNumbersιOver S ≫ v = 1 :=
  MonoidHom.mem_ker

instance : (infPoints G).Normal :=
  MonoidHom.normal_ker _

/-- The identity point, as a morphism of schemes, is the identity section. -/
theorem one_left : (1 : Over.mk (𝟙 S) ⟶ G).left = unitSection G := by
  have h : (SemiCartesianMonoidalCategory.toUnit (Over.mk (𝟙 S))).left = 𝟙 S :=
    (Category.comp_id _).symm.trans (Over.w _)
  rw [Hom.one_def, Over.comp_left, h]
  exact Category.id_comp _

theorem ι_comp_left_eq {v : dualNumbersOver S ⟶ G} (hv : v ∈ infPoints G) :
    S.dualNumbersι ≫ v.left = unitSection G := by
  rw [mem_infPoints] at hv
  rw [← one_left G, ← hv]
  rfl

/-! ### The bridge from infinitesimal points to the Lie algebra -/

/-- The derivation `d_v : 𝒪_G → (i ≫ v)_*𝒪_S` attached to a point `v : S[ε] ⟶ G`: the
`ε`-coefficient of `v^♯(a) = e^♯(a) + ε d_v(a)`. It is a derivation over `f⁻¹𝒪_S` because `v`
is a morphism of schemes over `S` and `ε² = 0`. -/
noncomputable def infDerivation (v : dualNumbersOver S ⟶ G) :
    ((Scheme.Modules.pushforward (S.dualNumbersι ≫ v.left)).obj
      (Scheme.Modules.unitModule S)).val.Derivation' G.hom.pullbackPresheafHom where
  d {V} :=
    { toFun := fun a ↦ (v.left.app V.unop a).snd
      map_zero' := by sorry
      map_add' := by sorry }
  d_mul := by sorry
  d_map := by sorry
  d_app := by sorry

/-- The morphism `(i ≫ v)^*Ω¹_{G/S} ⟶ 𝒪_S` attached to a point `v : S[ε] ⟶ G`: the derivation
`d_v` through the universal property of `Ω¹_{G/S}` and the adjunction `(i ≫ v)^* ⊣ (i ≫ v)_*`. -/
noncomputable def omegaHom (v : dualNumbersOver S ⟶ G) :
    (Scheme.Modules.pullback (S.dualNumbersι ≫ v.left)).obj G.hom.cotangentSheaf ⟶
      Scheme.Modules.unitModule S :=
  ((Scheme.Modules.pullbackPushforwardAdjunction _).homEquiv _ _).symm
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 _)).symm
      ((PresheafOfModules.DifferentialsConstruction.isUniversal' _).desc (infDerivation G v)))

/-- The bridge from infinitesimal points to the Lie algebra: a point `v : S[ε] ⟶ G` reducing to
the identity goes to the `ε`-coefficient of `v^♯`, a derivation `𝒪_G → e_*𝒪_S`, that is a morphism
`ω_{G/S} = e^*Ω¹_{G/S} ⟶ 𝒪_S`. (blueprint: `sk-d-tangent`) -/
noncomputable def toLie (v : infPoints G) : Lie G :=
  (Scheme.Modules.pullbackCongr (ι_comp_left_eq G v.2)).inv.app G.hom.cotangentSheaf ≫
    omegaHom G v.1

/-- The bridge is a bijection: a morphism `ω_{G/S} ⟶ 𝒪_S` is a derivation `d : 𝒪_G → e_*𝒪_S`, and
`a ↦ e^♯(a) + ε d(a)` is a morphism of schemes `S[ε] ⟶ G` over `S` reducing to the identity, since
its stalk maps are local, their reductions modulo `ε` being the local maps `e^♯`. -/
theorem toLie_bijective : Function.Bijective (toLie G) := by
  sorry

/-- The infinitesimal points of `G` are its Lie algebra. (blueprint: `sk-d-tangent`) -/
noncomputable def lieEquiv : infPoints G ≃ Lie G :=
  Equiv.ofBijective _ (toLie_bijective G)

/-- The bridge turns the group law of the infinitesimal points into the addition of `Lie(G)`. -/
theorem lieEquiv_mul (v w : infPoints G) : lieEquiv G (v * w) = lieEquiv G v + lieEquiv G w := by
  sorry

theorem lieEquiv_one : lieEquiv G 1 = 0 := by
  sorry

/-- The infinitesimal points form a commutative group: their group law is the addition of tangent
vectors. -/
theorem isMulCommutative_infPoints : IsMulCommutative (infPoints G) :=
  ⟨⟨fun v w ↦ (lieEquiv G).injective (by rw [lieEquiv_mul, lieEquiv_mul, add_comm])⟩⟩

/-! ### The bracket as the mixed term of the commutator -/

/-- The points of `G` over `S[ε][δ]` reducing to the identity both for `ε = 0` and for `δ = 0`. -/
noncomputable def mixedPoints : Subgroup (dualNumbers₂Over S ⟶ G) :=
  (pointsPrecomp G (dualNumbersιεOver S)).ker ⊓ (pointsPrecomp G (dualNumbersιδOver S)).ker

theorem mem_mixedPoints {z : dualNumbers₂Over S ⟶ G} :
    z ∈ mixedPoints G ↔ dualNumbersιεOver S ≫ z = 1 ∧ dualNumbersιδOver S ≫ z = 1 :=
  Iff.rfl

/-- The map `μ : infPoints G → mixedPoints G` induced by `η ↦ εδ`. -/
noncomputable def toMixed (v : infPoints G) : mixedPoints G :=
  ⟨dualNumbersMulOver S ≫ v.1, by sorry⟩

/-- `η ↦ εδ` identifies the infinitesimal points with the points over `S[ε][δ]` trivial for
`ε = 0` and for `δ = 0`: such a point has `z^♯(a) = e^♯(a) + εδ d(a)` for a derivation `d`. -/
theorem toMixed_bijective : Function.Bijective (toMixed G) := by
  sorry

/-- The infinitesimal points are the mixed points, through `η ↦ εδ`. -/
noncomputable def mixedEquiv : infPoints G ≃ mixedPoints G :=
  Equiv.ofBijective _ (toMixed_bijective G)

/-- The point `v_ε : S[ε][δ] ⟶ G` of an infinitesimal point `v`, through the projection
forgetting `δ`. -/
noncomputable def toε (v : infPoints G) : dualNumbers₂Over S ⟶ G :=
  dualNumbersProjεOver S ≫ v.1

/-- The point `v_δ : S[ε][δ] ⟶ G` of an infinitesimal point `v`, through the projection
forgetting `ε`. -/
noncomputable def toδ (v : infPoints G) : dualNumbers₂Over S ⟶ G :=
  dualNumbersProjδOver S ≫ v.1

/-- The commutator `v_ε w_δ v_ε⁻¹ w_δ⁻¹` of two infinitesimal points reduces to the identity both
for `ε = 0` and for `δ = 0`. -/
theorem commutator_mem_mixedPoints (v w : infPoints G) :
    toε G v * toδ G w * (toε G v)⁻¹ * (toδ G w)⁻¹ ∈ mixedPoints G := by
  sorry

/-- The bracket of two infinitesimal points: the mixed term `εδ` of their group commutator
`v_ε w_δ v_ε⁻¹ w_δ⁻¹` over `S[ε][δ]`. It is the restriction to the identity of the commutator
`[ṽ, w̃]` of the left-invariant vector fields extending `v` and `w`. (blueprint: `sk-d-tangent`) -/
noncomputable def infBracket (v w : infPoints G) : infPoints G :=
  (mixedEquiv G).symm ⟨_, commutator_mem_mixedPoints G v w⟩

/-- The Lie bracket on `Lie(G)`, transported from the infinitesimal points. -/
noncomputable instance : Bracket (Lie G) (Lie G) where
  bracket x y := lieEquiv G (infBracket G ((lieEquiv G).symm x) ((lieEquiv G).symm y))

theorem lie_def (x y : Lie G) :
    ⁅x, y⁆ = lieEquiv G (infBracket G ((lieEquiv G).symm x) ((lieEquiv G).symm y)) :=
  rfl

/-- `Lie(G)` is a Lie ring: the bracket is biadditive, alternating and satisfies the Jacobi
identity, as the commutator of derivations of `𝒪_G`. (blueprint: `sk-d-tangent`) -/
noncomputable instance : LieRing (Lie G) where
  add_lie := by sorry
  lie_add := by sorry
  lie_self := by sorry
  leibniz_lie := by sorry

/-- `Lie(G)` is a Lie algebra over `Γ(S, 𝒪_S)`. (blueprint: `sk-d-tangent`) -/
noncomputable instance : LieAlgebra Γ(S, ⊤) (Lie G) where
  lie_smul := by sorry

/-! ### Functoriality -/

variable {G} {H : Over S} [GrpObj H]

theorem comp_mem_infPoints (f : G ⟶ H) [IsMonHom f] {v : dualNumbersOver S ⟶ G}
    (hv : v ∈ infPoints G) : v ≫ f ∈ infPoints H := by
  rw [mem_infPoints] at hv ⊢
  rw [← Category.assoc, hv, MonObj.one_comp]

/-- A homomorphism of group schemes `f : G ⟶ H` maps infinitesimal points to infinitesimal
points: `v ↦ v ≫ f`. -/
noncomputable def infPointsMap (f : G ⟶ H) [IsMonHom f] : infPoints G →* infPoints H :=
  ((IsMonHom.monoidHom f _).comp (infPoints G).subtype).codRestrict (infPoints H)
    fun v ↦ comp_mem_infPoints f v.2

@[simp]
theorem coe_infPointsMap_apply (f : G ⟶ H) [IsMonHom f] (v : infPoints G) :
    (infPointsMap f v : dualNumbersOver S ⟶ H) = (v : dualNumbersOver S ⟶ G) ≫ f :=
  rfl

/-- A homomorphism of group schemes preserves brackets of infinitesimal points: it preserves
group commutators and commutes with `η ↦ εδ`. -/
theorem infPointsMap_infBracket (f : G ⟶ H) [IsMonHom f] (v w : infPoints G) :
    infPointsMap f (infBracket G v w) = infBracket H (infPointsMap f v) (infPointsMap f w) := by
  sorry

/-- Let `f : G ⟶ H` be a monomorphism of group schemes, a subgroup scheme of `H`. If the
commutators of the points of `H` over `S[ε][δ]` factor through `G`, then the bracket of two
infinitesimal points of `H` comes from `G`: the commutator `v_ε w_δ v_ε⁻¹ w_δ⁻¹` is `c ≫ f` for a
point `c` of `G` over `S[ε][δ]`, which is a mixed point of `G` since `f` is a monomorphism, and
its preimage under `η ↦ εδ` is an infinitesimal point of `G` mapping to `[v, w]`.
(blueprint: `sk-i-restriction`) -/
theorem infBracket_mem_range_infPointsMap (f : G ⟶ H) [IsMonHom f] [Mono f]
    (hf : ∀ a b : dualNumbers₂Over S ⟶ H, a * b * a⁻¹ * b⁻¹ ∈ (IsMonHom.monoidHom f _).range)
    (v w : infPoints H) : infBracket H v w ∈ (infPointsMap f).range := by
  sorry

end GrpObj

end InfPoints

/-! ### Group schemes over a ring -/

section Ring

variable {R : Type u} [CommRing R]

namespace GrpObj

variable (G : Over (Spec (.of R))) [GrpObj G]

/-- The `R`-module structure on `Lie(G)` for a group scheme over `Spec R`, through
`R ≅ Γ(Spec R, 𝒪)`. -/
noncomputable instance : Module R (Lie G) :=
  Module.compHom (Lie G) (Scheme.ΓSpecIso (.of R)).inv.hom

/-- `Lie(G)` is a Lie algebra over `R`. (blueprint: `sk-d-tangent`) -/
noncomputable instance : LieAlgebra R (Lie G) where
  lie_smul := by sorry

variable {G} {H : Over (Spec (.of R))} [GrpObj H]

/-- The differential `df : Lie(G) → Lie(H)` of a homomorphism of group schemes `f : G ⟶ H` over
`R`: on infinitesimal points, `v ↦ v ≫ f`. It is a homomorphism of Lie algebras.
(blueprint: `sk-d-tangent`) -/
noncomputable def differential (f : G ⟶ H) [IsMonHom f] : Lie G →ₗ⁅R⁆ Lie H where
  toFun x := lieEquiv H (infPointsMap f ((lieEquiv G).symm x))
  map_add' := by sorry
  map_smul' := by sorry
  map_lie' := by sorry

theorem differential_apply (f : G ⟶ H) [IsMonHom f] (x : Lie G) :
    differential f x = lieEquiv H (infPointsMap f ((lieEquiv G).symm x)) :=
  rfl

theorem differential_congr {f g : G ⟶ H} [IsMonHom f] [IsMonHom g] (e : f = g) :
    differential f = differential g := by
  subst e; rfl

theorem differential_id : differential (𝟙 G) = LieHom.id := by
  sorry

theorem differential_comp {K : Over (Spec (.of R))} [GrpObj K] (f : G ⟶ H) (g : H ⟶ K)
    [IsMonHom f] [IsMonHom g] : differential (f ≫ g) = (differential g).comp (differential f) := by
  sorry

/-- The differential of a monomorphism of group schemes, for instance of a closed immersion, is
injective. -/
theorem differential_injective (f : G ⟶ H) [IsMonHom f] [Mono f] :
    Function.Injective (differential f) := by
  sorry

/-- If the commutators of the points of `H` over `Spec R[ε, δ]/(ε², δ²)` factor through the
subgroup scheme `f : G ⟶ H`, then the brackets of tangent vectors of `H` are tangent to `G`: the
bracket is the mixed term of the commutator of the points `1 + εx` and `1 + δy`.
(blueprint: `sk-i-restriction`) -/
theorem lie_mem_range_differential_of_commutator_mem (f : G ⟶ H) [IsMonHom f] [Mono f]
    (hf : ∀ a b : dualNumbers₂Over (Spec (.of R)) ⟶ H,
      a * b * a⁻¹ * b⁻¹ ∈ (IsMonHom.monoidHom f _).range)
    (x y : Lie H) : ⁅x, y⁆ ∈ (differential f).range := by
  obtain ⟨u, hu⟩ :=
    infBracket_mem_range_infPointsMap f hf ((lieEquiv H).symm x) ((lieEquiv H).symm y)
  exact (LieHom.mem_range _ _).2
    ⟨lieEquiv G u, by rw [differential_apply, Equiv.symm_apply_apply, hu, lie_def]⟩

/-- If the subgroup scheme `f : G ⟶ H` contains the commutators of `H`, then the brackets of
tangent vectors of `H` are tangent to `G`. (blueprint: `sk-i-restriction`) -/
theorem lie_mem_range_differential_of_containsCommutators (f : G ⟶ H) [IsMonHom f] [Mono f]
    [IsMonHom.ContainsCommutators f] (x y : Lie H) : ⁅x, y⁆ ∈ (differential f).range :=
  lie_mem_range_differential_of_commutator_mem f (fun a b ↦ MonoidHom.mem_range.2
    (IsMonHom.ContainsCommutators.exists_comp_eq_commutator f a b)) x y

/-- The tangent vectors of a central subgroup scheme `f : G ⟶ H` are central in `Lie(H)`: for
`x ∈ Lie(G)` and `y ∈ Lie(H)` the points `1 + εx` and `1 + δy` commute over `R[ε, δ]/(ε², δ²)`,
so the mixed term `⁅df(x), y⁆` of their commutator vanishes. (blueprint: `sk-p-comparison`) -/
theorem range_differential_le_center (f : G ⟶ H) [IsMonHom f]
    (hf : ∀ (X : Over (Spec (.of R))) (a : X ⟶ G) (b : X ⟶ H), (a ≫ f) * b = b * (a ≫ f)) :
    (differential f).range ≤ (LieAlgebra.center R (Lie H) : LieSubalgebra R (Lie H)) := by
  sorry

/-- The differential of an open immersion of group schemes `f : G ⟶ H` is bijective: every
infinitesimal point of `H` has the same underlying map as the identity section, hence factors
through the open subscheme `G`. -/
theorem differential_bijective_of_isOpenImmersion (f : G ⟶ H) [IsMonHom f]
    [IsOpenImmersion f.left] : Function.Bijective (differential f) := by
  sorry

/-- An open immersion of group schemes `G ⟶ H` identifies `Lie(G)` with `Lie(H)`. -/
noncomputable def lieEquivOfIsOpenImmersion (f : G ⟶ H) [IsMonHom f] [IsOpenImmersion f.left] :
    Lie G ≃ₗ⁅R⁆ Lie H :=
  LieEquiv.ofBijective _ (differential_bijective_of_isOpenImmersion f)

end GrpObj

/-! ### Points with values in the ring of dual numbers -/

/-- The `A`-points `X(A)` of a scheme `X` over `R`: the morphisms `Spec A ⟶ X` over `Spec R`. For a
group scheme `X` they form a group by `Hom.group`. -/
abbrev points (X : Over (Spec (.of R))) (A : Type u) [CommRing A] [Algebra R A] :=
  (Spec (.of A)).asOver (Spec (.of R)) ⟶ X

/-- The map `X(A) → X(B)` induced by an `R`-algebra homomorphism `φ : A → B`: precomposition with
`Spec φ : Spec B ⟶ Spec A`. -/
noncomputable def points.map (X : Over (Spec (.of R))) {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (x : points X A) : points X B :=
  (Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (.of R)) ≫ x

variable (G : Over (Spec (.of R))) [GrpObj G]

/-- The tangent group `T_1 G = ker(G(R[ε]) → G(R))` of a group scheme `G` over `R`: the points of
`G` with values in the ring of dual numbers that reduce to the identity modulo `ε`. Through the
isomorphism `(Spec R)[ε] ≅ Spec R[ε]` these are the infinitesimal points of `G`.
(blueprint: `sk-d-tangent`) -/
noncomputable def tangentGroup : Subgroup (points G (DualNumber R)) :=
  (pointsPrecomp G ((Spec.map (CommRingCat.ofHom (fstHom R R R).toRingHom)).asOver _)).ker

theorem mem_tangentGroup {x : points G (DualNumber R)} :
    x ∈ tangentGroup G ↔ points.map G (fstHom R R R) x = 1 :=
  MonoidHom.mem_ker

/-- The isomorphism `(Spec R)[ε] ⟶ Spec R[ε]` as a morphism over `Spec R`. -/
noncomputable def dualNumbersToSpecOver :
    dualNumbersOver (Spec (.of R)) ⟶ (Spec (.of (DualNumber R))).asOver (Spec (.of R)) :=
  Over.homMk (Scheme.dualNumbersToSpec (.of R)) (by sorry)

instance : IsIso (dualNumbersToSpecOver (R := R)) := by
  sorry

/-- The infinitesimal points of `G` are the points with values in the ring of dual numbers reducing
to the identity, through `(Spec R)[ε] ≅ Spec R[ε]`. -/
noncomputable def GrpObj.infPointsEquivTangentGroup : GrpObj.infPoints G ≃* tangentGroup G where
  toFun v := ⟨inv dualNumbersToSpecOver ≫ v.1, by sorry⟩
  invFun x := ⟨dualNumbersToSpecOver ≫ x.1, by sorry⟩
  left_inv _ := by sorry
  right_inv _ := by sorry
  map_mul' _ _ := by sorry

@[simp]
theorem GrpObj.coe_infPointsEquivTangentGroup_apply (v : GrpObj.infPoints G) :
    (GrpObj.infPointsEquivTangentGroup G v : points G (DualNumber R)) =
      inv dualNumbersToSpecOver ≫ (v : dualNumbersOver _ ⟶ G) :=
  rfl

end Ring

/-! ### Group schemes of finite type over a field -/

section Field

variable {k : Type u} [Field k]

/-- A morphism of schemes locally of finite type over an algebraically closed field `k` which is
surjective on underlying spaces is surjective on `k`-points.

Proof sketch (not formalised): the fibre of `f` over the closed point `y` is a nonempty scheme
locally of finite type over `k`; by the Nullstellensatz its closed points have residue field `k`,
and such a point is a `k`-point of `X` over `y`. -/
theorem exists_points_comp_eq_of_surjective [IsAlgClosed k] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] (f : X ⟶ Y) (hf : Function.Surjective f.left.base)
    (y : points Y k) : ∃ x : points X k, x ≫ f = y := by
  sorry

namespace GrpObj

variable (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]

/-- The Lie algebra of a group scheme of finite type over a field only sees the identity
component: the differential of the open immersion `G° ⟶ G` is bijective.
(blueprint: `sk-i-cartier`) -/
theorem differential_identityComponentι_bijective :
    Function.Bijective (differential (identityComponentι G)) :=
  differential_bijective_of_isOpenImmersion (identityComponentι G)

/-- The Lie algebra of a group scheme of finite type over a field is the Lie algebra of its
identity component. (blueprint: `sk-i-cartier`) -/
noncomputable def lieEquivIdentityComponent : Lie (identityComponent G) ≃ₗ⁅k⁆ Lie G :=
  lieEquivOfIsOpenImmersion (identityComponentι G)

/-- Cartier's theorem, Lie algebra form: over a field of characteristic zero, the Lie algebra of a
group scheme `G` of finite type has dimension the dimension of `G`.

Proof sketch (not formalised): `Lie(G)` is the tangent space at the identity; in characteristic
zero `G` is smooth (`AlgebraicGeometry.GrpObj.isReduced_of_charZero`), so this tangent space has
the dimension of `G` at the identity, which is the dimension of `G` since the connected components
of `G` are translates of `G°` after base change to the algebraic closure.
(blueprint: `sk-i-cartier`) -/
theorem finrank_lie_eq_topologicalKrullDim [CharZero k] :
    (Module.finrank k (Lie G) : WithBot ℕ∞) = topologicalKrullDim G.left := by
  sorry

end GrpObj

end Field

end AlgebraicGeometry
