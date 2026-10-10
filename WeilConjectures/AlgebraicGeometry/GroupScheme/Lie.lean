/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic.NoncommRing
public import WeilConjectures.AlgebraicGeometry.DualNumbers
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.InfinitesimalTranslation
public import WeilConjectures.AlgebraicGeometry.Modules.HomObjSections
public import WeilConjectures.AlgebraicGeometry.TangentSpace
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

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

All constructions are genuine definitions. The bridge `toLie` is a bijection: its inverse sends a
derivation `d : 𝒪_G → e_*𝒪_S` to the point `GrpObj.pointOfDerivation`, `a ↦ e^♯(a) + ε d(a)`.
The proofs that are still missing (the sheaf and local conditions of the thickening, the
bijectivity of the mixed-term map, the Lie algebra axioms, and the functoriality of the bracket)
are recorded as `sorry`. The base ring of a
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
theorem nonempty_lie_equiv_sections : Nonempty (Lie G ≃+ Γ(lieAlgebraSheaf G, ⊤)) :=
  ⟨(Scheme.Modules.ΓHomObjAddEquiv _ _).symm⟩

end GrpObj

/-! ### Infinitesimal points -/

section InfPoints

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

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
noncomputable def infPoints : Subgroup (Scheme.dualNumbersOver S ⟶ G) :=
  (pointsPrecomp G (Scheme.dualNumbersιOver S)).ker

theorem mem_infPoints {v : Scheme.dualNumbersOver S ⟶ G} :
    v ∈ infPoints G ↔ Scheme.dualNumbersιOver S ≫ v = 1 :=
  MonoidHom.mem_ker

instance : (infPoints G).Normal :=
  MonoidHom.normal_ker _

/-- The identity point, as a morphism of schemes, is the identity section. -/
theorem one_left : (1 : Over.mk (𝟙 S) ⟶ G).left = unitSection G := by
  rw [Hom.one_def, Over.comp_left, unitSection]
  have : (SemiCartesianMonoidalCategory.toUnit (Over.mk (𝟙 S))).left = 𝟙 S :=
    (Category.comp_id _).symm.trans (Over.w _)
  rw [this]
  exact Category.id_comp _

theorem ι_comp_left_eq {v : Scheme.dualNumbersOver S ⟶ G} (hv : v ∈ infPoints G) :
    S.dualNumbersι ≫ v.left = unitSection G := by
  rw [mem_infPoints] at hv
  rw [← one_left G, ← hv]
  rfl

/-! ### The bridge from infinitesimal points to the Lie algebra -/

/-- The derivation `d_v : 𝒪_G → (i ≫ v)_*𝒪_S` attached to a point `v : S[ε] ⟶ G`: the
`ε`-coefficient of `v^♯(a) = e^♯(a) + ε d_v(a)`. It is a derivation over `f⁻¹𝒪_S` because `v`
is a morphism of schemes over `S` and `ε² = 0`. -/
noncomputable def infDerivation (v : Scheme.dualNumbersOver S ⟶ G) :
    ((Scheme.Modules.pushforward (S.dualNumbersι ≫ v.left)).obj
      (Scheme.Modules.unitModule S)).val.Derivation' G.hom.pullbackPresheafHom where
  d {V} :=
    { toFun := fun a ↦ (v.left.app V.unop a).snd
      map_zero' := by rw [map_zero]; rfl
      map_add' x y := by rw [map_add]; rfl }
  d_mul {V} a b := by
    change (v.left.app V.unop (a * b)).snd =
      (v.left.app V.unop a).fst * (v.left.app V.unop b).snd +
        (v.left.app V.unop b).fst * (v.left.app V.unop a).snd
    rw [map_mul, snd_mul, smul_eq_mul, op_smul_eq_mul, mul_comm (v.left.app V.unop a).snd]
  d_map {X Y} f x := by
    have h := ConcreteCategory.congr_hom (v.left.c.naturality f) x
    exact (congr_arg snd h).trans (DualNumber.snd_mapRingHom _ _)
  d_app {X} a := by
    let ε₀ : (TopCat.Presheaf.pushforward CommRingCat v.left.base).obj
        (Scheme.dualNumbersOver S).left.presheaf ⟶
        (TopCat.Presheaf.pushforward CommRingCat v.left.base).obj
          (Scheme.dualNumbersOver S).left.presheaf :=
      Functor.whiskerLeft ((TopologicalSpace.Opens.map v.left.base).op ⋙ S.presheaf)
        (CommRingCat.dualNumberFst ≫ CommRingCat.dualNumberInl)
    have key : (G.hom.pullbackPresheafHom ≫ v.left.c) ≫ ε₀ =
        G.hom.pullbackPresheafHom ≫ v.left.c := by
      simp only [Scheme.Hom.pullbackPresheafHom, ← Adjunction.homEquiv_naturality_right_symm]
      congr 1
      ext U b
      have hb : ((v.left ≫ G.hom).app U b).snd = 0 := by
        rw [Scheme.Hom.congr_app (Over.w v) U]
        exact (DualNumber.snd_mapRingHom _ _).trans (map_zero _)
      exact TrivSqZeroExt.ext rfl hb.symm
    have h := ConcreteCategory.congr_hom (congr_app key X) a
    exact (congr_arg snd h).symm.trans rfl

/-- The morphism `(i ≫ v)^*Ω¹_{G/S} ⟶ 𝒪_S` attached to a point `v : S[ε] ⟶ G`: the derivation
`d_v` through the universal property of `Ω¹_{G/S}` and the adjunction `(i ≫ v)^* ⊣ (i ≫ v)_*`. -/
noncomputable def omegaHom (v : Scheme.dualNumbersOver S ⟶ G) :
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

/-! ### Points attached to derivations -/

omit [GrpObj G] in
/-- The morphism `g^*Ω¹_{G/S} ⟶ 𝒪_S` attached to a derivation `d : 𝒪_G → g_*𝒪_S` over `f⁻¹𝒪_S`,
for a morphism `g : S ⟶ G`: the universal property of `Ω¹_{G/S}` and the adjunction
`g^* ⊣ g_*`. -/
noncomputable def homOfDerivation (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) :
    (Scheme.Modules.pullback g).obj G.hom.cotangentSheaf ⟶ Scheme.Modules.unitModule S :=
  ((Scheme.Modules.pullbackPushforwardAdjunction _).homEquiv _ _).symm
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 _)).symm
      ((PresheafOfModules.DifferentialsConstruction.isUniversal' _).desc D))

omit [GrpObj G] in
theorem omegaHom_eq_homOfDerivation (v : Scheme.dualNumbersOver S ⟶ G) :
    omegaHom G v = homOfDerivation G _ (infDerivation G v) :=
  rfl

/-- The morphisms `ω_{G/S} ⟶ 𝒪_S` attached to derivations along two morphisms `g₁ = g₂ = e` agree
if the derivations do. -/
theorem pullbackCongr_inv_comp_homOfDerivation {g₁ g₂ : S ⟶ G.left} (h₁ : g₁ = unitSection G)
    (h₂ : g₂ = unitSection G)
    (D₁ : ((Scheme.Modules.pushforward g₁).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom)
    (D₂ : ((Scheme.Modules.pushforward g₂).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom)
    (hD : ∀ {V : (TopologicalSpace.Opens G.left)ᵒᵖ} (a : Γ(G.left, V.unop)), D₁.d a ≍ D₂.d a) :
    (Scheme.Modules.pullbackCongr h₁).inv.app G.hom.cotangentSheaf ≫ homOfDerivation G g₁ D₁ =
      (Scheme.Modules.pullbackCongr h₂).inv.app G.hom.cotangentSheaf ≫
        homOfDerivation G g₂ D₂ := by
  subst h₁ h₂
  obtain rfl : D₁ = D₂ := by
    ext V a
    exact eq_of_heq (hD a)
  rfl

omit [GrpObj G] in
/-- The components `Γ(G, U) → Γ(S, g⁻¹U)` of a derivation `d : 𝒪_G → g_*𝒪_S`. -/
def derivationApp (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (U : G.left.Opens) : Γ(G.left, U) →+ Γ(S, g ⁻¹ᵁ U) :=
  D.d (X := Opposite.op U)

omit [GrpObj G] in
theorem derivationApp_mul (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (U : G.left.Opens) (a b : Γ(G.left, U)) :
    derivationApp G g D U (a * b) =
      g.app U a * derivationApp G g D U b + g.app U b * derivationApp G g D U a :=
  D.d_mul a b

omit [GrpObj G] in
@[simp]
theorem derivationApp_one (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (U : G.left.Opens) :
    derivationApp G g D U 1 = 0 :=
  D.d_one _

omit [GrpObj G] in
theorem derivationApp_map (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) {U V : G.left.Opens} (i : V ⟶ U) (a : Γ(G.left, U)) :
    derivationApp G g D V (G.left.presheaf.map i.op a) =
      S.presheaf.map (homOfLE (g.preimage_mono i.le)).op (derivationApp G g D U a) :=
  D.d_map i.op a

omit [GrpObj G] in
/-- The ring homomorphism `Γ(G, U) → Γ(S, g⁻¹U)[ε]`, `a ↦ g^♯(a) + ε d(a)`, attached to a
derivation `d : 𝒪_G → g_*𝒪_S`. -/
noncomputable def pointOfDerivationRingHom (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (U : G.left.Opens) :
    Γ(G.left, U) →+* DualNumber Γ(S, g ⁻¹ᵁ U) where
  toFun a := inl (g.app U a) + inr (derivationApp G g D U a)
  map_one' := by
    ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [snd_mul, fst_add, fst_inl, fst_inr, add_zero, snd_add, snd_inl, snd_inr,
        zero_add, smul_eq_mul, op_smul_eq_mul, map_mul]
      rw [derivationApp_mul]
      ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

omit [GrpObj G] in
/-- The morphism of presheafed spaces `S[ε] ⟶ G`, `a ↦ g^♯(a) + ε d(a)`, attached to a derivation
`d : 𝒪_G → g_*𝒪_S`. -/
noncomputable def pointOfDerivationHom (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) :
    S.dualNumbers.toPresheafedSpace ⟶ G.left.toPresheafedSpace where
  base := g.base
  c :=
    { app U := CommRingCat.ofHom (pointOfDerivationRingHom G g D U.unop)
      naturality U V i := by
        ext a
        change pointOfDerivationRingHom G g D V.unop (G.left.presheaf.map i a) =
          DualNumber.mapRingHom (S.presheaf.map _).hom (pointOfDerivationRingHom G g D U.unop a)
        ext
        · simp only [pointOfDerivationRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
            fst_add, fst_inl, fst_inr, add_zero, DualNumber.fst_mapRingHom]
          exact ConcreteCategory.congr_hom (g.c.naturality i) a
        · simp only [pointOfDerivationRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
            snd_add, snd_inl, snd_inr, zero_add, DualNumber.snd_mapRingHom]
          exact derivationApp_map G g D i.unop a }

omit [GrpObj G] in
theorem ι_comp_pointOfDerivationHom (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) :
    S.dualNumbersι.toPshHom ≫ pointOfDerivationHom G g D = g.toPshHom := by
  refine PresheafedSpace.ext _ _ rfl ?_
  ext U a
  simp only [Functor.comp_obj, Functor.op_obj, PresheafedSpace.comp_base, eqToHom_refl,
    Functor.whiskerRight_id', TopCat.Presheaf.comp_app, TopCat.Presheaf.pushforward_obj_obj,
    TopologicalSpace.Opens.map_comp_obj, PresheafedSpace.comp_c_app, NatTrans.id_app,
    Category.comp_id, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  change (pointOfDerivationRingHom G g D U a).fst = g.app U a
  simp [pointOfDerivationRingHom]

omit [GrpObj G] in
/-- The morphism of schemes `S[ε] ⟶ G`, `a ↦ g^♯(a) + ε d(a)`, attached to a derivation
`d : 𝒪_G → g_*𝒪_S`: its stalk maps are local since their reductions modulo `ε` are those of `g`. -/
noncomputable def pointOfDerivation (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) : S.dualNumbers ⟶ G.left where
  toHom := pointOfDerivationHom G g D
  prop y := by
    have h := PresheafedSpace.stalkMap.comp S.dualNumbersι.toPshHom (pointOfDerivationHom G g D) y
    rw [PresheafedSpace.stalkMap.congr_hom _ _ (ι_comp_pointOfDerivationHom G g D),
      eqToHom_refl, Category.id_comp] at h
    have := g.prop y
    rw [h, CommRingCat.hom_comp] at this
    exact @isLocalHom_of_comp _ _ _ _ _ _ _ _ this

omit [GrpObj G] in
@[reassoc (attr := simp)]
theorem ι_comp_pointOfDerivation (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) :
    S.dualNumbersι ≫ pointOfDerivation G g D = g :=
  Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' (ι_comp_pointOfDerivationHom G g D))

omit [GrpObj G] in
/-- A derivation over `f⁻¹𝒪_S` kills the functions pulled back from `S`. -/
theorem derivationApp_app (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (U : S.Opens) (b : Γ(S, U)) :
    derivationApp G g D (G.hom ⁻¹ᵁ U) (G.hom.app U b) = 0 := by
  have h : G.hom.c = (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      G.hom.base).unit.app S.presheaf ≫
        (TopCat.Presheaf.pushforward CommRingCat.{u} G.hom.base).map G.hom.pullbackPresheafHom := by
    rw [Scheme.Hom.pullbackPresheafHom]
    exact (((TopCat.Presheaf.pullbackPushforwardAdjunction _ _).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)).symm
  have h2 := ConcreteCategory.congr_hom (congr_app h (Opposite.op U)) b
  change D.d (G.hom.c.app (Opposite.op U) b) = 0
  rw [h2]
  exact D.d_app _

omit [GrpObj G] in
/-- The point attached to a derivation along a section `g` of `G ⟶ S` is a point over `S`. -/
theorem pointOfDerivation_comp_hom (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (hg : g ≫ G.hom = 𝟙 S) :
    pointOfDerivation G g D ≫ G.hom = S.dualNumbersProj := by
  rw [Scheme.eq_dualNumbersProj_comp_of_snd_eq_zero (pointOfDerivation G g D ≫ G.hom),
    ι_comp_pointOfDerivation_assoc, hg, Category.comp_id]
  intro U b
  change (pointOfDerivationRingHom G g D _ (G.hom.app U b)).snd = 0
  simp only [pointOfDerivationRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    snd_add, snd_inl, snd_inr, zero_add]
  exact derivationApp_app G g D U b

omit [GrpObj G] in
/-- A point `v : S[ε] ⟶ G` is the point attached to its derivation `d_v` along `i ≫ v`. -/
theorem pointOfDerivation_infDerivation (v : Scheme.dualNumbersOver S ⟶ G) :
    pointOfDerivation G (S.dualNumbersι ≫ v.left) (infDerivation G v) = v.left := by
  refine Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' (PresheafedSpace.ext _ _ rfl ?_))
  ext U a
  simp only [Functor.comp_obj, Functor.op_obj, eqToHom_refl, Functor.whiskerRight_id',
    TopCat.Presheaf.comp_app, TopCat.Presheaf.pushforward_obj_obj, NatTrans.id_app,
    Category.comp_id]
  change pointOfDerivationRingHom G (S.dualNumbersι ≫ v.left) (infDerivation G v) U a =
    v.left.app U a
  ext
  · simp only [pointOfDerivationRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      fst_add, fst_inl, fst_inr, add_zero]
    rfl
  · simp only [pointOfDerivationRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      snd_add, snd_inl, snd_inr, zero_add]
    rfl

omit [GrpObj G] in
theorem pointOfDerivation_congr {g₁ g₂ : S ⟶ G.left} (h : g₁ = g₂)
    {D₁ : ((Scheme.Modules.pushforward g₁).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom}
    {D₂ : ((Scheme.Modules.pushforward g₂).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom}
    (hD : ∀ {V : (TopologicalSpace.Opens G.left)ᵒᵖ} (a : Γ(G.left, V.unop)), D₁.d a ≍ D₂.d a) :
    pointOfDerivation G g₁ D₁ = pointOfDerivation G g₂ D₂ := by
  subst h
  obtain rfl : D₁ = D₂ := by
    ext V a
    exact eq_of_heq (hD a)
  rfl

omit [GrpObj G] in
/-- A derivation `𝒪_G → g_*𝒪_S` is a morphism `g^*Ω¹_{G/S} ⟶ 𝒪_S`. -/
theorem homOfDerivation_bijective (g : S ⟶ G.left) :
    Function.Bijective (homOfDerivation G g) := by
  refine (Equiv.bijective _).comp ((Equiv.bijective _).comp ⟨fun D₁ D₂ h ↦ ?_, fun φ ↦ ?_⟩)
  · rw [← (PresheafOfModules.DifferentialsConstruction.isUniversal' _).fac D₁,
      ← (PresheafOfModules.DifferentialsConstruction.isUniversal' _).fac D₂]
    exact congrArg _ h
  · refine ⟨(PresheafOfModules.DifferentialsConstruction.derivation' _).postcomp φ, ?_⟩
    apply (PresheafOfModules.DifferentialsConstruction.isUniversal' _).postcomp_injective
    rw [PresheafOfModules.Derivation.Universal.fac]

/-- The morphisms `ω_{G/S} ⟶ 𝒪_S` attached to derivations along two morphisms `g₁ = g₂ = e` agree
only if the derivations do. -/
theorem heq_of_pullbackCongr_inv_comp_homOfDerivation_eq {g₁ g₂ : S ⟶ G.left}
    (h₁ : g₁ = unitSection G) (h₂ : g₂ = unitSection G)
    (D₁ : ((Scheme.Modules.pushforward g₁).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom)
    (D₂ : ((Scheme.Modules.pushforward g₂).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom)
    (h : (Scheme.Modules.pullbackCongr h₁).inv.app G.hom.cotangentSheaf ≫
        homOfDerivation G g₁ D₁ =
      (Scheme.Modules.pullbackCongr h₂).inv.app G.hom.cotangentSheaf ≫
        homOfDerivation G g₂ D₂) {V : (TopologicalSpace.Opens G.left)ᵒᵖ}
    (a : Γ(G.left, V.unop)) : D₁.d a ≍ D₂.d a := by
  subst h₁ h₂
  obtain rfl := (homOfDerivation_bijective G _).1 ((cancel_epi _).1 h)
  rfl

omit [GrpObj G] in
theorem eqRec_d_heq {g₁ g₂ : S ⟶ G.left} (h : g₁ = g₂)
    (D : ((Scheme.Modules.pushforward g₁).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) {V : (TopologicalSpace.Opens G.left)ᵒᵖ} (a : Γ(G.left, V.unop)) :
    (h ▸ D).d a ≍ D.d a := by
  subst h
  rfl

omit [GrpObj G] in
/-- The morphism attached to a sum of derivations is the sum of the morphisms. -/
theorem homOfDerivation_add (g : S ⟶ G.left)
    (D₁ D₂ D₃ : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom)
    (h : ∀ {V : (TopologicalSpace.Opens G.left)ᵒᵖ} (a : Γ(G.left, V.unop)),
      D₃.d a = D₁.d a + D₂.d a) :
    homOfDerivation G g D₃ = homOfDerivation G g D₁ + homOfDerivation G g D₂ := by
  have h1 : (PresheafOfModules.DifferentialsConstruction.isUniversal'
        G.hom.pullbackPresheafHom).desc D₃ =
      (PresheafOfModules.DifferentialsConstruction.isUniversal'
        G.hom.pullbackPresheafHom).desc D₁ +
      (PresheafOfModules.DifferentialsConstruction.isUniversal'
        G.hom.pullbackPresheafHom).desc D₂ := by
    apply (PresheafOfModules.DifferentialsConstruction.isUniversal'
      G.hom.pullbackPresheafHom).postcomp_injective
    rw [PresheafOfModules.Derivation.Universal.fac]
    ext X a
    have f1 := congrArg (fun D ↦ PresheafOfModules.Derivation.d D (X := X) a)
      ((PresheafOfModules.DifferentialsConstruction.isUniversal' G.hom.pullbackPresheafHom).fac D₁)
    have f2 := congrArg (fun D ↦ PresheafOfModules.Derivation.d D (X := X) a)
      ((PresheafOfModules.DifferentialsConstruction.isUniversal' G.hom.pullbackPresheafHom).fac D₂)
    simp only [PresheafOfModules.Derivation.postcomp_d_apply] at f1 f2
    rw [PresheafOfModules.Derivation.postcomp_d_apply, h, ← f1, ← f2]
    rfl
  have hS := (PresheafOfModules.sheafificationAdjunction
    (J := Opens.grothendieckTopology G.left) (𝟙 G.left.ringCatSheaf.obj)).left_adjoint_additive
  rw [homOfDerivation, homOfDerivation, homOfDerivation, h1]
  rw [← Adjunction.homAddEquiv_symm_add]
  congr 1
  have := ((PresheafOfModules.sheafificationAdjunction (J := Opens.grothendieckTopology G.left)
    (𝟙 G.left.ringCatSheaf.obj)).homAddEquiv
      (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' G.hom.pullbackPresheafHom)
      ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S))).symm.map_add
    ((PresheafOfModules.DifferentialsConstruction.isUniversal' G.hom.pullbackPresheafHom).desc D₁)
    ((PresheafOfModules.DifferentialsConstruction.isUniversal' G.hom.pullbackPresheafHom).desc D₂)
  simp only [Adjunction.homAddEquiv_symm_apply, PresheafOfModules.sheafificationAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv] at this
  exact this


/-- The bridge is a bijection: a morphism `ω_{G/S} ⟶ 𝒪_S` is a derivation `d : 𝒪_G → e_*𝒪_S`, and
`a ↦ e^♯(a) + ε d(a)` is a morphism of schemes `S[ε] ⟶ G` over `S` reducing to the identity, since
its stalk maps are local, their reductions modulo `ε` being the local maps `e^♯`. -/
theorem toLie_bijective : Function.Bijective (toLie G) := by
  refine ⟨fun v w h ↦ ?_, fun φ ↦ ?_⟩
  · apply Subtype.ext
    apply Over.OverMorphism.ext
    rw [← pointOfDerivation_infDerivation G v.1, ← pointOfDerivation_infDerivation G w.1]
    exact pointOfDerivation_congr G
      ((ι_comp_left_eq G v.2).trans (ι_comp_left_eq G w.2).symm)
      (heq_of_pullbackCongr_inv_comp_homOfDerivation_eq G _ _ _ _ h)
  · obtain ⟨D, hD⟩ := (homOfDerivation_bijective G (unitSection G)).2
      ((Scheme.Modules.pullbackCongr (rfl : unitSection G = unitSection G)).hom.app
        G.hom.cotangentSheaf ≫ φ)
    let v : Scheme.dualNumbersOver S ⟶ G := Over.homMk (pointOfDerivation G (unitSection G) D)
      (pointOfDerivation_comp_hom G _ D (unitSection_comp_hom G))
    have hv : v ∈ infPoints G := by
      rw [mem_infPoints]
      apply Over.OverMorphism.ext
      exact (ι_comp_pointOfDerivation G _ D).trans (one_left G).symm
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [toLie, omegaHom_eq_homOfDerivation, pullbackCongr_inv_comp_homOfDerivation G
      (ι_comp_left_eq G hv) rfl _ D (fun a ↦ heq_of_eq (zero_add _)), hD,
      Iso.inv_hom_id_app_assoc]

/-- The infinitesimal points of `G` are its Lie algebra. (blueprint: `sk-d-tangent`) -/
noncomputable def lieEquiv : infPoints G ≃ Lie G :=
  Equiv.ofBijective _ (toLie_bijective G)

/-- The derivation `d_v` of an infinitesimal point, transported to the identity section. -/
noncomputable def infDerivationAtUnit (v : infPoints G) :
    ((Scheme.Modules.pushforward (unitSection G)).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom :=
  (ι_comp_left_eq G v.2) ▸ infDerivation G v.1

theorem toLie_eq_homOfDerivation (v : infPoints G) :
    toLie G v = (Scheme.Modules.pullbackCongr (rfl : unitSection G = unitSection G)).inv.app
      G.hom.cotangentSheaf ≫ homOfDerivation G (unitSection G) (infDerivationAtUnit G v) :=
  pullbackCongr_inv_comp_homOfDerivation G (ι_comp_left_eq G v.2) rfl _ _
    (fun a ↦ (eqRec_d_heq G _ _ a).symm)

theorem infDerivationAtUnit_d (v : infPoints G) {V : (TopologicalSpace.Opens G.left)ᵒᵖ}
    (a : Γ(G.left, V.unop)) :
    (infDerivationAtUnit G v).d a = (unitSection G).app V.unop
      (rightTranslationDeriv ((mem_infPoints G).1 v.2) V.unop a) := by
  have hv := ι_comp_left_eq G v.2
  have hW : v.1.left ⁻¹ᵁ V.unop = (unitSection G) ⁻¹ᵁ V.unop := by
    rw [← hv]
    rfl
  refine eq_of_heq ((eqRec_d_heq G _ _ a).trans ?_)
  change (v.1.left.app V.unop a).snd ≍ _
  rw [Scheme.Hom.app_eq_appLE, snd_appLE_eq ((mem_infPoints G).1 v.2) V.unop _ le_rfl hW.le]
  exact Scheme.Hom.appLE_heq_app η[G].left V.unop hW hW.le
    (rightTranslationDeriv ((mem_infPoints G).1 v.2) V.unop a)


/-- The bridge turns the group law of the infinitesimal points into the addition of `Lie(G)`: the
operator `D_{vw}` of the right translation by `vw` is `D_v + D_w`, and `d_v = e^♯ ∘ D_v`. -/
theorem lieEquiv_mul (v w : infPoints G) : lieEquiv G (v * w) = lieEquiv G v + lieEquiv G w := by
  change toLie G (v * w) = toLie G v + toLie G w
  rw [toLie_eq_homOfDerivation, toLie_eq_homOfDerivation, toLie_eq_homOfDerivation,
    ← Preadditive.comp_add, homOfDerivation_add G _ _ _ _ (fun a ↦ ?_)]
  rw [infDerivationAtUnit_d, infDerivationAtUnit_d, infDerivationAtUnit_d]
  rename_i V
  have hD : rightTranslationDeriv ((mem_infPoints G).1 (v * w).2) V.unop a =
      rightTranslationDeriv ((mem_infPoints G).1 v.2) V.unop a +
        rightTranslationDeriv ((mem_infPoints G).1 w.2) V.unop a := by
    rw [rightTranslationDeriv_mul ((mem_infPoints G).1 v.2) ((mem_infPoints G).1 w.2)]
    rfl
  rw [hD]
  exact map_add _ _ _

theorem lieEquiv_one : lieEquiv G 1 = 0 := by
  have := lieEquiv_mul G 1 1
  rw [mul_one] at this
  exact left_eq_add.1 this

/-- The infinitesimal points form a commutative group: their group law is the addition of tangent
vectors. -/
theorem isMulCommutative_infPoints : IsMulCommutative (infPoints G) :=
  ⟨⟨fun v w ↦ (lieEquiv G).injective (by rw [lieEquiv_mul, lieEquiv_mul, add_comm])⟩⟩

/-- An infinitesimal point is determined by the operator `D_v` of its right translation. -/
theorem eq_of_rightTranslationDeriv_eq {v w : infPoints G}
    (h : ∀ U, rightTranslationDeriv ((mem_infPoints G).1 v.2) U =
      rightTranslationDeriv ((mem_infPoints G).1 w.2) U) : v = w := by
  have hW (u : infPoints G) (U : G.left.Opens) : u.1.left ⁻¹ᵁ U = (unitSection G) ⁻¹ᵁ U := by
    rw [← ι_comp_left_eq G u.2]
    rfl
  have hb (u : infPoints G) : u.1.left.base = (unitSection G).base := by
    rw [← ι_comp_left_eq G u.2]
    rfl
  refine Subtype.ext (Over.OverMorphism.ext (Scheme.Hom.ext_appLE ((hb v).trans (hb w).symm)
    fun U V e₁ e₂ ↦ ?_))
  ext a
  refine TrivSqZeroExt.ext ?_ ?_
  · exact (fst_appLE_eq ((mem_infPoints G).1 v.2) U V e₁ (e₁.trans (hW v U).le) a).trans
      (fst_appLE_eq ((mem_infPoints G).1 w.2) U V e₂ (e₁.trans (hW v U).le) a).symm
  · rw [snd_appLE_eq ((mem_infPoints G).1 v.2) U V e₁ (e₁.trans (hW v U).le) a,
      snd_appLE_eq ((mem_infPoints G).1 w.2) U V e₂ (e₁.trans (hW v U).le) a, h U]


theorem lieEquiv_symm_add (x y : Lie G) :
    (lieEquiv G).symm (x + y) = (lieEquiv G).symm x * (lieEquiv G).symm y :=
  (lieEquiv G).injective (by simp [lieEquiv_mul])

/-! ### Rescaling infinitesimal points -/

omit [GrpObj G] in
/-- Multiplying the morphism attached to a derivation by a global function `r` multiplies the
derivation by `r`. -/
theorem homOfDerivation_comp_unitSmul (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (r : Γ(S, ⊤)) :
    homOfDerivation G g D ≫ Scheme.Modules.unitSmul r = homOfDerivation G g
      (D.postcomp ((Scheme.Modules.pushforward g).map (Scheme.Modules.unitSmul r)).val) := by
  rw [homOfDerivation, homOfDerivation, ← Adjunction.homEquiv_naturality_right_symm,
    ← PresheafOfModules.Derivation.Universal.desc_comp]
  exact congrArg _ (PresheafOfModules.sheafificationHomEquiv_symm_comp _ _ _).symm

theorem dualNumbersScaleOver_comp_mem_infPoints (r : Γ(S, ⊤))
    {v : Scheme.dualNumbersOver S ⟶ G} (hv : v ∈ infPoints G) :
    Scheme.dualNumbersScaleOver S r ≫ v ∈ infPoints G := by
  rw [mem_infPoints] at hv ⊢
  rw [Scheme.dualNumbersιOver_comp_scaleOver_assoc, hv]

/-- The rescaling `v ↦ v(rε)` of an infinitesimal point by a global function `r`. It is the
multiplication by `r` on the Lie algebra (`toLie_infPointsScale`). -/
noncomputable def infPointsScale (r : Γ(S, ⊤)) (v : infPoints G) : infPoints G :=
  ⟨Scheme.dualNumbersScaleOver S r ≫ v.1, dualNumbersScaleOver_comp_mem_infPoints G r v.2⟩

theorem toLie_infPointsScale (r : Γ(S, ⊤)) (v : infPoints G) :
    toLie G (infPointsScale G r v) = r • toLie G v := by
  rw [Scheme.Modules.homUnit_smul_def, toLie, toLie, Category.assoc, omegaHom_eq_homOfDerivation,
    omegaHom_eq_homOfDerivation, homOfDerivation_comp_unitSmul]
  refine pullbackCongr_inv_comp_homOfDerivation G _ _ _ _ fun {V} a ↦ heq_of_eq ?_
  rw [PresheafOfModules.Derivation.postcomp_d_apply]
  change (DualNumber.scale _ (v.1.left.app V.unop a)).snd =
    (v.1.left.app V.unop a).snd * S.presheaf.map (homOfLE le_top).op r
  rw [DualNumber.snd_scale, mul_comm]
  rfl

theorem lieEquiv_symm_smul (r : Γ(S, ⊤)) (x : Lie G) :
    (lieEquiv G).symm (r • x) = infPointsScale G r ((lieEquiv G).symm x) := by
  rw [Equiv.symm_apply_eq]
  change _ = toLie G _
  rw [toLie_infPointsScale]
  exact congrArg (r • ·) ((lieEquiv G).apply_symm_apply x).symm

/-! ### The bracket as the mixed term of the commutator -/

/-- The points of `G` over `S[ε][δ]` reducing to the identity both for `ε = 0` and for `δ = 0`. -/
noncomputable def mixedPoints : Subgroup (Scheme.dualNumbers₂Over S ⟶ G) :=
  (pointsPrecomp G (Scheme.dualNumbersιεOver S)).ker ⊓
    (pointsPrecomp G (Scheme.dualNumbersιδOver S)).ker

theorem mem_mixedPoints {z : Scheme.dualNumbers₂Over S ⟶ G} :
    z ∈ mixedPoints G ↔ Scheme.dualNumbersιεOver S ≫ z = 1 ∧ Scheme.dualNumbersιδOver S ≫ z = 1 :=
  Iff.rfl

/-- The map `μ : infPoints G → mixedPoints G` induced by `η ↦ εδ`. -/
noncomputable def toMixed (v : infPoints G) : mixedPoints G :=
  ⟨Scheme.dualNumbersMulOver S ≫ v.1, by
    have hv := (mem_infPoints G).1 v.2
    rw [mem_mixedPoints, Scheme.dualNumbersιεOver_comp_dualNumbersMulOver_assoc,
      Scheme.dualNumbersιδOver_comp_dualNumbersMulOver_assoc, hv, MonObj.comp_one]
    exact ⟨rfl, rfl⟩⟩

@[simp]
theorem coe_toMixed (v : infPoints G) :
    (toMixed G v : Scheme.dualNumbers₂Over S ⟶ G) = Scheme.dualNumbersMulOver S ≫ v.1 :=
  rfl

theorem dualNumbersι_comp_mixedPoints_left (z : mixedPoints G) :
    S.dualNumbers.dualNumbersι ≫ z.1.left = S.dualNumbersProj ≫ η[G].left := by
  have := congrArg CommaMorphism.left ((mem_mixedPoints G).1 z.2).1
  simpa [Hom.one_def, Over.toUnit_left, Scheme.dualNumbersιεOver] using this

theorem dualNumbers_dualNumbersι_comp_mixedPoints_left (z : mixedPoints G) :
    S.dualNumbersι.dualNumbers ≫ z.1.left = S.dualNumbersProj ≫ η[G].left := by
  have := congrArg CommaMorphism.left ((mem_mixedPoints G).1 z.2).2
  simpa [Hom.one_def, Over.toUnit_left, Scheme.dualNumbersιδOver] using this

theorem fst_snd_mixedPoints_app (z : mixedPoints G) (V : G.left.Opens) (a : Γ(G.left, V)) :
    (z.1.left.app V a).fst.snd = 0 := by
  have hz := dualNumbersι_comp_mixedPoints_left G z
  have hW : (S.dualNumbersProj ≫ η[G].left) ⁻¹ᵁ V = z.1.left ⁻¹ᵁ V := by
    rw [← hz]
    rfl
  have h := Scheme.Hom.appLE_apply_eq_of_eq hz V (z.1.left ⁻¹ᵁ V) le_rfl hW.ge a
  have h1 := Scheme.Hom.appLE_comp_apply S.dualNumbers.dualNumbersι z.1.left V (z.1.left ⁻¹ᵁ V)
    (z.1.left ⁻¹ᵁ V) le_rfl le_rfl le_rfl a
  have h2 := Scheme.Hom.appLE_comp_apply S.dualNumbersProj η[G].left V (z.1.left ⁻¹ᵁ V)
    (z.1.left ⁻¹ᵁ V) hW.ge le_rfl hW.ge a
  have h3 := h1.symm.trans (h.trans h2)
  rw [Scheme.dualNumbersι_appLE_self (X := S.dualNumbers)] at h3
  rw [← Scheme.Hom.appLE_eq_app]
  exact (congrArg TrivSqZeroExt.snd h3).trans ((congrArg TrivSqZeroExt.snd
    (Scheme.dualNumbersProj_appLE_self _ _ _)).trans (TrivSqZeroExt.snd_inl _ _))

theorem snd_fst_mixedPoints_app (z : mixedPoints G) (V : G.left.Opens) (a : Γ(G.left, V)) :
    (z.1.left.app V a).snd.fst = 0 := by
  have hz := dualNumbers_dualNumbersι_comp_mixedPoints_left G z
  have hW : (S.dualNumbersProj ≫ η[G].left) ⁻¹ᵁ V = z.1.left ⁻¹ᵁ V := by
    rw [← hz]
    rfl
  have h := Scheme.Hom.appLE_apply_eq_of_eq hz V (z.1.left ⁻¹ᵁ V) le_rfl hW.ge a
  have h1 := Scheme.Hom.appLE_comp_apply S.dualNumbersι.dualNumbers z.1.left V (z.1.left ⁻¹ᵁ V)
    (z.1.left ⁻¹ᵁ V) le_rfl le_rfl le_rfl a
  have h2 := Scheme.Hom.appLE_comp_apply S.dualNumbersProj η[G].left V (z.1.left ⁻¹ᵁ V)
    (z.1.left ⁻¹ᵁ V) hW.ge le_rfl hW.ge a
  have h3 := congrArg TrivSqZeroExt.snd (h1.symm.trans (h.trans h2))
  rw [Scheme.Hom.dualNumbers_appLE, DualNumber.snd_mapRingHom,
    Scheme.dualNumbersι_appLE_self] at h3
  rw [← Scheme.Hom.appLE_eq_app]
  exact h3.trans ((congrArg TrivSqZeroExt.snd
    (Scheme.dualNumbersProj_appLE_self _ _ _)).trans (TrivSqZeroExt.snd_inl _ _))

/-- The `εδ`-coefficient `d_z` of a point `z : S[ε][δ] ⟶ G` with no `ε`- and no `δ`-part:
`z^♯(a) = e^♯(a) + εδ d_z(a)`; it is a derivation `𝒪_G → e_*𝒪_S` over `f⁻¹𝒪_S`. -/
noncomputable def mixedDerivation (z : mixedPoints G) :
    ((Scheme.Modules.pushforward (S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ z.1.left)).obj
      (Scheme.Modules.unitModule S)).val.Derivation' G.hom.pullbackPresheafHom where
  d {V} :=
    { toFun := fun a ↦ (z.1.left.app V.unop a).snd.snd
      map_zero' := by rw [map_zero]; rfl
      map_add' x y := by rw [map_add]; rfl }
  d_mul {V} a b := by
    change (z.1.left.app V.unop (a * b)).snd.snd =
      (z.1.left.app V.unop a).fst.fst * (z.1.left.app V.unop b).snd.snd +
        (z.1.left.app V.unop b).fst.fst * (z.1.left.app V.unop a).snd.snd
    let φ : Γ(G.left, V.unop) →+* DualNumber (DualNumber Γ(S, z.1.left ⁻¹ᵁ V.unop)) :=
      (z.1.left.app V.unop).hom
    change (φ (a * b)).snd.snd = (φ a).fst.fst * (φ b).snd.snd + (φ b).fst.fst * (φ a).snd.snd
    have h1 (c : Γ(G.left, V.unop)) : (φ c).fst.snd = 0 := fst_snd_mixedPoints_app G z V.unop c
    have h2 (c : Γ(G.left, V.unop)) : (φ c).snd.fst = 0 := snd_fst_mixedPoints_app G z V.unop c
    rw [map_mul]
    simp only [snd_mul, smul_eq_mul, op_smul_eq_mul, snd_add, h1, h2, mul_zero, add_zero,
      zero_add]
    ring
  d_map {X Y} f x := by
    have h := ConcreteCategory.congr_hom (z.1.left.c.naturality f) x
    exact (congr_arg (fun y ↦ TrivSqZeroExt.snd (TrivSqZeroExt.snd y)) h).trans
      ((congrArg TrivSqZeroExt.snd (DualNumber.snd_mapRingHom _ _)).trans
        (DualNumber.snd_mapRingHom _ _))
  d_app {X} a := by
    let ε₀ : (TopCat.Presheaf.pushforward CommRingCat z.1.left.base).obj
        (Scheme.dualNumbers₂Over S).left.presheaf ⟶
        (TopCat.Presheaf.pushforward CommRingCat z.1.left.base).obj
          (Scheme.dualNumbers₂Over S).left.presheaf :=
      Functor.whiskerLeft ((TopologicalSpace.Opens.map z.1.left.base).op ⋙ S.dualNumbers.presheaf)
        (CommRingCat.dualNumberFst ≫ CommRingCat.dualNumberInl)
    have key : (G.hom.pullbackPresheafHom ≫ z.1.left.c) ≫ ε₀ =
        G.hom.pullbackPresheafHom ≫ z.1.left.c := by
      simp only [Scheme.Hom.pullbackPresheafHom, ← Adjunction.homEquiv_naturality_right_symm]
      congr 1
      ext U b
      have hb : ((z.1.left ≫ G.hom).app U b).snd = 0 := by
        rw [Scheme.Hom.congr_app (Over.w z.1) U]
        exact (DualNumber.snd_mapRingHom _ _).trans (map_zero _)
      exact TrivSqZeroExt.ext rfl hb.symm
    have h := ConcreteCategory.congr_hom (congr_app key X) a
    exact (congr_arg (fun y ↦ TrivSqZeroExt.snd (TrivSqZeroExt.snd y)) h).symm.trans rfl


theorem toMixed_surjective : Function.Surjective (toMixed G) := by
  intro z
  let g := S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ z.1.left
  have hg : g = unitSection G := by
    simp only [g, dualNumbersι_comp_mixedPoints_left, Scheme.dualNumbersι_comp_proj_assoc]
    rfl
  have hgS : g ≫ G.hom = 𝟙 S := hg ▸ unitSection_comp_hom G
  let v : Scheme.dualNumbersOver S ⟶ G := Over.homMk (pointOfDerivation G g (mixedDerivation G z))
    (pointOfDerivation_comp_hom G g _ hgS)
  have hv : v ∈ infPoints G := by
    rw [mem_infPoints]
    apply Over.OverMorphism.ext
    exact (ι_comp_pointOfDerivation G _ _).trans (hg.trans (one_left G).symm)
  refine ⟨⟨v, hv⟩, Subtype.ext (Over.OverMorphism.ext ?_)⟩
  refine Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' (PresheafedSpace.ext _ _ rfl ?_))
  ext U a
  simp only [Functor.comp_obj, Functor.op_obj, eqToHom_refl, Functor.whiskerRight_id',
    TopCat.Presheaf.comp_app, TopCat.Presheaf.pushforward_obj_obj, NatTrans.id_app,
    Category.comp_id]
  change DualNumber.mulRingHom (pointOfDerivationRingHom G g (mixedDerivation G z) U a) =
    z.1.left.app U a
  refine TrivSqZeroExt.ext (TrivSqZeroExt.ext ?_ ?_) (TrivSqZeroExt.ext ?_ ?_)
  · simp only [DualNumber.fst_mulRingHom, fst_inl, pointOfDerivationRingHom, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, fst_add, fst_inr, add_zero]
    rfl
  · simp only [DualNumber.fst_mulRingHom, snd_inl]
    exact (fst_snd_mixedPoints_app G z U a).symm
  · simp only [DualNumber.snd_mulRingHom, fst_inr]
    exact (snd_fst_mixedPoints_app G z U a).symm
  · simp only [DualNumber.snd_mulRingHom, snd_inr, pointOfDerivationRingHom, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, snd_add, snd_inl, snd_inr, zero_add]
    rfl


theorem toMixed_injective : Function.Injective (toMixed G) := by
  intro v w h
  have h' : Scheme.dualNumbersMulOver S ≫ v.1 = Scheme.dualNumbersMulOver S ≫ w.1 :=
    congrArg Subtype.val h
  have hv := (mem_infPoints G).1 v.2
  have hw := (mem_infPoints G).1 w.2
  have hιμ : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫
      Scheme.dualNumbersMulOver S = Scheme.dualNumbersιOver S := by
    rw [Scheme.dualNumbersιεOver_comp_dualNumbersMulOver, ← Category.assoc]
    congr 1
  have hz : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫
      (Scheme.dualNumbersMulOver S ≫ v.1) = 1 := by
    rw [reassoc_of% hιμ, hv]
  have hz' : Scheme.dualNumbersιOver S ≫ Scheme.dualNumbersιεOver S ≫
      (Scheme.dualNumbersMulOver S ≫ w.1) = 1 := by
    rw [reassoc_of% hιμ, hw]
  refine eq_of_rightTranslationDeriv_eq G fun U ↦ ?_
  have hT : rightTranslationOp₂ hz U = rightTranslationOp₂ hz' U :=
    Scheme.Hom.dualNumbers₂Op_congr _ _ (by rw [h']) U
  rw [rightTranslationOp₂_mul_over hv, rightTranslationOp₂_mul_over hw] at hT
  simpa using congrArg (fun y : DualNumber (DualNumber (AddMonoid.End Γ(G.left, U))) ↦
    y.snd.snd) hT


/-- `η ↦ εδ` identifies the infinitesimal points with the points over `S[ε][δ]` trivial for
`ε = 0` and for `δ = 0`: such a point has `z^♯(a) = e^♯(a) + εδ d(a)` for a derivation `d`. -/
theorem toMixed_bijective : Function.Bijective (toMixed G) :=
  ⟨toMixed_injective G, toMixed_surjective G⟩

/-- The infinitesimal points are the mixed points, through `η ↦ εδ`. -/
noncomputable def mixedEquiv : infPoints G ≃ mixedPoints G :=
  Equiv.ofBijective _ (toMixed_bijective G)

/-- The point `v_ε : S[ε][δ] ⟶ G` of an infinitesimal point `v`, through the projection
forgetting `δ`. -/
noncomputable def toε (v : infPoints G) : Scheme.dualNumbers₂Over S ⟶ G :=
  Scheme.dualNumbersProjεOver S ≫ v.1

/-- The point `v_δ : S[ε][δ] ⟶ G` of an infinitesimal point `v`, through the projection
forgetting `ε`. -/
noncomputable def toδ (v : infPoints G) : Scheme.dualNumbers₂Over S ⟶ G :=
  Scheme.dualNumbersProjδOver S ≫ v.1

/-- The commutator `v_ε w_δ v_ε⁻¹ w_δ⁻¹` of two infinitesimal points reduces to the identity both
for `ε = 0` and for `δ = 0`. -/
theorem commutator_mem_mixedPoints (v w : infPoints G) :
    toε G v * toδ G w * (toε G v)⁻¹ * (toδ G w)⁻¹ ∈ mixedPoints G := by
  have hv := (mem_infPoints G).1 v.2
  have hw := (mem_infPoints G).1 w.2
  rw [mem_mixedPoints]
  simp only [MonObj.comp_mul, GrpObj.comp_inv, toε, toδ]
  refine ⟨?_, ?_⟩
  · rw [Scheme.dualNumbersιεOver_comp_dualNumbersProjεOver_assoc,
      Scheme.dualNumbersιεOver_comp_dualNumbersProjδOver_assoc, hw, MonObj.comp_one]
    group
  · rw [Scheme.dualNumbersιδOver_comp_dualNumbersProjεOver_assoc,
      Scheme.dualNumbersιδOver_comp_dualNumbersProjδOver_assoc, hv, MonObj.comp_one]
    group

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

theorem toMixed_infBracket (v w : infPoints G) :
    (toMixed G (infBracket G v w) : Scheme.dualNumbers₂Over S ⟶ G) =
      toε G v * toδ G w * (toε G v)⁻¹ * (toδ G w)⁻¹ :=
  congrArg Subtype.val ((mixedEquiv G).apply_symm_apply ⟨_, commutator_mem_mixedPoints G v w⟩)

/-! ### The Lie algebra structure through left-invariant operators -/

/-- The left-invariant operators of the tangent vectors: `x ↦ D_x` on all sections of `𝒪_G`.
It is injective and turns brackets into commutators. -/
noncomputable def lieOp (x : Lie G) : ∀ U : G.left.Opens, AddMonoid.End Γ(G.left, U) :=
  fun U ↦ rightTranslationDeriv ((mem_infPoints G).1 ((lieEquiv G).symm x).2) U

theorem lieOp_injective : Function.Injective (lieOp G) := fun _ _ h ↦
  (lieEquiv G).symm.injective (eq_of_rightTranslationDeriv_eq G fun U ↦ congrFun h U)

theorem lieOp_add (x y : Lie G) : lieOp G (x + y) = lieOp G x + lieOp G y := by
  funext U
  rw [lieOp, rightTranslationDeriv_congr _ ((mem_infPoints G).1
    ((lieEquiv G).symm x * (lieEquiv G).symm y).2) (congrArg Subtype.val (lieEquiv_symm_add G x y)),
    rightTranslationDeriv_mul ((mem_infPoints G).1 ((lieEquiv G).symm x).2)
      ((mem_infPoints G).1 ((lieEquiv G).symm y).2)]
  rfl

theorem lieOp_lie (x y : Lie G) :
    lieOp G ⁅x, y⁆ = lieOp G x * lieOp G y - lieOp G y * lieOp G x := by
  funext U
  set v := (lieEquiv G).symm x
  set w := (lieEquiv G).symm y
  have hu : (lieEquiv G).symm ⁅x, y⁆ = infBracket G v w := by
    rw [lie_def, Equiv.symm_apply_apply]
  have hμ : Scheme.dualNumbersMulOver S ≫ (infBracket G v w).1 =
      toε G v * toδ G w * (toε G v)⁻¹ * (toδ G w)⁻¹ := by
    have := (mixedEquiv G).apply_symm_apply ⟨_, commutator_mem_mixedPoints G v w⟩
    exact congrArg Subtype.val this
  rw [lieOp, rightTranslationDeriv_congr _ ((mem_infPoints G).1 (infBracket G v w).2)
    (congrArg Subtype.val hu)]
  exact rightTranslationDeriv_eq_of_mul_eq_commutator _ _ _ hμ U


theorem lieOp_zero : lieOp G 0 = 0 := by
  have := lieOp_add G 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

/-- Multiplication by the pullback of a global function `r` of the base, on all sections of
`𝒪_G`. -/
noncomputable def mulOp (r : Γ(S, ⊤)) : ∀ U : G.left.Opens, AddMonoid.End Γ(G.left, U) :=
  fun U ↦ AddMonoidHom.mulLeft (G.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (G.hom.appTop r))

theorem lieOp_smul (r : Γ(S, ⊤)) (y : Lie G) : lieOp G (r • y) = mulOp G r * lieOp G y := by
  funext U
  ext b
  rw [lieOp, rightTranslationDeriv_congr _ ((mem_infPoints G).1
    (infPointsScale G r ((lieEquiv G).symm y)).2)
    (congrArg Subtype.val (lieEquiv_symm_smul G r y)),
    rightTranslationDeriv_scale ((mem_infPoints G).1 ((lieEquiv G).symm y).2)]
  rfl

theorem lieOp_mul_mulOp (x : Lie G) (r : Γ(S, ⊤)) :
    lieOp G x * mulOp G r = mulOp G r * lieOp G x := by
  funext U
  ext b
  exact rightTranslationDeriv_appLE_mul ((mem_infPoints G).1 ((lieEquiv G).symm x).2) U ⊤
    le_top r b

/-- `Lie(G)` is a Lie ring: the bracket is biadditive, alternating and satisfies the Jacobi
identity, as the commutator of derivations of `𝒪_G`. (blueprint: `sk-d-tangent`) -/
noncomputable instance : LieRing (Lie G) where
  add_lie x y z := by
    apply lieOp_injective
    simp only [lieOp_lie, lieOp_add]
    noncomm_ring
  lie_add x y z := by
    apply lieOp_injective
    simp only [lieOp_lie, lieOp_add]
    noncomm_ring
  lie_self x := by
    apply lieOp_injective
    rw [lieOp_lie, lieOp_zero, sub_self]
  leibniz_lie x y z := by
    apply lieOp_injective
    simp only [lieOp_lie, lieOp_add]
    noncomm_ring

/-- `Lie(G)` is a Lie algebra over `Γ(S, 𝒪_S)`. (blueprint: `sk-d-tangent`) -/
noncomputable instance : LieAlgebra Γ(S, ⊤) (Lie G) where
  lie_smul r x y := by
    apply lieOp_injective
    rw [lieOp_lie, lieOp_smul, lieOp_smul, lieOp_lie, ← mul_assoc, lieOp_mul_mulOp, mul_assoc,
      mul_assoc, mul_sub]

/-! ### Functoriality -/

variable {G} {H : Over S} [GrpObj H]

theorem comp_mem_infPoints (f : G ⟶ H) [IsMonHom f] {v : Scheme.dualNumbersOver S ⟶ G}
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
    (infPointsMap f v : Scheme.dualNumbersOver S ⟶ H) = (v : Scheme.dualNumbersOver S ⟶ G) ≫ f :=
  rfl

/-- A homomorphism of group schemes preserves brackets of infinitesimal points: it preserves
group commutators and commutes with `η ↦ εδ`. -/
theorem infPointsMap_infBracket (f : G ⟶ H) [IsMonHom f] (v w : infPoints G) :
    infPointsMap f (infBracket G v w) = infBracket H (infPointsMap f v) (infPointsMap f w) := by
  apply toMixed_injective H
  apply Subtype.ext
  rw [toMixed_infBracket, coe_toMixed, coe_infPointsMap_apply, ← Category.assoc, ← coe_toMixed,
    toMixed_infBracket]
  simp only [MonObj.mul_comp, GrpObj.inv_comp, toε, toδ, coe_infPointsMap_apply, Category.assoc]


/-- Let `f : G ⟶ H` be a monomorphism of group schemes, a subgroup scheme of `H`. If the
commutators of the points of `H` over `S[ε][δ]` factor through `G`, then the bracket of two
infinitesimal points of `H` comes from `G`: the commutator `v_ε w_δ v_ε⁻¹ w_δ⁻¹` is `c ≫ f` for a
point `c` of `G` over `S[ε][δ]`, which is a mixed point of `G` since `f` is a monomorphism, and
its preimage under `η ↦ εδ` is an infinitesimal point of `G` mapping to `[v, w]`.
(blueprint: `sk-i-restriction`) -/
theorem infBracket_mem_range_infPointsMap (f : G ⟶ H) [IsMonHom f] [Mono f]
    (hf : ∀ a b : Scheme.dualNumbers₂Over S ⟶ H, a * b * a⁻¹ * b⁻¹ ∈ (IsMonHom.monoidHom f _).range)
    (v w : infPoints H) : infBracket H v w ∈ (infPointsMap f).range := by
  obtain ⟨c, hc⟩ := hf (toε H v) (toδ H w)
  change c ≫ f = _ at hc
  have hc' : c ∈ mixedPoints G := by
    have h := commutator_mem_mixedPoints H v w
    rw [mem_mixedPoints] at h ⊢
    rw [← hc, ← MonObj.one_comp (X := Scheme.dualNumbersOver S) f] at h
    exact ⟨(cancel_mono f).1 ((Category.assoc _ _ _).trans h.1),
      (cancel_mono f).1 ((Category.assoc _ _ _).trans h.2)⟩
  refine ⟨(mixedEquiv G).symm ⟨c, hc'⟩, ?_⟩
  apply toMixed_injective H
  apply Subtype.ext
  rw [toMixed_infBracket, coe_toMixed, coe_infPointsMap_apply, ← Category.assoc, ← coe_toMixed]
  change ((mixedEquiv G) ((mixedEquiv G).symm ⟨c, hc'⟩)).1 ≫ f = _
  rw [Equiv.apply_symm_apply]
  exact hc


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
  lie_smul c x y := lie_smul ((Scheme.ΓSpecIso (.of R)).inv.hom c) x y

variable {G} {H : Over (Spec (.of R))} [GrpObj H]

theorem infPointsMap_id : infPointsMap (𝟙 G) = MonoidHom.id _ := by
  ext v
  exact Category.comp_id _

theorem infPointsMap_comp {K : Over (Spec (.of R))} [GrpObj K] (f : G ⟶ H) (g : H ⟶ K)
    [IsMonHom f] [IsMonHom g] : infPointsMap (f ≫ g) = (infPointsMap g).comp (infPointsMap f) := by
  ext v
  exact (Category.assoc _ _ _).symm

/-- The differential `df : Lie(G) → Lie(H)` of a homomorphism of group schemes `f : G ⟶ H` over
`R`: on infinitesimal points, `v ↦ v ≫ f`. It is a homomorphism of Lie algebras.
(blueprint: `sk-d-tangent`) -/
noncomputable def differential (f : G ⟶ H) [IsMonHom f] : Lie G →ₗ⁅R⁆ Lie H where
  toFun x := lieEquiv H (infPointsMap f ((lieEquiv G).symm x))
  map_add' x y := by
    simp only [lieEquiv_symm_add, map_mul, lieEquiv_mul]
  map_smul' c x := by
    change _ = c • lieEquiv H _
    rw [show c • x = (Scheme.ΓSpecIso (.of R)).inv.hom c • x from rfl, lieEquiv_symm_smul,
      show infPointsMap f (infPointsScale G _ ((lieEquiv G).symm x)) =
        infPointsScale H _ (infPointsMap f ((lieEquiv G).symm x)) from
          Subtype.ext ((coe_infPointsMap_apply _ _).trans (Category.assoc _ _ _))]
    exact toLie_infPointsScale H _ _
  map_lie' {x y} := by
    simp only [lie_def, Equiv.symm_apply_apply, infPointsMap_infBracket]

theorem differential_apply (f : G ⟶ H) [IsMonHom f] (x : Lie G) :
    differential f x = lieEquiv H (infPointsMap f ((lieEquiv G).symm x)) :=
  rfl

theorem differential_congr {f g : G ⟶ H} [IsMonHom f] [IsMonHom g] (e : f = g) :
    differential f = differential g := by
  subst e; rfl

theorem differential_id : differential (𝟙 G) = LieHom.id := by
  ext x
  rw [differential_apply, infPointsMap_id, MonoidHom.id_apply, Equiv.apply_symm_apply]
  rfl

theorem differential_comp {K : Over (Spec (.of R))} [GrpObj K] (f : G ⟶ H) (g : H ⟶ K)
    [IsMonHom f] [IsMonHom g] : differential (f ≫ g) = (differential g).comp (differential f) := by
  ext x
  rw [LieHom.comp_apply, differential_apply, differential_apply, differential_apply,
    Equiv.symm_apply_apply, infPointsMap_comp, MonoidHom.comp_apply]

theorem infPointsMap_injective (f : G ⟶ H) [IsMonHom f] [Mono f] :
    Function.Injective (infPointsMap f) := fun _ _ h ↦
  Subtype.ext ((cancel_mono f).1 (congrArg Subtype.val h))

/-- The differential of a monomorphism of group schemes, for instance of a closed immersion, is
injective. -/
theorem differential_injective (f : G ⟶ H) [IsMonHom f] [Mono f] :
    Function.Injective (differential f) := by
  intro x y h
  rw [differential_apply, differential_apply] at h
  exact (lieEquiv G).symm.injective (infPointsMap_injective f ((lieEquiv H).injective h))

/-- If the commutators of the points of `H` over `Spec R[ε, δ]/(ε², δ²)` factor through the
subgroup scheme `f : G ⟶ H`, then the brackets of tangent vectors of `H` are tangent to `G`: the
bracket is the mixed term of the commutator of the points `1 + εx` and `1 + δy`.
(blueprint: `sk-i-restriction`) -/
theorem lie_mem_range_differential_of_commutator_mem (f : G ⟶ H) [IsMonHom f] [Mono f]
    (hf : ∀ a b : Scheme.dualNumbers₂Over (Spec (.of R)) ⟶ H,
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
  rintro _ ⟨x, rfl⟩
  change differential f x ∈ LieModule.maxTrivSubmodule R (Lie H) (Lie H)
  rw [LieModule.mem_maxTrivSubmodule]
  intro y
  rw [lie_def, differential_apply, Equiv.symm_apply_apply]
  set u := infPointsMap f ((lieEquiv G).symm x)
  set w := (lieEquiv H).symm y
  have h1 : infBracket H w u = 1 := by
    apply toMixed_injective H
    apply Subtype.ext
    rw [toMixed_infBracket]
    have hc := hf _ (Scheme.dualNumbersProjδOver _ ≫ ((lieEquiv G).symm x).1) (toε H w)
    have hb : toδ H u = (Scheme.dualNumbersProjδOver _ ≫ ((lieEquiv G).symm x).1) ≫ f :=
      (Category.assoc _ _ _).symm
    rw [hb, ← hc]
    simp only [coe_toMixed, OneMemClass.coe_one, MonObj.comp_one]
    group
  rw [h1, lieEquiv_one]

/-- The differential of an open immersion of group schemes `f : G ⟶ H` is bijective: every
infinitesimal point of `H` has the same underlying map as the identity section, hence factors
through the open subscheme `G`. -/
theorem differential_bijective_of_isOpenImmersion (f : G ⟶ H) [IsMonHom f]
    [IsOpenImmersion f.left] : Function.Bijective (differential f) := by
  have : Mono f := Over.mono_of_mono_left f
  refine ⟨differential_injective f, fun y ↦ ?_⟩
  suffices h : Function.Surjective (infPointsMap f) by
    obtain ⟨u, hu⟩ := h ((lieEquiv H).symm y)
    exact ⟨lieEquiv G u, by rw [differential_apply, Equiv.symm_apply_apply, hu,
      Equiv.apply_symm_apply]⟩
  intro v
  have he : unitSection G ≫ f.left = unitSection H := by
    exact congrArg CommaMorphism.left (IsMonHom.one_hom (f := f))
  have hrange : Set.range v.1.left.base ⊆ Set.range f.left.base := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(unitSection G).base x, ?_⟩
    have h1 := ι_comp_left_eq H v.2
    rw [← he] at h1
    exact (congrArg (fun φ : Spec (.of R) ⟶ H.left ↦ φ.base x) h1).symm
  let u' : (Scheme.dualNumbersOver (Spec (.of R))).left ⟶ G.left :=
    IsOpenImmersion.lift f.left v.1.left hrange
  have hu' : u' ≫ f.left = v.1.left := IsOpenImmersion.lift_fac _ _ _
  let u : Scheme.dualNumbersOver (Spec (.of R)) ⟶ G := Over.homMk u' (by
    rw [← Over.w f, ← Category.assoc, hu']
    exact Over.w v.1)
  have hu : u ∈ infPoints G := by
    rw [mem_infPoints]
    apply (cancel_mono f).1
    rw [Category.assoc, MonObj.one_comp]
    have : u ≫ f = v.1 := Over.OverMorphism.ext hu'
    rw [this]
    exact (mem_infPoints H).1 v.2
  exact ⟨⟨u, hu⟩, Subtype.ext (Over.OverMorphism.ext hu')⟩

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
    Scheme.dualNumbersOver (Spec (.of R)) ⟶ (Spec (.of (DualNumber R))).asOver (Spec (.of R)) :=
  Over.homMk (Scheme.dualNumbersToSpec (.of R)) (Scheme.dualNumbersToSpec_comp_specMap (.of R))

instance : IsIso (dualNumbersToSpecOver (R := R)) := by
  have : IsIso ((Over.forget _).map (dualNumbersToSpecOver (R := R))) :=
    Scheme.isIso_dualNumbersToSpec (.of R)
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The point `ε ↦ 0` of `Spec R[ε]` is the closed immersion `i : S ⟶ S[ε]` through
`(Spec R)[ε] ≅ Spec R[ε]`. -/
theorem specMap_fstHom_asOver_eq :
    (Spec.map (CommRingCat.ofHom (fstHom R R R).toRingHom)).asOver (Spec (.of R)) =
      CartesianMonoidalCategory.toUnit _ ≫ Scheme.dualNumbersιOver (Spec (.of R)) ≫
        dualNumbersToSpecOver := by
  ext1
  simp [dualNumbersToSpecOver, Scheme.ι_comp_dualNumbersToSpec, Over.toUnit_left,
    specOverSpec_over]
  rfl

/-- An infinitesimal point gives a point of the tangent group through `(Spec R)[ε] ≅ Spec R[ε]`. -/
theorem GrpObj.inv_dualNumbersToSpecOver_comp_mem_tangentGroup
    {v : Scheme.dualNumbersOver (Spec (.of R)) ⟶ G} (hv : v ∈ GrpObj.infPoints G) :
    inv dualNumbersToSpecOver ≫ v ∈ tangentGroup G := by
  rw [mem_tangentGroup, points.map, specMap_fstHom_asOver_eq]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [(GrpObj.mem_infPoints G).1 hv, MonObj.comp_one]

/-- A point of the tangent group gives an infinitesimal point through `(Spec R)[ε] ≅ Spec R[ε]`. -/
theorem GrpObj.dualNumbersToSpecOver_comp_mem_infPoints {x : points G (DualNumber R)}
    (hx : x ∈ tangentGroup G) :
    dualNumbersToSpecOver ≫ x ∈ GrpObj.infPoints G := by
  rw [mem_tangentGroup, points.map, specMap_fstHom_asOver_eq] at hx
  let s : Over.mk (𝟙 (Spec (.of R))) ⟶ (Spec (.of R)).asOver (Spec (.of R)) :=
    Over.homMk (𝟙 _) (by simp [specOverSpec_over])
  have e : s ≫ CartesianMonoidalCategory.toUnit _ = 𝟙 _ :=
    CartesianMonoidalCategory.toUnit_unique _ _
  simp only [Category.assoc] at hx
  have h := congrArg (s ≫ ·) hx
  simp only [MonObj.comp_one] at h
  rw [← Category.assoc s, e, Category.id_comp] at h
  exact (GrpObj.mem_infPoints G).2 h

/-- The infinitesimal points of `G` are the points with values in the ring of dual numbers reducing
to the identity, through `(Spec R)[ε] ≅ Spec R[ε]`. -/
noncomputable def GrpObj.infPointsEquivTangentGroup : GrpObj.infPoints G ≃* tangentGroup G where
  toFun v :=
    ⟨inv dualNumbersToSpecOver ≫ v.1, GrpObj.inv_dualNumbersToSpecOver_comp_mem_tangentGroup G v.2⟩
  invFun x := ⟨dualNumbersToSpecOver ≫ x.1, GrpObj.dualNumbersToSpecOver_comp_mem_infPoints G x.2⟩
  left_inv v := Subtype.ext (IsIso.hom_inv_id_assoc dualNumbersToSpecOver v.1)
  right_inv x := Subtype.ext (IsIso.inv_hom_id_assoc dualNumbersToSpecOver x.1)
  map_mul' _ _ := Subtype.ext (MonObj.comp_mul _ _ _)

@[simp]
theorem GrpObj.coe_infPointsEquivTangentGroup_apply (v : GrpObj.infPoints G) :
    (GrpObj.infPointsEquivTangentGroup G v : points G (DualNumber R)) =
      inv dualNumbersToSpecOver ≫ (v : Scheme.dualNumbersOver _ ⟶ G) :=
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
