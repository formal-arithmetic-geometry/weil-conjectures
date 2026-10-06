/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Normal
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.Topology.JacobsonSpace
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Geometry of group schemes over a field

Let `G` be a group scheme over a field `k`: a group object in `Over (Spec k)`. This file states
the basic facts about the underlying scheme of `G` used for algebraic groups: left translation by a
rational point is an automorphism of `G`; a group scheme of finite type has finitely many connected
components and its identity component `G°` is open; the image of a homomorphism of group schemes of
finite type is closed; and a closed subgroup of a connected reduced group of the same dimension is
the whole group.

## Main definitions

- `AlgebraicGeometry.GrpObj.onePoint`: the identity point of `G`, the image of the unit section.
- `AlgebraicGeometry.GrpObj.mulLeft`: left translation by a rational point `g` of `G`.
- `AlgebraicGeometry.GrpObj.identityComponentOpens`: the identity component `G°`, as an open
  subset of `G`.
- `AlgebraicGeometry.GrpObj.identityComponent`: the identity component `G°` as an open subgroup
  scheme of `G`, with its inclusion `AlgebraicGeometry.GrpObj.identityComponentι : G° ⟶ G`, a
  normal monomorphism of group objects.

## Main results

- `AlgebraicGeometry.GrpObj.irreducibleSpace_identityComponent`: `G°` is irreducible.
- `AlgebraicGeometry.GrpObj.finiteIndex_range_identityComponentι`: `G°(k)` has finite index in
  `G(k)`.
- `AlgebraicGeometry.GrpObj.image_mulLeft_connectedComponent_onePoint`: the connected components
  of `G` are the translates of `G°` by rational points.
- `AlgebraicGeometry.finite_connectedComponents`: a group scheme of finite type over `k` has
  finitely many connected components.
- `AlgebraicGeometry.GrpObj.isReduced_of_charZero`: Cartier's theorem, a group scheme locally of
  finite type over a field of characteristic zero is reduced.
- `AlgebraicGeometry.isClosed_range_of_isMonHom`: the image of a homomorphism from a group scheme
  of finite type to a group scheme locally of finite type over `k` is closed.
- `AlgebraicGeometry.irreducibleSpace_of_connectedSpace`: a connected group scheme locally of
  finite type over `k` is irreducible.
- `AlgebraicGeometry.isIso_left_of_topologicalKrullDim_eq`: a closed subgroup of a connected reduced
  group of the same dimension is the whole group.

## Blueprint

- `sk-p-geometry`: the identity component, images of homomorphisms and the dimension criterion.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The identity point of a group scheme `G` over a field `k`: the image of the unique point of
`Spec k` under the unit section. (blueprint: `sk-p-geometry`) -/
noncomputable def GrpObj.onePoint (G : Over (Spec (.of k))) [GrpObj G] : G.left :=
  η[G].left.base (show Spec (.of k) from ⟨⊥, Ideal.isPrime_bot⟩)

/-- Left translation `x ↦ g * x` on a group scheme `G` over `k` by a rational point `g` of `G`.
(blueprint: `sk-p-geometry`) -/
noncomputable def GrpObj.mulLeft (G : Over (Spec (.of k))) [GrpObj G]
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G ⟶ G :=
  lift (toUnit G ≫ g) (𝟙 G) ≫ μ[G]

/-- Left translation by a rational point is an automorphism of the underlying scheme.
(blueprint: `sk-p-geometry`) -/
theorem GrpObj.isIso_mulLeft_left (G : Over (Spec (.of k))) [GrpObj G]
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : IsIso (GrpObj.mulLeft G g).left := by
  have hmul (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : GrpObj.mulLeft G g = (toUnit G ≫ g) * 𝟙 G :=
    rfl
  have hcomp (g h : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
      GrpObj.mulLeft G g ≫ GrpObj.mulLeft G h = GrpObj.mulLeft G (h * g) := by
    rw [hmul, hmul, hmul, MonObj.comp_mul, ← Category.assoc, toUnit_unique (_ ≫ toUnit G),
      Category.comp_id, ← mul_assoc, MonObj.comp_mul]
  have hone : GrpObj.mulLeft G 1 = 𝟙 G := by
    rw [hmul, MonObj.comp_one, one_mul]
  have : IsIso (GrpObj.mulLeft G g) :=
    ⟨GrpObj.mulLeft G g⁻¹, by rw [hcomp, inv_mul_cancel, hone],
      by rw [hcomp, mul_inv_cancel, hone]⟩
  exact inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulLeft G g)))

/-- The underlying scheme of a group scheme of finite type over a field is noetherian. -/
theorem isNoetherian_left (G : Over (Spec (.of k))) [LocallyOfFiniteType G.hom]
    [QuasiCompact G.hom] : IsNoetherian G.left :=
  have := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have := QuasiCompact.compactSpace_of_compactSpace G.hom
  {}

/-- A group scheme of finite type over a field has finitely many connected components.
(blueprint: `sk-p-geometry`) -/
theorem finite_connectedComponents (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    Finite (_root_.ConnectedComponents G.left) :=
  have := isNoetherian_left G
  inferInstance

/-- The connected component of the identity of a group scheme of finite type over a field is open.
(blueprint: `sk-p-geometry`) -/
theorem isOpen_connectedComponent_onePoint (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    IsOpen (connectedComponent (GrpObj.onePoint G)) :=
  have := isNoetherian_left G
  TopologicalSpace.NoetherianSpace.isOpen_connectedComponent _

/-- The identity component `G°` of a group scheme `G` of finite type over a field, as an open
subset of `G`: the connected component of the identity point. (blueprint: `sk-p-geometry`) -/
noncomputable def GrpObj.identityComponentOpens (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] : G.left.Opens :=
  ⟨connectedComponent (GrpObj.onePoint G), isOpen_connectedComponent_onePoint G⟩

section IdentityComponent

variable (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]

/-- The identity component `G°` of a group scheme `G` of finite type over a field, as a scheme
over `k`: the open subscheme of `G` on the connected component of the identity point.
(blueprint: `sk-p-geometry`) -/
noncomputable abbrev GrpObj.identityComponent : Over (Spec (.of k)) :=
  Over.mk ((GrpObj.identityComponentOpens G).ι ≫ G.hom)

/-- The open immersion `G° ⟶ G` of the identity component into `G`, as a morphism over `k`.
(blueprint: `sk-p-geometry`) -/
noncomputable def GrpObj.identityComponentι : GrpObj.identityComponent G ⟶ G :=
  Over.homMk (GrpObj.identityComponentOpens G).ι

instance : IsOpenImmersion (GrpObj.identityComponentι G).left :=
  inferInstanceAs (IsOpenImmersion (GrpObj.identityComponentOpens G).ι)

instance : Mono (GrpObj.identityComponentι G) :=
  Over.mono_of_mono_left _

/-- The image of `G° ⟶ G` is the connected component of the identity point. -/
theorem GrpObj.range_identityComponentι :
    Set.range (GrpObj.identityComponentι G).left.base =
      connectedComponent (GrpObj.onePoint G) :=
  Scheme.Opens.range_ι _

/-- A morphism `X ⟶ G` over `k` whose image lies in the connected component of the identity
factors (uniquely, as `G° ⟶ G` is a monomorphism) through the open subscheme `G°`. -/
noncomputable def GrpObj.identityComponentLift {X : Over (Spec (.of k))} (f : X ⟶ G)
    (hf : Set.range f.left.base ⊆ connectedComponent (GrpObj.onePoint G)) :
    X ⟶ GrpObj.identityComponent G :=
  Over.homMk (IsOpenImmersion.lift (GrpObj.identityComponentOpens G).ι f.left
      (hf.trans (Scheme.Opens.range_ι (GrpObj.identityComponentOpens G)).symm.subset))
    ((IsOpenImmersion.lift_fac_assoc (GrpObj.identityComponentOpens G).ι f.left _ _).trans
      (Over.w f))

@[reassoc (attr := simp)]
theorem GrpObj.identityComponentLift_comp_identityComponentι {X : Over (Spec (.of k))}
    (f : X ⟶ G) (hf : Set.range f.left.base ⊆ connectedComponent (GrpObj.onePoint G)) :
    GrpObj.identityComponentLift G f hf ≫ GrpObj.identityComponentι G = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (GrpObj.identityComponentOpens G).ι f.left _

omit [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] in
/-- The unit section of `G` lands in the identity component. -/
theorem GrpObj.range_one_subset_connectedComponent :
    Set.range η[G].left.base ⊆ connectedComponent (GrpObj.onePoint G) := by
  rintro _ ⟨x, rfl⟩
  obtain rfl : x = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) :=
    Subsingleton.elim (α := PrimeSpectrum k) _ _
  exact mem_connectedComponent

/-- Multiplication `G° × G° ⟶ G` lands in the identity component: the product of two connected
schemes with rational points is connected, and its image contains the identity.
(blueprint: `sk-p-geometry`) -/
theorem GrpObj.range_mul_subset_connectedComponent :
    Set.range ((GrpObj.identityComponentι G ⊗ₘ GrpObj.identityComponentι G) ≫ μ[G]).left.base ⊆
      connectedComponent (GrpObj.onePoint G) := by
  sorry

/-- Inversion maps the identity component into itself. (blueprint: `sk-p-geometry`) -/
theorem GrpObj.range_inv_subset_connectedComponent :
    Set.range (GrpObj.identityComponentι G ≫ ι[G]).left.base ⊆
      connectedComponent (GrpObj.onePoint G) := by
  sorry

/-- Conjugation `G × G° ⟶ G`, `(g, h) ↦ g * h * g⁻¹`, lands in the identity component: each
fibre `g G° g⁻¹` is connected and contains the identity. (blueprint: `sk-p-geometry`) -/
theorem GrpObj.range_conj_subset_connectedComponent :
    Set.range ((G ◁ GrpObj.identityComponentι G) ≫ GrpObj.conj G).left.base ⊆
      connectedComponent (GrpObj.onePoint G) := by
  sorry

/-- The identity component `G°` is an open subgroup scheme of `G`: the unit, multiplication and
inversion of `G` restrict to `G°`, and the group axioms follow from those of `G` since `G° ⟶ G`
is a monomorphism. (blueprint: `sk-p-geometry`) -/
noncomputable instance : GrpObj (GrpObj.identityComponent G) where
  one := GrpObj.identityComponentLift G η[G] (GrpObj.range_one_subset_connectedComponent G)
  mul := GrpObj.identityComponentLift G
    ((GrpObj.identityComponentι G ⊗ₘ GrpObj.identityComponentι G) ≫ μ[G])
    (GrpObj.range_mul_subset_connectedComponent G)
  inv := GrpObj.identityComponentLift G (GrpObj.identityComponentι G ≫ ι[G])
    (GrpObj.range_inv_subset_connectedComponent G)
  one_mul := by
    rw [← cancel_mono (GrpObj.identityComponentι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, leftUnitor_hom,
      toUnit_unique _ (toUnit _), ← Hom.one_def]
  mul_one := by
    rw [← cancel_mono (GrpObj.identityComponentι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, rightUnitor_hom,
      toUnit_unique _ (toUnit _), ← Hom.one_def]
  mul_assoc := by
    rw [← cancel_mono (GrpObj.identityComponentι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, mul_assoc]
  left_inv := by
    rw [← cancel_mono (GrpObj.identityComponentι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, ← Hom.inv_def, ← Hom.one_def]
  right_inv := by
    rw [← cancel_mono (GrpObj.identityComponentι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, ← Hom.inv_def, ← Hom.one_def]

/-- The inclusion `G° ⟶ G` of the identity component is a homomorphism of group schemes. -/
instance : IsMonHom (GrpObj.identityComponentι G) where
  one_hom := GrpObj.identityComponentLift_comp_identityComponentι G _ _
  mul_hom := GrpObj.identityComponentLift_comp_identityComponentι G _ _

/-- The identity component `G°` is a normal subgroup scheme of `G`: the conjugation morphism
`G × G° ⟶ G` factors through `G° ⟶ G`. (blueprint: `sk-p-geometry`) -/
instance : IsMonHom.Normal (GrpObj.identityComponentι G) where
  exists_comp_eq_conj :=
    ⟨GrpObj.identityComponentLift G _ (GrpObj.range_conj_subset_connectedComponent G),
      GrpObj.identityComponentLift_comp_identityComponentι G _ _⟩

/-- The identity component `G°` of a group scheme of finite type over a field is irreducible.
(blueprint: `sk-p-geometry`) -/
theorem GrpObj.irreducibleSpace_identityComponent :
    IrreducibleSpace (GrpObj.identityComponent G).left := by
  sorry

/-- The rational points of the identity component `G°` have finite index in the rational points
of `G`. (blueprint: `sk-p-geometry`) -/
theorem GrpObj.finiteIndex_range_identityComponentι :
    (IsMonHom.monoidHom (GrpObj.identityComponentι G)
      (𝟙_ (Over (Spec (.of k))))).range.FiniteIndex := by
  sorry

omit [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] in
/-- The connected components of a group scheme `G` of finite type over a field are the translates
of the identity component: left translation by a rational point `g` maps `G°` onto the connected
component of the point `g * 1 = g`. (blueprint: `sk-p-geometry`) -/
theorem GrpObj.image_mulLeft_connectedComponent_onePoint (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (GrpObj.mulLeft G g).left.base '' connectedComponent (GrpObj.onePoint G) =
      connectedComponent ((GrpObj.mulLeft G g).left.base (GrpObj.onePoint G)) := by
  have := GrpObj.isIso_mulLeft_left G g
  simpa [connectedComponentIn_univ] using
    (GrpObj.mulLeft G g).left.homeomorph.image_connectedComponentIn
      (Set.mem_univ (GrpObj.onePoint G))

end IdentityComponent

/-- Cartier's theorem: a group scheme locally of finite type over a field of characteristic zero
is reduced (indeed smooth). (blueprint: `sk-i-cartier`) -/
theorem GrpObj.isReduced_of_charZero [CharZero k] (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] : IsReduced G.left := by
  sorry

/-- The image of a homomorphism from a group scheme of finite type to a group scheme locally of
finite type over a field is closed (SGA 3, VI_B, Proposition 1.2).

The source must be quasi-compact: the homomorphism `ℤ ⟶ 𝔾ₐ` from the constant group scheme,
`n ↦ n`, over `ℚ` has image the infinite non-closed set of closed points `n ∈ 𝔸¹_ℚ`.

Proof sketch (not formalized): after base change to an algebraic closure the image is
constructible (Chevalley), hence contains a dense open subset of its closure; translating it by
rational points shows the image is open in its closure, hence closed. Closedness descends along
the closed surjection from the base change. The matrix-group case over an algebraically closed
field is `AlgebraicGeometry.GeneralLinearGroup.RationalHom.mem_range_points_iff` (blueprint
`lem-ag-homomorphism-image-closed`). (blueprint: `sk-p-geometry`) -/
theorem isClosed_range_of_isMonHom {G K : Over (Spec (.of k))} [GrpObj G] [GrpObj K]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [LocallyOfFiniteType K.hom] (f : G ⟶ K)
    [IsMonHom f] :
    IsClosed (Set.range f.left.base) := by
  sorry

section AlgClosed

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field `K`, the `K`-rational point of a group scheme `G` locally of
finite type through a closed point `x`, as a section `𝟙_ ⟶ G`. -/
noncomputable def GrpObj.sectionOfIsClosed (G : Over (Spec (.of K))) [LocallyOfFiniteType G.hom]
    (x : G.left) (hx : IsClosed {x}) : 𝟙_ (Over (Spec (.of K))) ⟶ G :=
  Over.homMk (pointOfClosedPoint G.hom x hx) (pointOfClosedPoint_comp G.hom x hx)

theorem GrpObj.sectionOfIsClosed_left_apply (G : Over (Spec (.of K))) [LocallyOfFiniteType G.hom]
    (x : G.left) (hx : IsClosed {x}) (a : Spec (.of K)) :
    (GrpObj.sectionOfIsClosed G x hx).left a = x :=
  pointOfClosedPoint_apply G.hom x hx a

/-- Over an algebraically closed field, the left translations of a group scheme locally of finite
type act transitively on its closed points. -/
theorem GrpObj.exists_homeomorph_apply_eq (G : Over (Spec (.of K))) [GrpObj G]
    [LocallyOfFiniteType G.hom] {x y : G.left} (hx : IsClosed {x}) (hy : IsClosed {y}) :
    ∃ φ : G.left ≃ₜ G.left, φ x = y := by
  set sx := GrpObj.sectionOfIsClosed G x hx
  set sy := GrpObj.sectionOfIsClosed G y hy
  have := GrpObj.isIso_mulLeft_left G (sy * sx⁻¹)
  refine ⟨(GrpObj.mulLeft G (sy * sx⁻¹)).left.homeomorph, ?_⟩
  have hcomp : sx ≫ GrpObj.mulLeft G (sy * sx⁻¹) = sy := by
    change sx ≫ ((toUnit G ≫ (sy * sx⁻¹)) * 𝟙 G) = sy
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (sx ≫ toUnit G) (𝟙 _),
      Category.id_comp, Category.comp_id, inv_mul_cancel_right]
  obtain ⟨a⟩ : Nonempty (Spec (.of K)) := inferInstance
  rw [Scheme.Hom.homeomorph_apply, ← GrpObj.sectionOfIsClosed_left_apply G x hx a,
    ← Scheme.Hom.comp_apply, ← Over.comp_left, hcomp, GrpObj.sectionOfIsClosed_left_apply]

/-- **A connected group scheme over an algebraically closed field is irreducible.** Some closed
point lies in a single irreducible component; the translations act transitively on the closed
points, so every closed point, hence every point, lies in a single irreducible component. Each
point then has an irreducible open neighbourhood, and a connected space with this property is
irreducible. -/
theorem irreducibleSpace_of_connectedSpace_of_isAlgClosed (G : Over (Spec (.of K))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [ConnectedSpace G.left] : IrreducibleSpace G.left := by
  have := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  let P (x : G.left) : Prop := ∀ Z₁ ∈ irreducibleComponents G.left,
    ∀ Z₂ ∈ irreducibleComponents G.left, x ∈ Z₁ → x ∈ Z₂ → Z₁ = Z₂
  -- some closed point lies in a single irreducible component
  have hA : ∃ p ∈ closedPoints G.left, P p := by
    obtain ⟨x₀⟩ := ‹ConnectedSpace G.left›.toNonempty
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
    have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : TopologicalSpace.NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
    have : Nonempty V := ⟨⟨x₀, hxV⟩⟩
    obtain ⟨U, hU, hUne, hUuniq⟩ :=
      TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_forall_eq (α := V)
    have hU' : IsOpen (((↑) : V → G.left) '' U) := V.2.isOpenMap_subtype_val U hU
    obtain ⟨p, ⟨⟨p, hpV⟩, hpU, rfl⟩, hp⟩ :=
      nonempty_inter_closedPoints (hUne.image _) hU'.isLocallyClosed
    refine ⟨_, hp, fun Z₁ hZ₁ Z₂ hZ₂ h₁ h₂ ↦ ?_⟩
    have hV' := V.2.isOpenEmbedding_subtypeVal
    have key := hUuniq ⟨p, hpV⟩ hpU _ (preimage_mem_irreducibleComponents hZ₁ hV'
      ⟨p, h₁, ⟨p, hpV⟩, rfl⟩) _ (preimage_mem_irreducibleComponents hZ₂ hV'
      ⟨p, h₂, ⟨p, hpV⟩, rfl⟩) h₁ h₂
    have hcl (Z : Set G.left) (hZ : Z ∈ irreducibleComponents G.left) (hp : p ∈ Z) :
        Z = closure (Z ∩ V) := by
      refine (subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2 V.2 ⟨p, hp, hpV⟩).antisymm
        (closure_minimal Set.inter_subset_left (isClosed_of_mem_irreducibleComponents Z hZ))
    have hZV : Z₁ ∩ V = Z₂ ∩ V := Set.ext fun y ↦
      ⟨fun ⟨hy, hyV⟩ ↦ ⟨(Set.ext_iff.1 key ⟨y, hyV⟩).1 hy, hyV⟩,
        fun ⟨hy, hyV⟩ ↦ ⟨(Set.ext_iff.1 key ⟨y, hyV⟩).2 hy, hyV⟩⟩
    calc Z₁ = closure (Z₁ ∩ V) := hcl Z₁ hZ₁ h₁
      _ = closure (Z₂ ∩ V) := by rw [hZV]
      _ = Z₂ := (hcl Z₂ hZ₂ h₂).symm
  -- every closed point lies in a single irreducible component
  have hB (q : G.left) (hq : q ∈ closedPoints G.left) : P q := by
    obtain ⟨p, hp, hP⟩ := hA
    obtain ⟨φ, hφ⟩ := GrpObj.exists_homeomorph_apply_eq G hq hp
    intro Z₁ hZ₁ Z₂ hZ₂ h₁ h₂
    exact φ.injective.image_injective (hP _ (φ.image_mem_irreducibleComponents hZ₁) _
      (φ.image_mem_irreducibleComponents hZ₂) ⟨q, h₁, hφ⟩ ⟨q, h₂, hφ⟩)
  -- every point lies in a single irreducible component
  have hC (x : G.left) : P x := by
    obtain ⟨q, hqx, hq⟩ := nonempty_inter_closedPoints (Z := closure {x})
      ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    intro Z₁ hZ₁ Z₂ hZ₂ h₁ h₂
    exact hB q hq Z₁ hZ₁ Z₂ hZ₂
      (closure_minimal (Set.singleton_subset_iff.2 h₁) (isClosed_of_mem_irreducibleComponents _ hZ₁)
        hqx)
      (closure_minimal (Set.singleton_subset_iff.2 h₂) (isClosed_of_mem_irreducibleComponents _ hZ₂)
        hqx)
  refine irreducibleSpace_of_forall_exists_isPreirreducible fun x ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hVN : TopologicalSpace.NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
  have hV' := V.2.isOpenEmbedding_subtypeVal
  obtain ⟨U, hU, hxU, hUirr⟩ :=
    @TopologicalSpace.NoetherianSpace.exists_isOpen_isPreirreducible V _ hVN (⟨x, hxV⟩ : V)
      fun W₁ hW₁ W₂ hW₂ hx₁ hx₂ ↦ by
        have hW (W : Set V) (hW : W ∈ irreducibleComponents V) (hxW : ⟨x, hxV⟩ ∈ W) :
            ∃ Z ∈ irreducibleComponents G.left, x ∈ Z ∧ W = ((↑) : V → G.left) ⁻¹' Z := by
          obtain ⟨Z, hZ, hWZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
            (hW.1.image _ continuous_subtype_val.continuousOn).closure
          have hsub : W ⊆ ((↑) : V → G.left) ⁻¹' Z := fun w hw ↦ hWZ (subset_closure ⟨w, hw, rfl⟩)
          have hxZ : x ∈ Z := hsub hxW
          have hpre := preimage_mem_irreducibleComponents hZ hV' ⟨x, hxZ, ⟨x, hxV⟩, rfl⟩
          exact ⟨Z, hZ, hxZ, hsub.antisymm (hW.2 hpre.1 hsub)⟩
        obtain ⟨Z₁, hZ₁, hxZ₁, rfl⟩ := hW W₁ hW₁ hx₁
        obtain ⟨Z₂, hZ₂, hxZ₂, rfl⟩ := hW W₂ hW₂ hx₂
        rw [hC x Z₁ hZ₁ Z₂ hZ₂ hxZ₁ hxZ₂]
  exact ⟨((↑) : V → G.left) '' U, V.2.isOpenMap_subtype_val U hU, ⟨_, hxU, rfl⟩,
    hUirr.image _ continuous_subtype_val.continuousOn⟩

end AlgClosed

/-- A connected group scheme locally of finite type over a field is irreducible (SGA 3, VI_A,
Proposition 2.4).

Having the rational point `e`, the connected scheme `G` is geometrically connected
(`GeometricallyConnected.of_connectedSpace_of_section`), so its base change to an algebraic
closure is connected, hence irreducible (`irreducibleSpace_of_connectedSpace_of_isAlgClosed`);
`G` is the image of this base change. (blueprint: `sk-p-geometry`) -/
theorem irreducibleSpace_of_connectedSpace (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [ConnectedSpace G.left] : IrreducibleSpace G.left := by
  let g : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  let : GrpObj (Over.mk (Limits.pullback.snd G.hom g)) := Over.grpObjMkPullbackSnd
  have hG : GeometricallyConnected G.hom :=
    GeometricallyConnected.of_connectedSpace_of_section G.hom η[G].left (by simp)
  have : ConnectedSpace (Over.mk (Limits.pullback.snd G.hom g)).left :=
    hG.geometrically_connectedSpace g _ _ (IsPullback.of_hasPullback G.hom g)
  have : LocallyOfFiniteType (Over.mk (Limits.pullback.snd G.hom g)).hom :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd G.hom g))
  have : IrreducibleSpace ↥(Limits.pullback G.hom g) :=
    irreducibleSpace_of_connectedSpace_of_isAlgClosed (Over.mk (Limits.pullback.snd G.hom g))
  have : Surjective g := ⟨fun x ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  have hsurj : Function.Surjective (Limits.pullback.fst G.hom g) :=
    (MorphismProperty.pullback_fst (P := @Surjective) G.hom g this).surj
  have := (IrreducibleSpace.isIrreducible_univ ↥(Limits.pullback G.hom g)).image _
    (Limits.pullback.fst G.hom g).continuous.continuousOn
  rw [Set.image_univ, hsurj.range_eq] at this
  exact (irreducibleSpace_def _).2 this

/-- A closed subgroup `J` of a connected reduced group scheme `G` locally of finite type over a
field, with `J` reduced of the same dimension as `G`, is all of `G`.
(blueprint: `sk-p-geometry`) -/
theorem isIso_left_of_topologicalKrullDim_eq {J G : Over (Spec (.of k))} [GrpObj J] [GrpObj G]
    [LocallyOfFiniteType G.hom] [IsReduced J.left] [IsReduced G.left] [ConnectedSpace G.left]
    (f : J ⟶ G) [IsMonHom f] [IsClosedImmersion f.left]
    (h : topologicalKrullDim J.left = topologicalKrullDim G.left) : IsIso f.left := by
  have := irreducibleSpace_of_connectedSpace G
  have : IsIntegral G.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : Surjective f.left :=
    ⟨f.left.isClosedEmbedding.isInducing.surjective_of_topologicalKrullDim_eq
      f.left.isClosedEmbedding.isClosed_range (topologicalKrullDim_ne_top G.hom) h⟩
  exact isIso_of_isClosedImmersion_of_surjective f.left

/-! ### Subgroup schemes containing the commutators -/

section ContainsCommutators

variable {S : Scheme.{u}} {G H : Over S} [GrpObj G] [GrpObj H]

/-- A homomorphism of group schemes `f : H ⟶ G` over `S` *contains the commutators* of `G` when
every commutator `a b a⁻¹ b⁻¹` of two points `a b : X ⟶ G` of `G`, with values in an arbitrary
`S`-scheme `X`, factors through `f`. For a subgroup scheme `H ⊆ G` this is the scheme-theoretic
form of `⁅G, G⁆ ⊆ H`, that is, of the commutativity of the quotient `G ⧸ H`.
(blueprint: `sk-i-restriction`) -/
class IsMonHom.ContainsCommutators (f : H ⟶ G) [IsMonHom f] : Prop where
  exists_comp_eq_commutator (f) : ∀ {X : Over S} (a b : X ⟶ G),
    ∃ c : X ⟶ H, c ≫ f = a * b * a⁻¹ * b⁻¹

instance : IsMonHom.ContainsCommutators (𝟙 G) where
  exists_comp_eq_commutator a b := ⟨a * b * a⁻¹ * b⁻¹, Category.comp_id _⟩

theorem IsMonHom.ContainsCommutators.of_eq {f g : H ⟶ G} [IsMonHom f] [IsMonHom g]
    [IsMonHom.ContainsCommutators f] (e : f = g) : IsMonHom.ContainsCommutators g := by
  subst e; assumption

/-- A subgroup scheme containing the commutators is normal: `g h g⁻¹ = (g h g⁻¹ h⁻¹) h`. -/
instance (priority := low) IsMonHom.Normal.of_containsCommutators (f : H ⟶ G) [IsMonHom f]
    [Mono f] [IsMonHom.ContainsCommutators f] : IsMonHom.Normal f where
  exists_comp_eq_conj := by
    obtain ⟨c, hc⟩ :=
      IsMonHom.ContainsCommutators.exists_comp_eq_commutator f (fst G H) (snd G H ≫ f)
    refine ⟨c * snd G H, ?_⟩
    have h := (IsMonHom.monoidHom f (G ⊗ H)).map_mul c (snd G H)
    simp only [IsMonHom.monoidHom_apply] at h
    rw [h, hc, GrpObj.conj, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, whiskerLeft_fst,
      whiskerLeft_snd, inv_mul_cancel_right]

end ContainsCommutators

/-- A fibre product over `Spec k` of two schemes locally of finite type over `k` is locally of
finite type over `k`. -/
instance {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

end AlgebraicGeometry
