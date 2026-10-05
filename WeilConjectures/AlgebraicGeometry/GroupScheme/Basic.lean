/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Normal
public import Mathlib.Topology.KrullDimension

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
- `AlgebraicGeometry.isClosed_range_of_isMonHom`: the image of a homomorphism of group schemes
  locally of finite type over `k` is closed.
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
  sorry

/-- A group scheme of finite type over a field has finitely many connected components.
(blueprint: `sk-p-geometry`) -/
theorem finite_connectedComponents (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    Finite (_root_.ConnectedComponents G.left) := by
  sorry

/-- The connected component of the identity of a group scheme of finite type over a field is open.
(blueprint: `sk-p-geometry`) -/
theorem isOpen_connectedComponent_onePoint (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    IsOpen (connectedComponent (GrpObj.onePoint G)) := by
  sorry

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

/-- The image of a homomorphism of group schemes locally of finite type over a field is closed.
(blueprint: `sk-p-geometry`) -/
theorem isClosed_range_of_isMonHom {G K : Over (Spec (.of k))} [GrpObj G] [GrpObj K]
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType K.hom] (f : G ⟶ K) [IsMonHom f] :
    IsClosed (Set.range f.left.base) := by
  sorry

/-- A closed subgroup `J` of a connected reduced group scheme `G` locally of finite type over a
field, with `J` reduced of the same dimension as `G`, is all of `G`.
(blueprint: `sk-p-geometry`) -/
theorem isIso_left_of_topologicalKrullDim_eq {J G : Over (Spec (.of k))} [GrpObj J] [GrpObj G]
    [LocallyOfFiniteType G.hom] [IsReduced J.left] [IsReduced G.left] [ConnectedSpace G.left]
    (f : J ⟶ G) [IsMonHom f] [IsClosedImmersion f.left]
    (h : topologicalKrullDim J.left = topologicalKrullDim G.left) : IsIso f.left := by
  sorry

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
