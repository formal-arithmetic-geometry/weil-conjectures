/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Submission.WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The differential of a homomorphism of group schemes over a field

The differential `df : Lie(G) → Lie(H)` of a homomorphism of group schemes `f : G ⟶ H` over a
field `k` sends a tangent vector `v : Spec k[ε] ⟶ G` to `v ≫ f`. It is a homomorphism of Lie
algebras, functorial, injective for monomorphisms and bijective for open immersions. If the
commutators of `H` factor through a subgroup scheme `G ⟶ H`, then the brackets of `Lie(H)` lie in
`Lie(G)`; the tangent vectors of a central subgroup scheme are central.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt IsLocalRing
open scoped MonObj commutatorElement

namespace AlgebraicGeometry.GrpObj

variable {k : Type u} [Field k] {G H : Over (Spec (.of k))} [GrpObj G] [GrpObj H]

/-! ### Composing points with a homomorphism -/

section KerPost

variable {A : Type u} [CommRing A] [Algebra k A]

theorem comp_mem_pointsKer {π : A →ₐ[k] k} (f : G ⟶ H) [IsMonHom f] {p : points G A}
    (hp : p ∈ pointsKer G π) : p ≫ f ∈ pointsKer H π := by
  rw [mem_pointsKer] at hp ⊢
  change points.map G π p ≫ f = 1
  rw [hp, MonObj.one_comp]

/-- Composition with a homomorphism of group schemes `f : G ⟶ H`, on points reducing to the
identity. -/
noncomputable def kerPost {π : A →ₐ[k] k} (f : G ⟶ H) [IsMonHom f] :
    pointsKer G π →* pointsKer H π where
  toFun p := ⟨p.1 ≫ f, comp_mem_pointsKer f p.2⟩
  map_one' := Subtype.ext (MonObj.one_comp f)
  map_mul' p q := Subtype.ext ((IsMonHom.monoidHom f _).map_mul p.1 q.1)

@[simp]
theorem coe_kerPost {π : A →ₐ[k] k} (f : G ⟶ H) [IsMonHom f] (p : pointsKer G π) :
    (kerPost f p : points H A) = p.1 ≫ f :=
  rfl

theorem kerMap_kerPost {B : Type u} [CommRing B] [Algebra k B] {πA : A →ₐ[k] k}
    {πB : B →ₐ[k] k} (ψ : A →ₐ[k] B) (hψ : πB.comp ψ = πA) (f : G ⟶ H) [IsMonHom f]
    (p : pointsKer G πA) : kerMap ψ hψ (kerPost f p) = kerPost f (kerMap ψ hψ p) :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem kerPost_tangentMap [IsLocalRing A] {π : A →ₐ[k] k} (f : G ⟶ H) [IsMonHom f] (m : A)
    (hm : m * m = 0) (hπ : π m = 0) (v : pointsKer G aug₁) :
    kerPost f (tangentMap m hm hπ v) = tangentMap m hm hπ (kerPost f v) :=
  (kerMap_kerPost _ _ f v).symm

theorem kerPost_injective {π : A →ₐ[k] k} (f : G ⟶ H) [IsMonHom f] [Mono f] :
    Function.Injective (kerPost (π := π) f) := fun _ _ h ↦
  Subtype.ext ((cancel_mono f).1 (congrArg Subtype.val h))

/-- A homomorphism of group schemes preserves the bracket of tangent vectors. -/
theorem tangentBracket_kerPost (f : G ⟶ H) [IsMonHom f] (v w : pointsKer G aug₁) :
    tangentBracket (kerPost f v) (kerPost f w) = kerPost f (tangentBracket v w) := by
  apply tangentMul_injective
  rw [tangentMul_tangentBracket, tangentMul, ← kerPost_tangentMap, ← tangentMul,
    tangentMul_tangentBracket, map_commutatorElement, kerPost_tangentMap, kerPost_tangentMap]

end KerPost

/-! ### The differential -/

theorem lieEquivTangent_infPointsMap (f : G ⟶ H) [IsMonHom f] (x : Lie G) :
    lieEquivTangent H (lieEquiv H (infPointsMap f ((lieEquiv G).symm x))) =
      kerPost f (lieEquivTangent G x) := by
  apply Subtype.ext
  change inv dualNumbersToSpecOver ≫ _ = (inv dualNumbersToSpecOver ≫ _) ≫ f
  rw [Equiv.symm_apply_apply, coe_infPointsMap_apply, Category.assoc]

/-- The differential `df : Lie(G) → Lie(H)` of a homomorphism of group schemes `f : G ⟶ H` over
`k`: on tangent vectors, `v ↦ v ≫ f`. It is a homomorphism of Lie algebras.
(blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def differential (f : G ⟶ H) [IsMonHom f] : Lie G →ₗ⁅k⁆ Lie H where
  toFun x := lieEquiv H (infPointsMap f ((lieEquiv G).symm x))
  map_add' x y := by
    simp only [lieEquiv_symm_add, map_mul, lieEquiv_mul]
  map_smul' c x := by
    change _ = c • lieEquiv H _
    rw [show c • x = (Scheme.ΓSpecIso (.of k)).inv.hom c • x from rfl, lieEquiv_symm_smul,
      show infPointsMap f (infPointsScale G _ ((lieEquiv G).symm x)) =
        infPointsScale H _ (infPointsMap f ((lieEquiv G).symm x)) from
          Subtype.ext ((coe_infPointsMap_apply _ _).trans (Category.assoc _ _ _))]
    exact toLie_infPointsScale H _ _
  map_lie' {x y} := by
    apply (lieEquivTangent H).injective
    change lieEquivTangent H (lieEquiv H (infPointsMap f ((lieEquiv G).symm ⁅x, y⁆))) =
      lieEquivTangent H ⁅lieEquiv H (infPointsMap f ((lieEquiv G).symm x)),
        lieEquiv H (infPointsMap f ((lieEquiv G).symm y))⁆
    rw [lieEquivTangent_infPointsMap, lieEquivTangent_lie, lieEquivTangent_lie,
      lieEquivTangent_infPointsMap, lieEquivTangent_infPointsMap, tangentBracket_kerPost]

theorem differential_apply (f : G ⟶ H) [IsMonHom f] (x : Lie G) :
    differential f x = lieEquiv H (infPointsMap f ((lieEquiv G).symm x)) :=
  rfl

theorem lieEquivTangent_differential (f : G ⟶ H) [IsMonHom f] (x : Lie G) :
    lieEquivTangent H (differential f x) = kerPost f (lieEquivTangent G x) :=
  lieEquivTangent_infPointsMap f x


theorem differential_congr {f g : G ⟶ H} [IsMonHom f] [IsMonHom g] (e : f = g) :
    differential f = differential g := by
  subst e; rfl

theorem differential_id : differential (𝟙 G) = LieHom.id := by
  ext x
  rw [differential_apply, LieHom.id_apply]
  conv_rhs => rw [← (lieEquiv G).apply_symm_apply x]
  congr 1

theorem differential_comp {K : Over (Spec (.of k))} [GrpObj K] (f : G ⟶ H) (g : H ⟶ K)
    [IsMonHom f] [IsMonHom g] : differential (f ≫ g) = (differential g).comp (differential f) := by
  ext x
  rw [LieHom.comp_apply, differential_apply, differential_apply, differential_apply,
    Equiv.symm_apply_apply]
  congr 1

/-- The differential of a monomorphism of group schemes, for instance of a closed immersion, is
injective. -/
theorem differential_injective (f : G ⟶ H) [IsMonHom f] [Mono f] :
    Function.Injective (differential f) := fun x y h ↦ by
  apply (lieEquivTangent G).injective
  apply kerPost_injective f
  rw [← lieEquivTangent_differential, ← lieEquivTangent_differential, h]


end AlgebraicGeometry.GrpObj
