/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing

/-!
# The support and cosupport conditions of the perverse t-structure

Let `a : X ⟶ S` be a morphism carrying a compactification, in the intended application the
structure morphism of a separated scheme of finite type over a field `k`, and let `A` be a
coefficient category. For `K` in the derived category `D(X_ét, A)` the *support condition* asks
that the support of the cohomology sheaf `𝓗⁻ⁱK` have dimension at most `i` for every `i`,
and the *cosupport condition* is the support condition for the Verdier dual `𝔻_X K`. The
perverse classes `ᵖD^{≤n}` and `ᵖD^{≥n}` are cut out by the two conditions after the shift
by `n`.

## Main definitions

- `AlgebraicGeometry.Etale.sheafSupport`: the support of an étale sheaf, the complement of the
  largest open on which it vanishes.
- `AlgebraicGeometry.Etale.DerivedCategory.SupportCondition`,
  `AlgebraicGeometry.Etale.DerivedCategory.CosupportCondition`: `SuppCon` and `CosuppCon`
  (blueprint `def-per-support-condition`).
- `AlgebraicGeometry.Etale.DerivedCategory.IsPerverseLE`,
  `AlgebraicGeometry.Etale.DerivedCategory.IsPerverseGE`,
  `AlgebraicGeometry.Etale.DerivedCategory.IsPerverseHeartCandidate`: the classes
  `ᵖD^{≤n}`, `ᵖD^{≥n}` and the perverse heart candidate
  (blueprint `def-per-perverse-subcategories`).

## Implementation notes

The blueprint works with `ℚ̄_ℓ`-coefficients, which are not available on the étale site; the
conditions are stated here for an arbitrary coefficient category `A`, as in the rest of
`WeilConjectures.SixFunctors.Etale`, sheaves of modules over the finite stages `ℤ/ℓⁿ` being
the intended ones. The support of a sheaf is taken closed: the complement
of the union of the opens on which the sheaf vanishes. For a constructible sheaf this is the
closure of the set of points with nonzero stalk, which has the same dimension. The dimension
is the Krull dimension of the subspace, so that the empty support has dimension `⊥ = -∞`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X S : Scheme.{u}}

/-- The support of a sheaf `F` on the small étale site of `X`: the points `x` such that `F`
does not vanish on any Zariski open neighbourhood of `x`. It is closed, the complement of the
largest open on which `F` vanishes. -/
def sheafSupport (F : Sheaf X.smallEtaleTopology A) : Set X :=
  {x | ∀ U : X.Opens, x ∈ U → ¬ IsZero (((U.ι)^*[A]).obj F)}

lemma sheafSupport_congr {F G : Sheaf X.smallEtaleTopology A}
    (e : F ≅ G) : sheafSupport F = sheafSupport G := by
  ext x
  exact forall₂_congr fun U _ ↦ not_congr
    ⟨fun h ↦ h.of_iso (((U.ι)^*[A]).mapIso e).symm,
      fun h ↦ h.of_iso (((U.ι)^*[A]).mapIso e)⟩

namespace DerivedCategory

/-- The *support condition* `SuppCon(K)`: for every `i : ℤ`, the support of the cohomology
sheaf `𝓗⁻ⁱK` has dimension at most `i`, the empty support having dimension `-∞`. In
particular `𝓗⁻ⁱK` vanishes for `i < 0`. (blueprint: `def-per-support-condition`) -/
def SupportCondition (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) : Prop :=
  ∀ i : ℤ, (sheafSupport ((_root_.DerivedCategory.homologyFunctor _ (-i)).obj K)).Nonempty →
    0 ≤ i ∧ topologicalKrullDim
      (sheafSupport ((_root_.DerivedCategory.homologyFunctor _ (-i)).obj K)) ≤ (i.toNat : ℕ∞)

lemma SupportCondition.of_iso {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (e : K ≅ L) (hK : SupportCondition K) : SupportCondition L := by
  intro i
  rw [← sheafSupport_congr ((_root_.DerivedCategory.homologyFunctor _ (-i)).mapIso e)]
  exact hK i

lemma SupportCondition.map_iso {C : Type*} [Category C]
    (F : C ⥤ _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) {x y : C} (e : x ≅ y)
    (h : SupportCondition (F.obj x)) : SupportCondition (F.obj y) :=
  SupportCondition.of_iso (F.mapIso e) h

/-- The class `ᵖD^{≤n}(X) = ᵖD^{≤0}(X)[-n]`: `K` lies in it if `K[n]` satisfies the support
condition. (blueprint: `def-per-perverse-subcategories`) -/
def IsPerverseLE (n : ℤ) (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) : Prop :=
  SupportCondition (K⟦n⟧)

lemma IsPerverseLE.of_iso {n : ℤ}
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (e : K ≅ L)
    (hK : IsPerverseLE n K) : IsPerverseLE n L :=
  SupportCondition.of_iso ((shiftFunctor _ n).mapIso e) hK

/-- The classes are compatible with shifts: `K[m] ∈ ᵖD^{≤n}` if and only if
`K ∈ ᵖD^{≤m+n}`. -/
lemma isPerverseLE_shift_iff (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (m n : ℤ) : IsPerverseLE n (K⟦m⟧) ↔ IsPerverseLE (m + n) K :=
  ⟨fun h ↦ SupportCondition.of_iso ((shiftFunctorAdd _ m n).app K).symm h,
    fun h ↦ SupportCondition.of_iso ((shiftFunctorAdd _ m n).app K) h⟩

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
variable (a : X ⟶ S) [HasCompactification a] [(R(a)_![A]).IsLeftAdjoint]

/-- The *cosupport condition* `CosuppCon(K)`: the support condition for the Verdier dual
`𝔻_X K = RHom(K, ω_X)`, the dualizing complex being taken relative to `a : X ⟶ S`.
(blueprint: `def-per-support-condition`) -/
def CosupportCondition (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) : Prop :=
  SupportCondition ((verdierDual _ a).obj (op K))

variable {a} in
lemma CosupportCondition.of_iso {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (e : K ≅ L) (hK : CosupportCondition a K) :
    CosupportCondition a L :=
  SupportCondition.map_iso _ e.op.symm hK

/-- The class `ᵖD^{≥n}(X) = ᵖD^{≥0}(X)[-n]`: `K` lies in it if `K[n]` satisfies the
cosupport condition. (blueprint: `def-per-perverse-subcategories`) -/
def IsPerverseGE (n : ℤ) (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) : Prop :=
  CosupportCondition a (K⟦n⟧)

/-- The *perverse heart candidate* `Perv^cand(X) = ᵖD^{≤0}(X) ∩ ᵖD^{≥0}(X)`.
(blueprint: `def-per-perverse-subcategories`) -/
def IsPerverseHeartCandidate (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) : Prop :=
  IsPerverseLE 0 K ∧ IsPerverseGE a 0 K

variable {a}

lemma IsPerverseGE.of_iso {n : ℤ}
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (e : K ≅ L)
    (hK : IsPerverseGE a n K) : IsPerverseGE a n L :=
  CosupportCondition.of_iso ((shiftFunctor _ n).mapIso e) hK

/-- The classes are compatible with shifts: `K[m] ∈ ᵖD^{≥n}` if and only if
`K ∈ ᵖD^{≥m+n}`. -/
lemma isPerverseGE_shift_iff (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (m n : ℤ) : IsPerverseGE a n (K⟦m⟧) ↔ IsPerverseGE a (m + n) K :=
  ⟨fun h ↦ CosupportCondition.of_iso ((shiftFunctorAdd _ m n).app K).symm h,
    fun h ↦ CosupportCondition.of_iso ((shiftFunctorAdd _ m n).app K) h⟩

/-- The cosupport classes only depend on the structure morphism `a`, not on the proof that it
carries a compactification; this lets one transport them along an equality `a = a'`. -/
lemma IsPerverseGE.of_eq {a a' : X ⟶ S} [HasCompactification a] [HasCompactification a']
    [(R(a)_![A]).IsLeftAdjoint] [(R(a')_![A]).IsLeftAdjoint]
    (h : a = a') {n : ℤ} {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : IsPerverseGE a n K) : IsPerverseGE a' n K := by
  subst h
  exact hK

end DerivedCategory

end AlgebraicGeometry.Etale
