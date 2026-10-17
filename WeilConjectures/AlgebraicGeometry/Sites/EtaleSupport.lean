/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension

/-!
# Points of bounded transcendence degree and supports of étale sheaves

Let `X` be a scheme of finite type over a field `K`. For `a ≥ 0` the set
`E_a(X) = {x ∈ X | trdeg_K κ(x) ≤ a}` is `AlgebraicGeometry.Scheme.trdegLE`. The support of an
étale sheaf `F` is the set of points `x` such that `F_x̄ ≠ 0` for some geometric point `x̄`
over `x` (`AlgebraicGeometry.Etale.sheafSupport`), and the support of a complex is the union of
the supports of its cohomology sheaves (`AlgebraicGeometry.Etale.complexSupport`). These are the
notions of blueprint `def-kun-support`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-- Blueprint `def-kun-support`: Closed points, transcendence degree, support

For a scheme `X` over a field `K` (structure morphism `b`) and `a ≥ 0`, the set
`E_a(X) = {x ∈ X | trdeg_K κ(x) ≤ a}` of points whose residue field has transcendence degree at
most `a` over `K` (`AlgebraicGeometry.Scheme.residueFieldTrdeg`). -/
def trdegLE {K : Type u} [Field K] {X : Scheme.{u}} (b : X ⟶ Spec (.of K)) (a : ℕ) : Set X :=
  {x | residueFieldTrdeg b x ≤ a}

lemma mem_trdegLE {K : Type u} [Field K] {X : Scheme.{u}} (b : X ⟶ Spec (.of K)) (a : ℕ)
    (x : X) : x ∈ trdegLE b a ↔ residueFieldTrdeg b x ≤ a :=
  Iff.rfl

lemma trdegLE_mono {K : Type u} [Field K] {X : Scheme.{u}} (b : X ⟶ Spec (.of K)) {a a' : ℕ}
    (h : a ≤ a') : trdegLE b a ⊆ trdegLE b a' :=
  fun x (hx : residueFieldTrdeg b x ≤ a) ↦ hx.trans (by exact_mod_cast h)

end Scheme

namespace Etale

variable {X : Scheme.{u}} {A : Type w} [Category.{v} A] [HasColimitsOfSize.{u, u} A]

/-- Blueprint `def-kun-support`: Closed points, transcendence degree, support

The *support* of an étale sheaf `F` on `X`: the set of points `x ∈ X` such that the geometric
stalk `F_x̄` is nonzero for some geometric point `x̄ : Spec Ω ⟶ X` lying over `x` (`Ω` a
separably closed field). -/
def sheafSupport (F : Sheaf X.smallEtaleTopology A) : Set X :=
  {x | ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (s : Spec (.of Ω) ⟶ X),
    s (IsLocalRing.closedPoint Ω) = x ∧
      ¬ IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj F)}

lemma mem_sheafSupport (F : Sheaf X.smallEtaleTopology A) (x : X) :
    x ∈ sheafSupport F ↔ ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω)
      (s : Spec (.of Ω) ⟶ X), s (IsLocalRing.closedPoint Ω) = x ∧
        ¬ IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj F) :=
  Iff.rfl

/-- Isomorphic sheaves have the same support. -/
lemma sheafSupport_congr {F G : Sheaf X.smallEtaleTopology A} (e : F ≅ G) :
    sheafSupport F = sheafSupport G := by
  ext x
  refine exists_congr fun Ω ↦ exists_congr fun _ ↦ exists_congr fun _ ↦ exists_congr fun s ↦
    and_congr_right fun _ ↦ not_congr ⟨fun h ↦ h.of_iso ?_, fun h ↦ h.of_iso ?_⟩
  · exact ((Scheme.pointSmallEtale s).sheafFiber.mapIso e).symm
  · exact (Scheme.pointSmallEtale s).sheafFiber.mapIso e

/-- Blueprint `def-kun-support`: Closed points, transcendence degree, support

The *support* of a complex `K ∈ D(X_ét)`: the union over `q` of the supports of its cohomology
sheaves `H^q(K)`. -/
def complexSupport [Abelian (Sheaf X.smallEtaleTopology A)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology A)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) : Set X :=
  ⋃ q : ℤ, sheafSupport ((DerivedCategory.homologyFunctor _ q).obj K)

lemma mem_complexSupport [Abelian (Sheaf X.smallEtaleTopology A)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology A)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) (x : X) :
    x ∈ complexSupport K ↔
      ∃ q : ℤ, x ∈ sheafSupport ((DerivedCategory.homologyFunctor _ q).obj K) :=
  Set.mem_iUnion

end Etale

end AlgebraicGeometry
