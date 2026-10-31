/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDgModules
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.RingedDgScalarAdjunction
import WeilConjectures.CategoryTheory.SheafDgQuasiIsoUnit
import WeilConjectures.CategoryTheory.SheafDgQuasiIsoCounit

/-!
# Derived equivalence from a quasi-isomorphism of sheaf DG algebras

Source: Stacks Project, `sdga.tex`, Tag 0FTZ and Tag 0FTR (blueprint:
lem-sf-sheaf-dg-quasiiso-equivalence).

The existing ringed-site DG module framework supplies the sheafified balanced tensor,
restriction of scalars, derived localizations, and the normalized scalar-adjunction
model.  The structure below records the additional invertibility conclusion of the
quasi-isomorphism lemma without introducing a second DG-module category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalOpposite CategoryTheory.Pretriangulated

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}

/-- The derived scalar-extension/restriction package attached to a quasi-isomorphism.

Source: Stacks Project, `sdga.tex`, Tags 0FTZ and 0FTR (blueprint:
lem-sf-sheaf-dg-quasiiso-equivalence).  The `model` field is the canonical
`ScalarModel`: its ordinary component is tensor with the target algebra, its
`extension` is the universal derived extension, its `restriction` is exact
restriction of scalars, and its `adjunction` has the ordinary unit and multiplication
counit normalizations.  The two `IsIso` fields state that these adjunction maps are
isomorphisms, so the two functors are quasi-inverses.  The field `adjunction_shift`
states that the unit and counit commute with every integer shift, for the shift
structures `model.extensionShift` and `model.restrictionShift` of the two functors. -/
class DgQuasiIsoEquivalence {A B : Algebra O} (α : A ⟶ B) where
  [source : DerivedStructure A]
  [target : DerivedStructure B]
  model : ScalarModel α
  adjunction_shift :
    letI := model.extensionShift
    letI := model.restrictionShift
    model.adjunction.CommShift ℤ
  unit_isIso : ∀ M : Derived A, IsIso (model.adjunction.unit.app M)
  counit_isIso : ∀ N : Derived B, IsIso (model.adjunction.counit.app N)

/-- A quasi-isomorphism of ringed-site DG algebras induces a derived equivalence.

Source: Stacks Project, `sdga.tex`, Tag 0FTZ (`lemma-qis-equivalence`), including
its exact restriction quasi-inverse, normalized extension/restriction adjunction,
and Tag 0FTR for the identity underlying ringed topos
(blueprint: lem-sf-sheaf-dg-quasiiso-equivalence).

The site is small in the fixed module universe and its coefficient sheaf is
commutative.  `A` and `B` are associative unital DG algebras over that sheaf;
`α.hom` is their degree-zero algebra chain map.  `QuasiIso α.hom` renders the
hypothesis that every cohomology map is an isomorphism.  The conclusion packages
exact restriction, universal derived extension by the sheafified balanced graded
tensor, the ordinary unit and multiplication counit, their derived adjunction,
its invertible unit and counit, and compatibility of the functors, unit and counit
with all integer shifts.  No boundedness, coefficient-flatness, or topological-space
hypothesis is added.

Proof plan:
1. Put `F(M) = M ⊗_A B` and let `U` restrict the right action along `α`. The formulas
`f ↦ (m ↦ f(m ⊗ 1))` and `g ↦ (m ⊗ b ↦ g(m) b)` are mutually inverse on chain maps and
on homotopies, giving `F ⊣ U` on homotopy categories with unit `m ↦ m ⊗ 1` and counit
`n ⊗ b ↦ n b` (lem-sfb-sheaf-dg-homotopy-system). Restriction keeps the underlying
complexes, so preserves quasi-isomorphisms and cones; tensor commutes with cones, the
comparison `M[1] ⊗_A B ≅ (M ⊗_A B)[1]` being the identity on homogeneous tensors. Both
functors are exact (Stacks 0FTZ, section-dg-bimodules).
2. Good right `A`-modules (lem-sfb-sheaf-dg-good-resolutions) resolve every `M`. For a
quasi-isomorphism `s` of good modules, `C(s)` is good and acyclic, so `C(s) ⊗_A B` is
acyclic; by the cone identification of step 1 and the cone criterion, `s ⊗ 1` is a
quasi-isomorphism. No flatness of `B` is used (Stacks 0FSH, 0FSI, 0FTF).
3. lem-sf-localized-derived-adjunction, with `K(A)`, `K(B)`, `E = F`, `R = U` and the
quasi-isomorphisms, gives the universal `L_α = - ⊗^L_A B`, its comparison
`c_P : L_α(Q_A P) ≅ Q_B(P ⊗_A B)` on good `P`, and the adjunction `L_α ⊣ U_α` with
`U_α(c_P) ∘ η_{Q_A P} = Q_A(p ↦ p ⊗ 1)` and the localized multiplication counit
(Stacks 0FTZ, 0FTR).
4. The cone of `α` is acyclic and is a left DG `A`-module with `a(b, x) = (ab, (-1)^|a| ax)`.
For good `P`, `P ⊗_A C(α)` is acyclic, and `C(P ⊗_A α) ≅ P ⊗_A C(α)` by the sign
`(-1)^|p|` on the shifted summand. So `p ↦ p ⊗ 1` is a quasi-isomorphism, and by step 3
the unit is invertible on `Q_A P`; a good resolution and naturality give it on every
`Q_A M` (Stacks 0FTZ, 0FSH).
5. `U_α` detects isomorphisms: write a morphism as a roof `Q_B(g) Q_B(s)^{-1}`; if its
restriction is invertible, every `H^q(g)` is invertible since restriction keeps the
underlying complex, so `g` is a quasi-isomorphism (lem-sfb-sheaf-dg-homotopy-system).
6. The triangle identity `U_α(ε_N) ∘ η_{U_α N} = 1` and step 4 make `U_α(ε_N)` invertible,
hence `ε_N` invertible by step 5. Unit and counit are isomorphisms, so `U_α` is an
equivalence with quasi-inverse `L_α` (Stacks 0FTZ).
7. The shift `M[k]^i = M^{i+k}` with differential `(-1)^k d_M` keeps the action; the map
`M[k] ⊗_A B → (M ⊗_A B)[k]` is the identity on tensors, restriction commutes strictly
with shifts, and the ordinary unit and counit commute with these identifications. The
shift-compatible derivation of lem-sf-localized-derived-adjunction gives the shift
structures of `L_α`, `U_α` and the compatibility of the derived unit and counit
(Stacks 0FTR, section-shift-dg). -/
theorem sheaf_dg_quasiiso_equivalence {A B : Algebra O} (α : A ⟶ B)
    (hα : QuasiIso α.hom) : Nonempty (DgQuasiIsoEquivalence α) := by
  classical
  obtain ⟨s⟩ := ringed_dg_scalar_adjunction O A B α
  let := s.source
  let := s.target
  let := s.model.restrictionShift
  let := s.model.restrictionExact
  let := s.model.adjunction.leftAdjointCommShift ℤ
  let : s.model.adjunction.CommShift ℤ :=
    s.model.adjunction.commShift_of_rightAdjoint ℤ
  let m : ScalarModel α :=
    { s.model with
      extensionShift := s.model.adjunction.leftAdjointCommShift ℤ
      extensionExact := s.model.adjunction.isTriangulated_leftAdjoint }
  let : m.extension.CommShift ℤ := m.extensionShift
  let : m.restriction.CommShift ℤ := m.restrictionShift
  let : m.adjunction.CommShift ℤ := m.adjunction.commShift_of_rightAdjoint ℤ
  refine ⟨{ model := m, adjunction_shift := ?_, unit_isIso := ?_, counit_isIso := ?_ }⟩
  · exact inferInstance
  · exact sheaf_dg_quasiiso_unit_isIso α s hα
  · exact sheaf_dg_quasiiso_counit_isIso α s hα

end CategoryTheory.RingedSiteDg
