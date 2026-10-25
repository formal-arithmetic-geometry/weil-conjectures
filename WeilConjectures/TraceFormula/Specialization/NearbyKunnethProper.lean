/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal

/-!

# Gabber's Künneth formula for nearby cycles: proper models

Let `P` be the product over the strictly henselian trait `S = Spec k'⟦t⟧` (`k'` separably closed)
of models `M`, `N` of finite type along proper structure morphisms, with projections compatible
with the structure morphisms of the geometric generic fibres to `Spec Ω`. This file proves that
the Künneth map `Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)` is an isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_kunnethMap_of_isProper`),
following Illusie's argument (*Autour du théorème de monodromie locale*, Thm. 4.7; blueprint
`sk-prop-tf-nearby-external-kunneth`): the cone `C` of `Π_{A,B}`

* has no global sections, `RΓ(X_s × Y_s, C) = 0` (the global-sections step,
  `NearbyCyclesModel.isIso_lowerStar_kunnethMap`);
* is supported on finitely many closed points
  (`NearbyCyclesModel.exists_finite_isIso_upperStar_map_kunnethMap`, the finite-support step);

and a bounded constructible complex supported on finitely many closed points without global
sections vanishes (`ProEtale.CondensedRing.isZero_of_isZero_upperStar_finsetComplOpens`, blueprint
`det-nearby-kunneth-finite-support`).

## Unfinished inputs

* `NearbyCyclesModel.exists_finite_isIso_upperStar_map_kunnethMap`: the finite-support step, by
  generic slicing and induction on the dimension (SGA 4½, [Th. finitude], §§3.4, 3.7, the inertia
  sequence `1 ⟶ P ⟶ I' ⟶ I ⟶ 1`, and the invariants under the pro-`p` group `P`,
  blueprint `det-nearby-kunneth-invariants`, proved in
  `WeilConjectures.RepresentationTheory.ProfiniteInvariants`). None of strict localizations of `𝔸¹_S`, nearby
  cycles over a varying trait, or the action of inertia on nearby cycles is formalised.
* `ProEtale.CondensedRing.isZero_of_isZero_upperStar_finsetComplOpens`: blueprint
  `det-nearby-kunneth-finite-support` for closed points which need not be rational (the special
  fibre is over a separably closed, not necessarily perfect, field). The case of rational points
  is `ProEtale.CondensedRing.isZero_of_isZero_upperStar_pointsComplι_of_isZero_lowerStar`; the
  general case reduces to it by the finite purely inseparable base change making the finitely many
  points rational (topological invariance,
  `ProEtale.CondensedRing.isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Complexes supported at finitely many closed points -/

/-- The open complement of a finite set of closed points of a scheme. -/
def finsetComplOpens {X : Scheme.{u}} (S : Finset X) (hS : ∀ x ∈ S, IsClosed {x}) : X.Opens :=
  ⟨(↑S)ᶜ, by
    rw [isOpen_compl_iff, ← Set.biUnion_of_singleton (↑S : Set X)]
    exact S.finite_toSet.isClosed_biUnion fun x hx ↦ hS x hx⟩

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {ℓ : ℕ} [Fact ℓ.Prime] [hΛ : IsEllAdicFinitenessCoefficient ℓ Λ] [IsFinitenessCoefficient ℓ Λ]

include hΛ in
/-- **Global sections detect complexes supported at finitely many closed points** (blueprint
`det-nearby-kunneth-finite-support`): let `V` be a separated scheme of finite type over a
separably closed field `k` and `S` a finite set of closed points of `V`. A bounded constructible
complex `C` on `V` whose restriction to `V ∖ S` vanishes and whose global sections `RΓ(V, C)`
vanish is zero.

The closed points of `V` need not be rational (`k` need not be perfect). The case of rational
points is `ProEtale.CondensedRing.isZero_of_isZero_upperStar_pointsComplι_of_isZero_lowerStar`;
the general case reduces to it by a finite purely inseparable extension `k''` of `k` over which
the points of `S` become rational: the base change `V_{k''} ⟶ V` is a finite universal
homeomorphism, so pullback along it is an equivalence on bounded constructible complexes
(topological invariance, SGA 4 VIII 1.1). -/
theorem isZero_of_isZero_upperStar_finsetComplOpens {k : Type u} [Field k] [IsSepClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {V : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (S : Finset V.left) (hS : ∀ x ∈ S, IsClosed {x})
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V.left) Ab.{u + 1})
      (condensedRingObj Λ V.left)))
    (hC : boundedConstructible (condensedRingObj Λ V.left) C)
    (hU : IsZero (L(((finsetComplOpens S hS).ι)^*⟦Λ⟧).obj C))
    (hΓ : IsZero (R((V.hom)_*⟦Λ⟧).obj C)) : IsZero C :=
  sorry

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

include hΛ in
/-- **The finite-support step of Gabber's Künneth formula** (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Finite support"; Illusie, *Autour du théorème de monodromie
locale*, proof of Thm. 4.7): for the product `P` over the strictly henselian trait of models `M`,
`N` of finite type and bounded constructible `A`, `B`, the Künneth map `Π_{A,B}` is an
isomorphism away from finitely many closed points of the special fibre `X_s × Y_s`.

The proof is by induction on the dimension of `X_η̄ × Y_η̄`: on small neighbourhoods with
quasi-finite coordinates `X ⟶ 𝔸^q_S`, `Y ⟶ 𝔸^r_S`, the restriction of `Π_{A,B}` to the generic
slice `S' = (𝔸¹_S)_{(s')}` of a coordinate is, by the generic-slicing description of nearby
cycles (SGA 4½, [Th. finitude], §§3.4, 3.7), the invariants under the pro-`p` kernel `P` of
`I' ⟶ I` of the Künneth map of the sliced models, of smaller dimension; invariants under `P`
commute with tensor products with complexes with trivial `P`-action (blueprint
`det-nearby-kunneth-invariants`). Hence the cone of `Π_{A,B}` lies over finitely many points of
each coordinate line, and is supported on finitely many points since the coordinates are
quasi-finite. -/
theorem exists_finite_isIso_upperStar_map_kunnethMap (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (hB : boundedConstructible (condensedRingObj Λ Y) B) :
    ∃ (S : Finset Z'.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsIso (L(((finsetComplOpens S hS).ι)^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) :=
  sorry

set_option maxHeartbeats 1600000 in
-- the triangle of the Künneth map has large terms
include hΛ in
/-- **Gabber's Künneth formula for proper models** (Illusie, *Autour du théorème de monodromie
locale*, Thm. 4.7; blueprint `sk-prop-tf-nearby-external-kunneth`): for the product `P` over the
strictly henselian trait of models `M`, `N` of finite type along proper structure morphisms, with
projections compatible with the structure morphisms to `Spec Ω`, and bounded constructible `A`,
`B`, the Künneth map `Π_{A,B}` is an isomorphism. Its cone `C` is bounded constructible (given
that the source and target of `Π_{A,B}` are, by Deligne's finiteness theorem), has no global
sections (`NearbyCyclesModel.isIso_lowerStar_kunnethMap`, given that the Künneth map of the trait
at the cohomology of the geometric generic fibres is invertible), and is supported on finitely
many closed points (`NearbyCyclesModel.exists_finite_isIso_upperStar_map_kunnethMap`); hence it
vanishes (`ProEtale.CondensedRing.isZero_of_isZero_upperStar_finsetComplOpens`). -/
theorem isIso_kunnethMap_of_isProper (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) [IsProper qM] [IsProper qN]
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (hB : boundedConstructible (condensedRingObj Λ Y) B)
    (hΨA : boundedConstructible (condensedRingObj Λ X'.left) ((M.nearbyCycles Λ).obj A))
    (hΨB : boundedConstructible (condensedRingObj Λ Y'.left) ((N.nearbyCycles Λ).obj B))
    (hsrc : boundedConstructible (condensedRingObj Λ Z'.left)
      (L((f₁')^*⟦Λ⟧).obj ((M.nearbyCycles Λ).obj A) ⊗
        L((f₂')^*⟦Λ⟧).obj ((N.nearbyCycles Λ).obj B)))
    (htgt : boundedConstructible (condensedRingObj Λ Z'.left)
      ((P.nearbyCycles Λ).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B)))
    (hT : IsIso (kunnethMap Λ (Hom.id (traitGenericModel k')) (Hom.id (traitGenericModel k'))
      (R((gM)_*⟦Λ⟧).obj (L((M.ε)^*⟦Λ⟧).obj A)) (R((gN)_*⟦Λ⟧).obj (L((N.ε)^*⟦Λ⟧).obj B)))) :
    IsIso (kunnethMap Λ φ₁ φ₂ A B) := by
  obtain ⟨S, hS, hU⟩ := exists_finite_isIso_upperStar_map_kunnethMap Λ hM hN hpb hP heM heN hA hB
  have hR := isIso_lowerStar_kunnethMap Λ hM hN hpb hP hgen heM heN hA hB hΨA hΨB hT
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle (kunnethMap Λ φ₁ φ₂ A B)
  have : LocallyOfFiniteType Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i
    hP.locallyOfFiniteType
  have : QuasiCompact Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.quasiCompact
  have : IsSeparated Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.isSeparated
  have : IsLocallyNoetherian Z'.left := LocallyOfFiniteType.isLocallyNoetherian Z'.hom
  have : CompactSpace Z'.left := QuasiCompact.compactSpace_of_compactSpace Z'.hom
  have : IsNoetherian Z'.left := ⟨⟩
  have hC := (boundedConstructible (condensedRingObj Λ Z'.left)).ext_of_isTriangulatedClosed₃ _
    hT hsrc htgt
  have h₁ := Triangle.isZero₃_of_isIso₁ _ (R((Z'.hom)_*⟦Λ⟧).map_distinguished _ hT) hR
  have h₂ := Triangle.isZero₃_of_isIso₁ _
    (L(((finsetComplOpens S hS).ι)^*⟦Λ⟧).map_distinguished _ hT) hU
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_isZero_upperStar_finsetComplOpens Λ S hS C hC h₂ h₁)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
