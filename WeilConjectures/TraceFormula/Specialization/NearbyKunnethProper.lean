/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.TraceFormula.Specialization.ClosedPointsSupport
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethClosure
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.TraceFormula.Specialization.TraitProductRestrict

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
sections vanishes (blueprint `det-nearby-kunneth-finite-support`; for `ℚ̄_ℓ`-coefficients
`ProEtale.CondensedRing.isZero_of_isZero_upperStar_finsetComplOpens`, a hypothesis here).

## Unfinished inputs

* `NearbyCyclesModel.exists_finite_isIso_upperStar_map_kunnethMap`: the finite-support step, by
  generic slicing and induction on the dimension (SGA 4½, [Th. finitude], §§3.4, 3.7, the inertia
  sequence `1 ⟶ P ⟶ I' ⟶ I ⟶ 1`, and the invariants under the pro-`p` group `P`,
  blueprint `det-nearby-kunneth-invariants`, proved in
  `WeilConjectures.RepresentationTheory.ProfiniteInvariants`). None of strict localizations of
  `𝔸¹_S`, nearby cycles over a varying trait, or the action of inertia on nearby cycles is
  formalised. The slices may be taken of the form `Spec K⟦t⟧` (with `K` a separable closure of
  `k'(x)`, through `k'⟦t⟧[x] ⟶ K⟦t⟧`, the completion of the strict localization), so that the
  induction stays within the traits `trait K`; the identification (2) is then the invertibility
  of the pullback exchange `α` along the slice, for the model whose generic fibre lies over the
  fixed field of `P`, and the restriction of `Π` to the slice is reduced to the Künneth map of the
  sliced models by `NearbyCyclesModel.isIso_map_kunnethMap_iff_of_isIso_pullbackExchange`.

The reduction to proper models is proved: locality on the special fibre reduces to affine total
spaces (`NearbyCyclesModel.isIso_kunnethMap_of_forall_isProper`), and for affine total spaces one
passes to the models of the total spaces and to proper closures
(`NearbyCyclesModel.exists_isProper_openImmersion_of_isAffine`), extending the coefficients by
zero (`NearbyCyclesModel.isIso_kunnethMap_of_forall_isProper_of_isAffine`,
`WeilConjectures.TraceFormula.Specialization.NearbyKunnethClosure`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {ℓ : ℕ} [Fact ℓ.Prime] [hΛ : IsEllAdicFinitenessCoefficient ℓ Λ] [IsFinitenessCoefficient ℓ Λ]

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
vanishes (the hypothesis `hdetect`, blueprint `det-nearby-kunneth-finite-support`). -/
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
      (R((gM)_*⟦Λ⟧).obj (L((M.ε)^*⟦Λ⟧).obj A)) (R((gN)_*⟦Λ⟧).obj (L((N.ε)^*⟦Λ⟧).obj B))))
    (hdetect : ∀ (S : Finset Z'.left) (hS : ∀ x ∈ S, IsClosed {x})
      (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z'.left) Ab.{u + 1})
        (condensedRingObj Λ Z'.left))), boundedConstructible (condensedRingObj Λ Z'.left) C →
      IsZero (L(((finsetComplOpens S hS).ι)^*⟦Λ⟧).obj C) →
        IsZero (R((Z'.hom)_*⟦Λ⟧).obj C) → IsZero C) :
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
    (hdetect S hS C hC h₂ h₁)

omit [Fact ℓ.Prime] [IsFinitenessCoefficient ℓ Λ] [IsSepClosed k'] [Fact (ringChar k').Prime] in
include hΛ in
/-- The source `Lf₁'^* Ψ_M A ⊗ Lf₂'^* Ψ_N B` of the Künneth map is bounded constructible if the
nearby cycles `Ψ_M A`, `Ψ_N B` are. -/
lemma boundedConstructible_kunnethMap_source
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (hΨA : boundedConstructible (condensedRingObj Λ X'.left) ((M.nearbyCycles Λ).obj A))
    (hΨB : boundedConstructible (condensedRingObj Λ Y'.left) ((N.nearbyCycles Λ).obj B)) :
    boundedConstructible (condensedRingObj Λ Z'.left)
      (L((f₁')^*⟦Λ⟧).obj ((M.nearbyCycles Λ).obj A) ⊗
        L((f₂')^*⟦Λ⟧).obj ((N.nearbyCycles Λ).obj B)) := by
  have : (boundedConstructible (condensedRingObj Λ Z'.left)).IsMonoidal :=
    isMonoidal_boundedConstructible Λ (X := Z') (ℓ := ℓ)
  exact CategoryTheory.ObjectProperty.prop_tensor
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hΨA)
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hΨB)

set_option maxHeartbeats 800000 in
-- instance search for the monoidal structure of bounded constructible complexes
omit [Fact ℓ.Prime] [IsFinitenessCoefficient ℓ Λ] [IsSepClosed k'] [Fact (ringChar k').Prime] in
include hΛ φ₁ φ₂ in
/-- The target `Ψ_P (Lf₁^* A ⊗ Lf₂^* B)` of the Künneth map is bounded constructible if the
geometric nearby cycles `Li^* Rj_* Lj^*` of `P` preserve bounded constructible complexes: since
`ε_M` and `ε_N` factor through the total spaces, `Lε_P^* (Lf₁^* A ⊗ Lf₂^* B)` is the pullback
`Lj^* C₀` of a bounded constructible complex on the total space of `P`. -/
lemma boundedConstructible_kunnethMap_target (qP : P.total ⟶ trait k')
    (hgeom : ∀ C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology P.total) Ab.{u + 1})
        (condensedRingObj Λ P.total)), boundedConstructible (condensedRingObj Λ P.total) C₀ →
      boundedConstructible (condensedRingObj Λ Z'.left) ((P.geometric.nearbyCycles Λ).obj C₀))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (hB : boundedConstructible (condensedRingObj Λ Y) B) :
    boundedConstructible (condensedRingObj Λ Z'.left)
      ((P.nearbyCycles Λ).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B)) := by
  have htensor : ∀ C D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology P.total) Ab.{u + 1})
      (condensedRingObj Λ P.total)), boundedConstructible (condensedRingObj Λ P.total) C →
        boundedConstructible (condensedRingObj Λ P.total) D →
          boundedConstructible (condensedRingObj Λ P.total) (C ⊗ D) := by
    have : (boundedConstructible (condensedRingObj Λ P.total)).IsMonoidal :=
      isMonoidal_boundedConstructible Λ (X := Over.mk (qP ≫ traitToBase k' k')) (ℓ := ℓ)
    exact fun C D hC hD ↦ CategoryTheory.ObjectProperty.prop_tensor hC hD
  obtain ⟨C₀, hC₀, ⟨e⟩⟩ := exists_boundedConstructible_tensor_iso Λ φ₁ φ₂ heM heN hA hB htensor
  exact (boundedConstructible _).prop_of_iso (L((P.i)^*⟦Λ⟧).mapIso (R((P.j)_*⟦Λ⟧).mapIso
    ((Functor.Monoidal.μIso L((P.ε)^*⟦Λ⟧) _ _).symm ≪≫
      (((pullbackSquareComparison Λ φ₁.commSq_ε).app A).symm ⊗ᵢ
        ((pullbackSquareComparison Λ φ₂.commSq_ε).app B).symm) ≪≫ e).symm)) (hgeom C₀ hC₀)

omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- **Projective closures over the trait**: an affine scheme of finite type over the trait
`S = Spec k'⟦t⟧` is an open subscheme of a proper `S`-scheme: its closure in `ℙⁿ_S` along an
immersion into `𝔸ⁿ_S ⊆ ℙⁿ_S` (`AlgebraicGeometry.HasCompactification.of_isQuasiAffine`). -/
theorem exists_isProper_openImmersion_of_isAffine {T : Scheme.{u}} (q : T ⟶ trait k')
    [IsAffine T] [LocallyOfFiniteType q] :
    ∃ (Tc : Scheme.{u}) (qc : Tc ⟶ trait k') (c : T ⟶ Tc), IsProper qc ∧ IsOpenImmersion c ∧
      c ≫ qc = q := by
  have : QuasiCompact q := inferInstance
  have := HasCompactification.of_isQuasiAffine q
  let c := HasCompactification.compactification q
  exact ⟨c.Z, c.g, c.i, c.isProper, c.isOpenImmersion, c.comm.symm⟩

omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- A proper scheme over the trait is noetherian. -/
lemma noetherianSpace_of_isProper {T : Scheme.{u}} (q : T ⟶ trait k') [IsProper q] :
    TopologicalSpace.NoetherianSpace T := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian T := ⟨⟩
  infer_instance

omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- The Künneth formula for products over the trait of proper models with compatible projections
applies to the product `X̄ ×_S Ȳ` of the standard models of proper schemes over the trait. -/
theorem isIso_kunnethMap_closure_of_forall_isProper
    (hproper : ∀ {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
      {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
      {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
      {f₂' : Z'.left ⟶ Y'.left} (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
      {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
      {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))},
      M.IsTraitModelOver qM gM → N.IsTraitModelOver qN gN →
      IsPullback φ₁.total φ₂.total qM qN →
      P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM) →
      φ₂.generic ≫ gN = φ₁.generic ≫ gM → IsProper qM → IsProper qN →
      ∀ {eM : M.total ⟶ X}, M.j ≫ eM = M.ε → ∀ {eN : N.total ⟶ Y}, N.j ≫ eN = N.ε →
      ∀ {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))}
        {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          (condensedRingObj Λ Y))},
        boundedConstructible (condensedRingObj Λ X) A →
          boundedConstructible (condensedRingObj Λ Y) B → IsIso (kunnethMap Λ φ₁ φ₂ A B))
    {Xc Yc : Scheme.{u}} (qcM : Xc ⟶ trait k') (qcN : Yc ⟶ trait k') [IsProper qcM]
    [IsProper qcN]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Xc) Ab.{u + 1})
      (condensedRingObj Λ Xc)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Yc) Ab.{u + 1})
      (condensedRingObj Λ Yc)))
    (hA : boundedConstructible (condensedRingObj Λ Xc) A)
    (hB : boundedConstructible (condensedRingObj Λ Yc) B) :
    IsIso (kunnethMap Λ (closureFst qcM qcN) (closureSnd qcM qcN) A B) := by
  refine hproper (closureFst qcM qcN) (closureSnd qcM qcN) (qM := qcM)
    (gM := pullback.snd qcM (traitGenericPoint k')) (qN := qcN)
    (gN := pullback.snd qcN (traitGenericPoint k'))
    ⟨inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback _ _,
      IsPullback.of_hasPullback _ _⟩
    ⟨inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback _ _,
      IsPullback.of_hasPullback _ _⟩
    (IsPullback.of_hasPullback qcM qcN)
    ⟨inferInstanceAs (LocallyOfFiniteType (pullback.fst qcM qcN ≫ qcM)),
      inferInstanceAs (QuasiCompact (pullback.fst qcM qcN ≫ qcM)),
      inferInstanceAs (IsSeparated (pullback.fst qcM qcN ≫ qcM)), ?_,
      IsPullback.of_hasPullback _ _⟩
    (by simp) inferInstance inferInstance (eM := 𝟙 _) (by simp [geometric]) (eN := 𝟙 _)
    (by simp [geometric]) hA hB
  have e : (closureFst qcM qcN).generic ≫ pullback.snd qcM (traitGenericPoint k') =
      pullback.snd (pullback.fst qcM qcN ≫ qcM) (traitGenericPoint k') := by simp
  rw [e]
  exact IsPullback.of_hasPullback _ _

omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- **Reduction of Gabber's Künneth formula to proper models, affine case** (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Reduction to projective flat families"; Illusie,
*Autour du théorème de monodromie locale*, proof of Thm. 4.7): if the Künneth map is an isomorphism
for all products over the trait of models of finite type along proper structure morphisms, with
projections compatible with the structure morphisms of the geometric generic fibres to `Spec Ω`,
then it is an isomorphism for products over the trait of models with affine total spaces.

The Künneth map is that of the models of the total spaces
(`NearbyCyclesModel.isIso_kunnethMap_of_toGeometricGeneric`); these are restrictions of the
standard models of projective closures of the total spaces
(`NearbyCyclesModel.exists_isProper_openImmersion_of_isAffine`), and the coefficients are
extended by zero (`NearbyCyclesModel.isIso_kunnethMap_toGeometricGeneric_of_closure`). -/
theorem isIso_kunnethMap_of_forall_isProper_of_isAffine
    (hproper : ∀ {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
      {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
      {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
      {f₂' : Z'.left ⟶ Y'.left} (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
      {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
      {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))},
      M.IsTraitModelOver qM gM → N.IsTraitModelOver qN gN →
      IsPullback φ₁.total φ₂.total qM qN →
      P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM) →
      φ₂.generic ≫ gN = φ₁.generic ≫ gM → IsProper qM → IsProper qN →
      ∀ {eM : M.total ⟶ X}, M.j ≫ eM = M.ε → ∀ {eN : N.total ⟶ Y}, N.j ≫ eN = N.ε →
      ∀ {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))}
        {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          (condensedRingObj Λ Y))},
        boundedConstructible (condensedRingObj Λ X) A →
          boundedConstructible (condensedRingObj Λ Y) B → IsIso (kunnethMap Λ φ₁ φ₂ A B))
    (h : IsTraitProduct φ₁ φ₂) (hMa : IsAffine M.total) (hNa : IsAffine N.total)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (hB : boundedConstructible (condensedRingObj Λ Y) B) :
    IsIso (kunnethMap Λ φ₁ φ₂ A B) := by
  obtain ⟨qM, gM, qN, gN, hM, hN, hpb, hP, hc⟩ := h.exists_isTraitModelOver
  obtain ⟨eM, heM⟩ := h.exists_comp_ε_left
  obtain ⟨eN, heN⟩ := h.exists_comp_ε_right
  have := hMa
  have := hNa
  have := hM.locallyOfFiniteType
  have := hN.locallyOfFiniteType
  obtain ⟨Xc, qcM, uM, hqM, huM, hcM⟩ := exists_isProper_openImmersion_of_isAffine qM
  obtain ⟨Yc, qcN, uN, hqN, huN, hcN⟩ := exists_isProper_openImmersion_of_isAffine qN
  have := noetherianSpace_of_isProper qcM
  have := noetherianSpace_of_isProper qcN
  refine isIso_kunnethMap_of_toGeometricGeneric Λ _ _ heM heN A B ?_
  exact isIso_kunnethMap_toGeometricGeneric_of_closure Λ hM hN hpb hP hc uM uN hcM hcN
    (fun A' B' hA' hB' ↦ isIso_kunnethMap_closure_of_forall_isProper Λ hproper qcM qcN A' B' hA'
      hB')
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hA)
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hB)

omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- **Reduction of Gabber's Künneth formula to proper models** (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Reduction to projective flat families"; Illusie,
*Autour du théorème de monodromie locale*, proof of Thm. 4.7): if the Künneth map is an isomorphism
for all products over the trait of models of finite type along proper structure morphisms, with
projections compatible with the structure morphisms of the geometric generic fibres to `Spec Ω`,
then it is an isomorphism for all products over the trait.

The assertion is local on the special fibre
(`NearbyCyclesModel.isIso_kunnethMap_of_forall_exists_restriction`): around each point of the
special fibre the product restricts to the product `V ×_S W` of affine opens `V`, `W` of the total
spaces (`NearbyCyclesModel.IsTraitProduct.restrictOpen`), where
`NearbyCyclesModel.isIso_kunnethMap_of_forall_isProper_of_isAffine` applies. -/
theorem isIso_kunnethMap_of_forall_isProper
    (hproper : ∀ {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
      {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
      {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
      {f₂' : Z'.left ⟶ Y'.left} (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
      {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
      {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))},
      M.IsTraitModelOver qM gM → N.IsTraitModelOver qN gN →
      IsPullback φ₁.total φ₂.total qM qN →
      P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM) →
      φ₂.generic ≫ gN = φ₁.generic ≫ gM → IsProper qM → IsProper qN →
      ∀ {eM : M.total ⟶ X}, M.j ≫ eM = M.ε → ∀ {eN : N.total ⟶ Y}, N.j ≫ eN = N.ε →
      ∀ {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))}
        {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          (condensedRingObj Λ Y))},
        boundedConstructible (condensedRingObj Λ X) A →
          boundedConstructible (condensedRingObj Λ Y) B → IsIso (kunnethMap Λ φ₁ φ₂ A B))
    (h : IsTraitProduct φ₁ φ₂)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (hB : boundedConstructible (condensedRingObj Λ Y) B) :
    IsIso (kunnethMap Λ φ₁ φ₂ A B) := by
  obtain ⟨qM, gM, qN, gN, hM, hN, -, hP, -⟩ := h.exists_isTraitModelOver
  have := hM.isTraitModel.isNoetherian_total
  have := hN.isTraitModel.isNoetherian_total
  have := hP.isTraitModel.isNoetherian_total
  have : LocallyOfFiniteType Z'.hom :=
    MorphismProperty.of_isPullback hP.isPullback_i hP.locallyOfFiniteType
  have : QuasiCompact Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i hP.quasiCompact
  have : IsLocallyNoetherian Z'.left := LocallyOfFiniteType.isLocallyNoetherian Z'.hom
  have : CompactSpace Z'.left := QuasiCompact.compactSpace_of_compactSpace Z'.hom
  have : IsNoetherian Z'.left := ⟨⟩
  refine isIso_kunnethMap_of_forall_exists_restriction Λ φ₁ φ₂ A B fun z ↦ ?_
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := φ₁.total (P.i z)) (U := ⊤) trivial
  obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := φ₂.total (P.i z)) (U := ⊤) trivial
  have hVq : QuasiCompact V.ι := inferInstance
  have hWq : QuasiCompact W.ι := inferInstance
  have hUq : QuasiCompact (productOpen φ₁ φ₂ V W).ι := inferInstance
  refine ⟨P.i ⁻¹ᵁ productOpen φ₁ φ₂ V W, _, _, _, _, _, M.restrictOpen V, N.restrictOpen W,
    P.restrictOpen (productOpen φ₁ φ₂ V W), f₁, _, f₂, _, 𝟙 X, _, 𝟙 Y, _, 𝟙 Z,
    φ₁.restrictOpen _ V inf_le_left, φ₂.restrictOpen _ W inf_le_right, M.restrictOpenHom V,
    N.restrictOpenHom W, P.restrictOpenHom _, ⟨hzV, hzW⟩,
    isKunnethRestriction_restrictOpen φ₁ φ₂ V W, ?_⟩
  exact isIso_kunnethMap_of_forall_isProper_of_isAffine Λ hproper (h.restrictOpen V W) hV hW
    ((boundedConstructible _).prop_of_iso ((leftDerivedUpperStarId Λ X).app A).symm hA)
    ((boundedConstructible _).prop_of_iso ((leftDerivedUpperStarId Λ Y).app B).symm hB)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
