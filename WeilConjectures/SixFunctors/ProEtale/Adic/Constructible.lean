/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf

/-!
# Lisse and constructible `ℓ`-adic sheaves on the pro-étale site

Let `X` be a scheme. Following Bhatt–Scholze (*The pro-étale topology for schemes*, §6.8) and
the blueprint (`def-weil-constructible-heart`, `def-weil-finite-torsion-constructibility`), a
sheaf `F` of `ℚ̄_ℓ`-modules on the small pro-étale site of `X` is

- *lisse* (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf`) if it is pro-étale locally a finite
  direct sum of copies of the constant `ℓ`-adic sheaf `ℚ̄_ℓ`
  (`AlgebraicGeometry.ProEtale.adicConstantSheaf`), that is, locally free of finite rank over
  `ℚ̄_ℓ,X`;
- *constructible* (`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf`) if, locally on `X`,
  `X` is the disjoint union of finitely many locally closed subschemes on each of which `F` is
  lisse (`AlgebraicGeometry.ProEtale.IsAdicStratifiedLisseSheaf`).

A lisse sheaf on a connected `X` is the same as a continuous finite-dimensional representation
of `π₁(X)` with coefficients in a finite extension `E` of `ℚ_ℓ`: the trivialising pro-étale
cover may be taken to be a pro-finite étale Galois cover, whose group acts continuously on the
fibre `E^n`. In particular a lisse sheaf has a finite field of definition, and the category
of constructible `ℚ̄_ℓ`-sheaves is the `2`-colimit over finite `E ⊆ ℚ̄_ℓ` of the categories of
constructible `E`-sheaves (`def-weil-algebraically-closed-coefficients`).

The strata are only required to be locally closed: on the noetherian schemes of the blueprint
every locally closed subset is constructible, and with this convention pullback along an
arbitrary morphism preserves constructibility. The stratification is only required locally on
`X`, so that constructibility is a local property; on the quasi-compact schemes of the blueprint
this is the same as a global finite stratification.

## Main definitions

- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf` and
  `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf`.
- `AlgebraicGeometry.ProEtale.adicConstructibleSheaf`: constructibility as an object property.
- `AlgebraicGeometry.ProEtale.IsIrreducibleAdicLocalSystem`: irreducible lisse sheaves.

## Main results

- `AlgebraicGeometry.ProEtale.isAdicLisseSheaf_adicConstantSheaf`: `ℚ̄_ℓ,X` is lisse.
- The constructible sheaves contain `0` and are closed under isomorphisms, kernels, cokernels,
  finite products and extensions; the last four are Bhatt–Scholze, Lemma 6.8.? / the blueprint
  `def-weil-constructible-heart`, stated here with `sorry`.
- `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.upperStar`: pullback preserves
  constructibility (stated with `sorry`).
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- A sheaf of `ℚ̄_ℓ`-modules on the small pro-étale site of `X` is *lisse* if it is pro-étale
locally isomorphic to a finite direct sum of copies of the constant `ℓ`-adic sheaf `ℚ̄_ℓ`: there
is a pro-étale covering family of `X` over each member `f : V ⟶ X` of which `f^* F ≅ ℚ̄_ℓ,Vⁿ`. -/
def IsAdicLisseSheaf (F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) : Prop :=
  ∃ R ∈ Scheme.proetalePrecoverage X, ∀ ⦃V : Scheme.{u}⦄ (f : V ⟶ X), R f →
    ∃ n : ℕ, Nonempty ((f)^*[WeilCoefficients.{u} l].obj F ≅
      ⨁ fun _ : Fin n ↦ adicConstantSheaf l V)

/-- Being lisse is invariant under isomorphism. -/
lemma IsAdicLisseSheaf.of_iso {F G : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)}
    (e : F ≅ G) (hF : IsAdicLisseSheaf F) : IsAdicLisseSheaf G := by
  obtain ⟨R, hR, h⟩ := hF
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨n, ⟨e'⟩⟩ := h f hf
  exact ⟨n, ⟨((f)^*[_].mapIso e).symm ≪≫ e'⟩⟩

/-- The constant `ℓ`-adic sheaf is lisse, trivialised by the identity cover. -/
lemma isAdicLisseSheaf_adicConstantSheaf (X : Scheme.{u}) :
    IsAdicLisseSheaf (adicConstantSheaf l X) := by
  refine ⟨.singleton (𝟙 X), Precoverage.mem_coverings_of_isIso _, fun V f hf ↦ ?_⟩
  obtain ⟨⟩ := hf
  exact ⟨1, ⟨(upperStarId _ X).app _ ≪≫ (biproduct.isoProduct
    (fun _ : Fin 1 ↦ adicConstantSheaf l X) ≪≫ productUniqueIso _).symm⟩⟩

/-- A sheaf of `ℚ̄_ℓ`-modules on the small pro-étale site of `X` is *stratified lisse* if `X` is
the disjoint union of finitely many locally closed subschemes `Z_k`, given by immersions
`i_k : Z_k ⟶ X` whose images partition `X`, such that each restriction `i_k^* F` is lisse. -/
def IsAdicStratifiedLisseSheaf (F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    Prop :=
  ∃ (ι : Type) (_ : Finite ι) (Z : ι → Scheme.{u}) (i : (k : ι) → Z k ⟶ X),
    (∀ k, IsImmersion (i k)) ∧ (∀ x : X, ∃! k, x ∈ Set.range (i k).base) ∧
      ∀ k, IsAdicLisseSheaf ((i k)^*[WeilCoefficients.{u} l].obj F)

/-- Being stratified lisse is invariant under isomorphism. -/
lemma IsAdicStratifiedLisseSheaf.of_iso
    {F G : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)} (e : F ≅ G)
    (hF : IsAdicStratifiedLisseSheaf F) : IsAdicStratifiedLisseSheaf G := by
  obtain ⟨ι, hι, Z, i, hi, hcover, h⟩ := hF
  exact ⟨ι, hι, Z, i, hi, hcover, fun k ↦ (h k).of_iso ((_)^*[_].mapIso e)⟩

/-- A lisse sheaf is stratified lisse, with the trivial stratification. -/
lemma IsAdicLisseSheaf.isAdicStratifiedLisseSheaf
    {F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)} (hF : IsAdicLisseSheaf F) :
    IsAdicStratifiedLisseSheaf F :=
  ⟨Unit, inferInstance, fun _ ↦ X, fun _ ↦ 𝟙 X, fun _ ↦ inferInstance,
    fun x ↦ ⟨(), ⟨x, rfl⟩, fun _ _ ↦ rfl⟩,
    fun _ ↦ hF.of_iso ((upperStarId _ X).app F).symm⟩

/-- A sheaf of `ℚ̄_ℓ`-modules on the small pro-étale site of `X` is *constructible* if it is
stratified lisse locally on `X`: every point of `X` has an open neighbourhood `W`, given by an
open immersion `j : W ⟶ X`, such that `X ∩ W` is the disjoint union of finitely many locally
closed subschemes on each of which `j^* F` is lisse. On a quasi-compact `X` this is the same as
being stratified lisse. -/
def IsAdicConstructibleSheaf (F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    Prop :=
  ∀ x : X, ∃ (W : Scheme.{u}) (j : W ⟶ X), IsOpenImmersion j ∧ x ∈ Set.range j.base ∧
    IsAdicStratifiedLisseSheaf ((j)^*[WeilCoefficients.{u} l].obj F)

/-- Being constructible is invariant under isomorphism. -/
lemma IsAdicConstructibleSheaf.of_iso
    {F G : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)} (e : F ≅ G)
    (hF : IsAdicConstructibleSheaf F) : IsAdicConstructibleSheaf G := by
  intro x
  obtain ⟨W, j, hj, hx, h⟩ := hF x
  exact ⟨W, j, hj, hx, h.of_iso ((_)^*[_].mapIso e)⟩

/-- A stratified lisse sheaf is constructible. -/
lemma IsAdicStratifiedLisseSheaf.isAdicConstructibleSheaf
    {F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)}
    (hF : IsAdicStratifiedLisseSheaf F) : IsAdicConstructibleSheaf F := by
  intro x
  exact ⟨X, 𝟙 X, inferInstance, ⟨x, rfl⟩, hF.of_iso ((upperStarId _ X).app F).symm⟩

/-- A lisse sheaf is constructible. -/
lemma IsAdicLisseSheaf.isAdicConstructibleSheaf
    {F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)} (hF : IsAdicLisseSheaf F) :
    IsAdicConstructibleSheaf F :=
  hF.isAdicStratifiedLisseSheaf.isAdicConstructibleSheaf

/-- The constant `ℓ`-adic sheaf is constructible. -/
lemma isAdicConstructibleSheaf_adicConstantSheaf (X : Scheme.{u}) :
    IsAdicConstructibleSheaf (adicConstantSheaf l X) :=
  (isAdicLisseSheaf_adicConstantSheaf X).isAdicConstructibleSheaf

/-- The pullback of a lisse sheaf is lisse: the pullback of a trivialising cover is a
trivialising cover, and the pullback of the constant `ℓ`-adic sheaf is the constant `ℓ`-adic
sheaf. -/
theorem IsAdicLisseSheaf.upperStar {Y : Scheme.{u}} (f : Y ⟶ X)
    {F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)} (hF : IsAdicLisseSheaf F) :
    IsAdicLisseSheaf ((f)^*[WeilCoefficients.{u} l].obj F) :=
  sorry

/-- The pullback of a constructible sheaf is constructible: the preimages of the open
neighbourhoods and of the strata are open neighbourhoods and strata, given by the base changes
of the immersions, and the restrictions to them are pullbacks of lisse sheaves. -/
theorem IsAdicConstructibleSheaf.upperStar {Y : Scheme.{u}} (f : Y ⟶ X)
    {F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)}
    (hF : IsAdicConstructibleSheaf F) :
    IsAdicConstructibleSheaf ((f)^*[WeilCoefficients.{u} l].obj F) :=
  sorry

/-- A finite direct sum of lisse sheaves is lisse: refine the two trivialising covers. -/
theorem IsAdicLisseSheaf.biprod
    {F G : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)} (hF : IsAdicLisseSheaf F)
    (hG : IsAdicLisseSheaf G) : IsAdicLisseSheaf (F ⊞ G) :=
  sorry

/-- A sheaf of `ℚ̄_ℓ`-modules on the small pro-étale site of `X` is an *irreducible `ℓ`-adic local
system* if it is lisse and nonzero, and every lisse subsheaf of it is zero or all of it. For
`X` connected this says that the corresponding continuous representation of `π₁(X)` is
irreducible. -/
def IsIrreducibleAdicLocalSystem
    (F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) : Prop :=
  IsAdicLisseSheaf F ∧ ¬ IsZero F ∧
    ∀ (G : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) (i : G ⟶ F), Mono i →
      IsAdicLisseSheaf G → IsZero G ∨ IsIso i

variable (l X) in
/-- Constructibility of `ℓ`-adic pro-étale sheaves, as an object property. -/
def adicConstructibleSheaf :
    ObjectProperty (Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :=
  fun F ↦ IsAdicConstructibleSheaf F

lemma adicConstructibleSheaf_iff (F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    adicConstructibleSheaf l X F ↔ IsAdicConstructibleSheaf F :=
  Iff.rfl

instance : (adicConstructibleSheaf l X).IsClosedUnderIsomorphisms where
  of_iso e hF := IsAdicConstructibleSheaf.of_iso e hF

instance : (adicConstructibleSheaf l X).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, IsAdicLisseSheaf.isAdicConstructibleSheaf
      ⟨.singleton (𝟙 X), Precoverage.mem_coverings_of_isIso _, fun V f hf ↦ ?_⟩⟩
    obtain ⟨⟩ := hf
    refine ⟨0, ⟨IsZero.iso ?_ ?_⟩⟩
    · exact Functor.map_isZero _ (isZero_zero _)
    · exact ⟨fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext' _ _ fun j ↦ Fin.elim0 j⟩⟩,
        fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext _ _ fun j ↦ Fin.elim0 j⟩⟩⟩

/-- **Kernels of constructible sheaves are constructible** (Bhatt–Scholze, §6.8): after
refining the stratifications, a morphism of constructible sheaves is a morphism of lisse
sheaves on each stratum, whose rank is constant on the strata of a further finite
stratification; on these the kernel is lisse. -/
instance : (adicConstructibleSheaf l X).IsClosedUnderKernels :=
  sorry

/-- **Cokernels of constructible sheaves are constructible**, as for kernels. -/
instance : (adicConstructibleSheaf l X).IsClosedUnderCokernels :=
  sorry

/-- **Finite products of constructible sheaves are constructible**: refine the
stratifications. -/
instance : (adicConstructibleSheaf l X).IsClosedUnderFiniteProducts :=
  sorry

/-- **Extensions of constructible sheaves are constructible**: on a common stratification an
extension of lisse sheaves is lisse, an extension of continuous representations of the
fundamental group being continuous. -/
instance : (adicConstructibleSheaf l X).IsClosedUnderExtensions :=
  sorry

end AlgebraicGeometry.ProEtale
