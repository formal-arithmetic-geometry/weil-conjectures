/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicOpenUnit
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Unbounded pro-etale direct image and open restriction

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-prop-sf-existence/prop-exc-base-change-proper.proof.md`, Step 3; Stacks
Project, `derived.tex`, Tag 08BJ and `proetale.tex`, Tag 09BN
(blueprint: lem-exc-proetale-derived-open-restriction).

The comparison reuses the canonical sectionwise restriction isomorphism of Q100.
Its derived component is normalized by the sectionwise equality on the fibre product;
the extension-by-zero clause records the exact open unit normalization.
Since this module imports `ProperExceptionalOpenBaseChange` (prop-exc-base-change-proper)
for that construction, the reverse proof-dependency import of this module there is
left out, as it would close an import cycle (stages/2-statements.md §3, rule 7).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The specified open restriction map, obtained from the sectionwise fibre-product
identification by K-injective derivation. This is exactly the restriction isomorphism
used by the proper/open comparison, with no properness hypothesis on `p`.
Source: blueprint Step 3; Stacks Tags 08BJ and 09BN
(blueprint: lem-exc-proetale-derived-open-restriction). -/
noncomputable def proEtaleOpenRestrictionComparison
    {V T W : Scheme.{u}} (p : V ⟶ T) (i : W ⟶ T) [IsOpenImmersion i]
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleConstantDerivedDirectImage p A ⋙ sfIntrinsicDerivedPullback A i ⟶
      sfIntrinsicDerivedPullback A (pullback.fst p i) ⋙
        proEtaleConstantDerivedDirectImage (pullback.snd p i) A :=
  (sfProperOpenDerivedRestriction A (pullback.snd p i) (pullback.fst p i) i p
    (IsPullback.of_hasPullback p i).flip).hom

/-- The inverse of the specified extension-by-zero normalization, with no freely chosen
isomorphism: apply `Rr_*` to the open unit and then apply inverse restriction at `k_!M`.
Thus its inverse is precisely `Rr_*(η_M⁻¹) ∘ ρ_{k_!M}`. The unit is that of the
canonical derived open adjunction, so every functor in this composite has the same
intrinsic constant-coefficient presentation.
Source: blueprint Step 3, final open-unit calculation; Stacks Tags 03DI and 09BN
(blueprint: lem-exc-proetale-derived-open-restriction). -/
noncomputable def proEtaleOpenRestrictionLambdaInverse
    {V T W : Scheme.{u}} (p : V ⟶ T) (i : W ⟶ T) [IsOpenImmersion i]
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleConstantDerivedDirectImage (pullback.snd p i) A ⟶
      sfIntrinsicDerivedOpen A (pullback.fst p i) ⋙
        proEtaleConstantDerivedDirectImage p A ⋙ sfIntrinsicDerivedPullback A i :=
  whiskerRight (exceptionalOpenAdjunction (pullback.fst p i) A).unit
      (proEtaleConstantDerivedDirectImage (pullback.snd p i) A) ≫
    whiskerLeft (sfIntrinsicDerivedOpen A (pullback.fst p i))
      (sfProperOpenDerivedRestriction A (pullback.snd p i) (pullback.fst p i) i p
        (IsPullback.of_hasPullback p i).flip).inv

/-- Unbounded open restriction and its extension-by-zero normalization.
For every finite commutative coefficient ring `A`, every morphism `p`, every open
immersion `i`, and every unbounded object `L`, the canonical comparison
`ρ_L : i^* Rp_* L ⟶ Rr_* k^* L` is an isomorphism and is natural in `L`.
The final clause asserts invertibility of the specified inverse of
the natural isomorphism
`λ_M : i^* Rp_* k_! M ≅ Rr_* M`; its normalization is the composite of `ρ` with
the inverse of the open adjunction unit. No properness, cohomological-dimension,
boundedness, or etale-origin hypothesis occurs. Source: blueprint Step 3;
Stacks Tags 08BJ and 09BN (blueprint: lem-exc-proetale-derived-open-restriction).

Proof (the node's five steps).
1. By lem-weil-pbc-open-immersion-base-change, `k` is an open immersion. Identify open
inverse image with restriction, including the constant ring sheaves
(lem-weil-proetale-weakly-etale-localization). For `Q ⟶ W` the direct-image formula of
def-weil-pbc-proetale-operations gives `(i^* p_* F)(Q) = F(V ×_T Q)` and
`(r_* k^* F)(Q) = F(U ×_W Q)`; the Cartesian identity `U = V ×_T W` (def-pc-fibre-product)
identifies these objects compatibly with restrictions, maps of `F` and the `A`-actions.
This is the sectionwise isomorphism `α_F`, applied degreewise to complexes.
2. `k_! ⊣ k^*` (lem-weil-extension-by-zero-adjunction) with `k_!` exact
(lem-weil-extension-by-zero-exact); by lem-weil-pbc-right-adjoint-preserves-kinjective,
`k^*` preserves K-injective complexes. No bound on degrees is used.
3. Represent `L` by `C ⟶ I` with `I` K-injective (prop-pur-kinjective-resolutions-exist,
small site by def-weil-pbc-proetale-site). Then `Rp_* L` is `p_* I`; exactness of `i^*`,
`k^*` gives `i^* p_* I` and `k^* I`. Since `k^* I` is K-injective it computes
`Rr_* k^* L` as `r_* k^* I` (lem-weil-pbc-kinjective-total-derived). The comparison is
represented by the degreewise isomorphism `α_I`, so `ρ_L` is an isomorphism.
4. Naturality and independence: derived maps between K-injectives are chain maps up to
homotopy (lem-weil-pbc-kinjective-hom-derived); the square of `α_I`, `α_J` with `h` commutes
sectionwise, and additive termwise functors preserve homotopies and homotopy equivalences.
5. Exact `k_!` (lem-weil-extension-by-zero-exact) and `k^*` act termwise on derived
categories; the open unit (lem-exc-proetale-open-unit) is a degreewise isomorphism, giving
`η_M : M ≅ k^* k_! M`. Then `λ_M = Rr_*(η_M⁻¹) ∘ ρ_{k_! M}` is a natural isomorphism, i.e.
its inverse `proEtaleOpenRestrictionLambdaInverse` is invertible. Only `k_! M` is resolved
on `V`; arbitrary opens and unbounded complexes are allowed throughout.
-/
theorem proEtaleDerivedOpenRestriction
    {V T W : Scheme.{u}} (p : V ⟶ T) (i : W ⟶ T) [IsOpenImmersion i]
    (A : Type u) [CommRing A] [Finite A] :
    IsIso (proEtaleOpenRestrictionComparison p i A) ∧
      (∀ L, IsIso ((proEtaleOpenRestrictionComparison p i A).app L)) ∧
      IsIso (proEtaleOpenRestrictionLambdaInverse p i A) := by
  -- The sheaf-level open unit makes extension by zero fully faithful.
  have : ∀ M, IsIso
      ((sfIntrinsicExtensionByZeroAdjunction (pullback.fst p i) A).unit.app M) :=
    fun M ↦ sfIntrinsicOpenUnit_isIso (pullback.fst p i) A M
  have : IsIso (sfIntrinsicExtensionByZeroAdjunction (pullback.fst p i) A).unit :=
    NatIso.isIso_of_isIso_app _
  let h :=
    (sfIntrinsicExtensionByZeroAdjunction (pullback.fst p i) A).fullyFaithfulLOfIsIsoUnit
  have := h.full
  have := h.faithful
  have : IsIso (sfIntrinsicOpenAdjunction A (pullback.fst p i)).unit := inferInstance
  -- Exact termwise derivation transports the unit isomorphism to the derived category.
  have : IsIso (exceptionalOpenAdjunction (pullback.fst p i) A).unit :=
    (exceptionalOpenAdjunction (pullback.fst p i) A).isIso_unit_of_iso
    ((mapDerivedCategoryCompIso (sfIntrinsicExtensionByZero (pullback.fst p i) A)
        (sfIntrinsicPullback A (pullback.fst p i))).symm ≪≫
      mapDerivedCategoryNatIso
        (asIso (sfIntrinsicOpenAdjunction A (pullback.fst p i)).unit).symm ≪≫
      mapDerivedCategoryIdIso _)
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [proEtaleOpenRestrictionComparison]
    infer_instance
  · intro L
    dsimp only [proEtaleOpenRestrictionComparison]
    infer_instance
  · dsimp only [proEtaleOpenRestrictionLambdaInverse]
    infer_instance

end AlgebraicGeometry.Scheme
