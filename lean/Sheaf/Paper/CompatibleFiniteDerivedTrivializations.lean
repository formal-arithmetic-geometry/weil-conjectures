/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.DerivedLocalIsomorphismSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.ConstructibleSheaf.Defs
import Sheaf.AlgebraicGeometry.FiniteLisseTowerSectionCover
import Sheaf.Paper.NormalizedDerivedIsomorphismSectionReduction

/-! # Compatible finite derived trivializations

Source: Stacks Project, Tag 09BV, inverse isomorphism sheaves and stable images;
bounded-derived adaptation from the proper-base-change blueprint
(blueprint: lem-weil-pbc-compatible-finite-derived-trivializations).

Index `n : ℕ` means level `n + 1`. Normalization isomorphisms are encoded by their
universal arrows to exact restriction of scalars. By derived extension/restriction
adjunction, this is equivalent to specifying the isomorphisms in the node, with their
canonical iterated quotient cocycles. The compatibility square below is the adjunct
of the displayed equation rho ∘ (e ⊗ᴸ B_n) ∘ eta⁻¹ = e_n.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Finite derived local systems with specified coefficient normalizations admit a common
pro-etale trivializing covering compatible with every normalization. There is no assumption
that the reduction maps on isomorphism sheaves are surjective, and bounds may depend on n.

Source: Stacks Project, Tag 09BV, adapted to the finite derived isomorphism sheaves in the
proper-base-change blueprint
(blueprint: lem-weil-pbc-compatible-finite-derived-trivializations).

Proof:
1. Cover X by affine opens V. Represent each finite locally constant isomorphism sheaf
   on V by a finite etale V-scheme P_n (finite-locally-constant-sets-representability).
   Yoneda turns reduction into V-maps P_(n+1) -> P_n, with the same composite reductions.
2. Write P_n = Spec A_n and take Spec(colim A_n). The affine limit/colimit comparison
   supplies its projections. The algebra is ind-etale, hence the limit is weakly etale;
   compose with the open immersion V -> X. The countable colimit stays in the site universe.
3. At each geometric point, the stalks of the isomorphism sheaves are finite nonempty sets.
   Images from later stages stabilize separately at each level. Their stable-image subsets
   are nonempty with surjective consecutive maps: choose a stage beyond both stabilizations
   to lift a given stable element. Their inverse limit is nonempty. Stalk germs give compatible
   geometric points of the P_n, hence a geometric point of their affine inverse limit.
   Thus the affine weakly etale limit surjects onto V and is a singleton pro-etale cover.
4. The universal sections over P_n and the limit projections give compatible sections of
   the comparison pullbacks of the isomorphism sheaves, using the actual comma-colimit
   formula for comparison inverse image. No inverse-limit preservation is used.
5. Refine this cover by affine objects weakly contractible for the full pro-etale site,
   and compose with the affine-open cover of X. Restriction preserves all section equations.
6. The derived-isomorphism-sheaf weakly-contractible evaluation bijection turns these
   sections into actual local derived isomorphisms. Its compatibility with composition and
   scalar extension, together with tensor/pullback comparison, identifies section reduction
   with rho ∘ (e ⊗ᴸ B_n) ∘ eta⁻¹. Under the universal-arrow adjunction this is exactly the
   displayed normalization square. Boundedness after reduction follows from rho and eta;
   finite Tor dimension and a uniform bound are unnecessary. For empty X use the empty cover.
-/
theorem compatible_finite_derived_trivializations
    (X : Scheme.{u}) (B : ℕ → Type (u + 1)) [∀ n : ℕ, CommRing (B n)]
    [∀ n : ℕ, Finite (B n)] (q : ∀ n : ℕ, B (n + 1) →+* B n)
    (hq : ∀ n : ℕ, Function.Surjective (q n))
    (E : ∀ n : ℕ, DerivedCategory (ModuleCat.{u + 1} (B n)))
    (K : ∀ n : ℕ, DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (B n))))
    (dE : ∀ n : ℕ, E (n + 1) ⟶ (normalizationModuleRestrict (q n)).obj (E n))
    (dK : ∀ n : ℕ, K (n + 1) ⟶
      (normalizationRestrict X.smallEtaleTopology (q n)).obj (K n))
    (hE : ∀ n : ℕ, ∃ a b : ℤ, (E n).IsGE a ∧ (E n).IsLE b)
    (hK : ∀ n : ℕ, ∃ a b : ℤ, (K n).IsGE a ∧ (K n).IsLE b)
    (hEf : ∀ (n : ℕ) (i : ℤ), Module.Finite (B n)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (B n)) i).obj (E n)))
    (hKf : ∀ (n : ℕ) (i : ℤ), IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (B n))) i).obj (K n)))
    (hη : ∀ n : ℕ, Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk (dE n))))
    (hρ : ∀ n : ℕ, Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk (dK n))))
    (hI : ∀ n : ℕ, IsLisseEtaleSheafOfSets
      (derivedLocalIsomorphismSheaf ((normalizationConstant X.smallEtaleTopology).obj (E n))
        (K n)))
    (hInonempty : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ X), Nonempty ((pointSmallEtale s).sheafFiber.obj
        (derivedLocalIsomorphismSheaf ((normalizationConstant X.smallEtaleTopology).obj (E n))
          (K n)))) :
    ∃ (𝒰 : Cover.{u} proetalePrecoverage X)
      (e : ∀ (j : 𝒰.I₀) (n : ℕ),
        (localProEtaleComparison (𝒰.f j) (B n)).obj
            ((normalizationConstant X.smallEtaleTopology).obj (E n)) ≅
          (localProEtaleComparison (𝒰.f j) (B n)).obj (K n)),
      ∀ (j : 𝒰.I₀) (n : ℕ),
        (e j (n + 1)).hom ≫ localProEtaleNormalization (𝒰.f j) (q n) (dK n) =
          localProEtaleNormalization (𝒰.f j) (q n)
              (normalizationConstantArrow X.smallEtaleTopology (q n) (dE n)) ≫
            (normalizationRestrict (ProEt.topology (𝒰.X j)) (q n)).map (e j n).hom := by
  classical
  have _ := hq
  have _ := hE
  have _ := hK
  have _ := hEf
  have _ := hKf
  obtain ⟨r, hev⟩ := normalized_derived_isomorphism_section_reduction X B q E K dE dK hη hρ
  obtain ⟨J, U, hcov, ha, hw, s, hs⟩ := finite_lisse_tower_section_cover X
    (fun n ↦ derivedLocalIsomorphismSheaf
      ((normalizationConstant X.smallEtaleTopology).obj (E n)) (K n)) r hI hInonempty
  let 𝒰 : Cover.{u} proetalePrecoverage X :=
    ⟨⟨J, fun j ↦ (U j).left, fun j ↦ (U j).hom⟩, hcov⟩
  refine ⟨𝒰, fun j n ↦ sourceDerivedIsoEvaluation X (B n)
    ((normalizationConstant X.smallEtaleTopology).obj (E n)) (K n)
    (U j) (ha j) (hw j) (s j n), ?_⟩
  intro j n
  have h := hev n (U j) (ha j) (hw j) (s j (n + 1))
  rw [hs j n] at h
  exact h

end AlgebraicGeometry.Scheme
