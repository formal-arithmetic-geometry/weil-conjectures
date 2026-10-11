import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Finite geometric stalks of constructible module sheaves

Source: Stacks Project, proof of Lemma 095N (line 12412 ff.), using Definitions 03RU and
03RW and Lemma 03Q1 (blueprint: lem-weil-pbc-constructible-module-finite-stalks).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- If a sheaf of modules on the small étale site is constructible, each geometric stalk is
finite, and hence finitely generated as a module over the finite coefficient ring.
Proof steps (blueprint dependencies): (1) choose the stratum through the image point using
`IsConstructibleEtaleModuleSheaf` and `def-constructible-stratification`; (2) factor the
geometric point through its immersion using `lem-weil-pbc-field-point-factors-through-immersion`;
(3) identify the inverse-image stalk with the original stalk by
`lem-weil-pbc-inverse-image-stalk-germ`; (4) apply
`lem-weil-pbc-finite-locally-constant-module-values` to obtain a finite stalk, using the
cofiltered pointed-neighbourhood and elementwise-colimit lemmas to compare module and
abelian-group stalks; (5) a finite module is finitely generated. Source: Stacks Project,
proof of Lemma 095N (line 12412 ff.) (blueprint: lem-weil-pbc-constructible-module-finite-stalks).
-/
theorem constructibleModule_finite_geometric_stalk
    {T : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ T) :
    Finite (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) ∧
      Module.Finite Λ (((pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
