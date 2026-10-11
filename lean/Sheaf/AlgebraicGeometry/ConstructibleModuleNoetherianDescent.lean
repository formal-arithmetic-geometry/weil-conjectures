import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Noetherian descent of constructible module sheaves

Source: Stacks Project, Etale Cohomology, Lemma 09Z7 (proof, first paragraph)
(blueprint: lem-weil-pbc-constructible-module-noetherian-descent).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A constructible sheaf of modules on a quasi-compact, quasi-separated scheme descends
along a morphism to a constructible sheaf on a Noetherian scheme.
Source: Stacks Project, Etale Cohomology, Lemma 09Z7 (proof, first paragraph)
(blueprint: lem-weil-pbc-constructible-module-noetherian-descent).
Proof outline: (1) Noetherian approximation gives a cofiltered system of schemes of
finite type over `Spec ℤ` with affine transitions and limit `X`, using
`prop-nagata-noetherian-inverse-system` and `def-nagata-noetherian-inverse-system`.
(2) Reindex it by a directed set using
`lem-weil-pbc-cofiltered-limit-directed-reindex`.
(3) Each stage is Noetherian, hence quasi-compact and quasi-separated, by
`pqf-lem-locnoeth-lft` and `lem-weil-pbc-locally-noetherian-quasi-separated`.
(4) `lem-weil-pbc-constructible-module-limit-descent` descends `F` to a
constructible `F'` at one stage and supplies the displayed inverse-image isomorphism.
(5) Taking that stage as `X'` gives the existential conclusion. -/
theorem exists_noetherian_descent
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    ∃ (X' : Scheme.{u}), IsNoetherian X' ∧
      ∃ (ν : X ⟶ X') (F' : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        Scheme.IsConstructibleEtaleModuleSheaf F' ∧
          Nonempty (((ν)^*[ModuleCat.{u + 1} Λ]).obj F' ≅ F) := by
  sorry

end AlgebraicGeometry.Etale
