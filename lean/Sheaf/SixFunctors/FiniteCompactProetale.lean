module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal
import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
import Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.AlgebraicGeometry.UnboundedSiteComparison
import Sheaf.CategoryTheory.CompactObject
import Sheaf.Paper.FiniteComparisonLocalizing
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.ConstructibleSheaf.Refinement

/-!
# Compactness of finite constructible pro-etale complexes

Source: Weil conjectures blueprint main-20261015, `sec-six-functors-basics`,
`sk-prop-ctf-finite-compact/sk-prop-ctf-finite-compact-proetale.md` and its proof
`sk-prop-ctf-finite-compact-proetale.proof.md`
(blueprint: det-ctf-finite-compact-proetale).

The ambient category is the unbounded derived category of module objects over the
pulled-back condensed ring `A_X` of a finite discrete `ℓ`-primary ring `A`.  The
compactness map is the one of `CategoryTheory.IsCompactObject`
(blueprint: def-pc-compact-object), written out for one family with an ambient coproduct,
because the localizing closure is a full subcategory with the ambient coproducts.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry Scheme DirectSum

namespace WeilConjectures

open Classical in
/-- Every bounded constructible finite-Tor pro-etale complex `C` is compact in the
localizing closure `Loc(Dctf(X, A))`: for every family `E` of objects of the closure, with
its ambient coproduct `∐ E` (again in the closure), the canonical map
`⨁ᵢ Hom(C, E i) → Hom(C, ∐ E)`, `f ↦ f ≫ Sigma.ι E i` on the `i`-th summand, is bijective.

Source: blueprint main-20261015, `sk-prop-ctf-finite-compact/`
`sk-prop-ctf-finite-compact-proetale.md` and `.proof.md`
(blueprint: det-ctf-finite-compact-proetale).

Proof (the node's steps).
1. By `lem-weil-pbc-finite-discrete-condensed-ring-constant` and
   `lem-weil-pbc-finite-discrete-scheme-ring-constant`, `θ : A_const ≅ A_X`; transporting
   actions along `θ` identifies the module categories, their derived categories, coproducts,
   derived tensor products and finite constant local models, so the constructibility and
   Tor conventions agree with the constant-`A` ones of `det-ctf-finite-comparison-localizing`.
2. `X` is quasi-compact and quasi-separated (finite affine cover by finitely generated
   `k`-algebras, ascending chain condition on opens, `lem-wf-affine-noetherian-components`),
   and the finite ring `A` is Noetherian; the empty scheme and the zero ring are included.
3. By `lem-sfb-unbounded-site-comparison`, `F = ν_X^*` is exact, fully faithful and preserves
   small coproducts; by `det-pe-finite-tor-comparison-noetherian` there is
   `C₀ ∈ Dctf(X_et, A)` with `c : F C₀ ≅ C`.
4. Via `def-pe-etale-constructible-module`, `lem-weil-pbc-finite-locally-constant-module-values`,
   `lemma-constructible-immersion-independence` and `lem-weil-pbc-constructible-qcqs-affine-local`
   (Stacks 095E), `C₀` lies in the étale `Dctf` of `det-ctf-finite-compact-etale`, hence is
   compact against all ordinary unbounded étale objects.
5. By the first clause of `det-ctf-finite-comparison-localizing`, choose étale `M_i` with
   `a_i : F M_i ≅ E i`; coproduct preservation gives `a : F (∐ M_i) ≅ ∐ E` with
   `a ∘ F ι_i = ι_i ∘ a_i`.
6. `u ↦ a_i F(u) c⁻¹` and `v ↦ a F(v) c⁻¹` are bijections on Hom groups which carry the étale
   compactness map to the displayed map (`a F(ι_i u) c⁻¹ = ι_i a_i F(u) c⁻¹`, then additivity);
   so the displayed map is bijective.  The empty family, `C = 0`, `A = 0` and `X = ∅` give
   zero groups. -/
theorem finiteCompactProEtale
    (D : FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    (A : Type) [CommRing A] (hA : Finite A)
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (r : ℕ) (hr : ∀ a : A, (ℓ ^ r) • a = 0) :
    ∀ (C : DerivedCategory
        (AlgebraicGeometry.ProEtale.pulledBackModuleObjects
          (Profinite.continuousMapRingObj A) X)),
      (AlgebraicGeometry.ProEtale.constantModelBoundedConstructible
          (Profinite.continuousMapRingObj A) X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K) C →
      ∀ (I : Type w)
        (E : I → DerivedCategory
          (AlgebraicGeometry.ProEtale.pulledBackModuleObjects
            (Profinite.continuousMapRingObj A) X)) [hE : HasCoproduct E],
        (∀ i, AlgebraicGeometry.ProEtale.localizingClosureProEtale
          (Profinite.continuousMapRingObj A) X (E i)) →
        AlgebraicGeometry.ProEtale.localizingClosureProEtale
          (Profinite.continuousMapRingObj A) X (∐ E) →
        Function.Bijective
          (DirectSum.toAddMonoid
            (fun i : I => Preadditive.rightComp C (Sigma.ι E i)) :
            (⨁ i : I, (C ⟶ E i)) →+ (C ⟶ ∐ E)) := by
  sorry

end WeilConjectures
