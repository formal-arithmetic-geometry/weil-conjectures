module

public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent
import WeilConjectures.AlgebraicGeometry.AffineEtaleBaseChangeSystem
import WeilConjectures.AlgebraicGeometry.EtaleFiniteCoverFactorizationDescent
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-! # Finite local systems descend along affine inverse limits

Source: Stacks Project, Etale Cohomology, Tag 0GL2,
`lemma-category-loc-cst-is-colimit`, part (3), essential surjectivity for finite rings
(blueprint: lem-sfb-finite-local-system-affine-limit-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A finite locally constant module sheaf on a qcqs affine-transition inverse limit
descends to a finite locally constant module sheaf at a stage. Both local-constancy
conditions explicitly use finite module values on the localized small etale sites.
The isomorphisms, including the final inverse-image isomorphism, are module-linear.
There is no Noetherian hypothesis on any scheme.

Source: Stacks Project, Tag 0GL2, `lemma-category-loc-cst-is-colimit`, part (3)
(blueprint: lem-sfb-finite-local-system-affine-limit-descent).

Proof:
1. The projections are affine (`lem-weil-pbc-limit-affine-transition`), so the
   nonempty system and qcqs permanence make the limit qcqs
   (`lem-weil-pbc-affine-morphism-permanence`, `lem-weil-pbc-qcqs-morphism-permanence`).
   The one-stratum partition makes F constructible
   (`def-weil-pbc-etale-constructible-sheaf`); descend it by
   `lem-weil-pbc-constructible-module-limit-descent` to a constructible model F_i.
2. Take a finite affine open cover of X_i (`lem-weil-pbc-qcqs-finite-affine-open-cover`).
   Its inverse images are affine. On each, refine the given trivializing cover to a
   finite affine etale cover (`lem-weil-pbc-etale-covering-affine-refinement`).
   Restrict the trivializations using `lemma-constructible-pullback-constant` and
   `lem-pe-constant-left-module-inverse-image`; there are finitely many local models.
3. Descend these covers by `lem-weil-pbc-etale-finite-cover-factorization-descent`,
   with terminal auxiliary targets. Directedness gives one common stage j.
   Covering preservation (`lem-weil-pbc-affine-etale-base-change-system`) makes the
   combined family an etale cover of X_j. Pull F_i back to F_j.
4. On every descended cover member compare the restriction of F_j with its prescribed
   finite constant module sheaf. Both are constructible, using
   `lem-weil-pbc-constructible-etale-module-sheaf-comparison` and
   `prop-constructible-pullback`. Their pullbacks to the limit are isomorphic by the
   chosen trivialization. The relevant base-change system has that cover member as
   limit (`lem-weil-pbc-scheme-over-limit`). Constant pullback and inverse-image
   composition identify the objects (`lemma-constructible-pullback-constant`,
   `lem-pe-constant-left-module-inverse-image`, `lem-weil-pbc-inverse-image-composition`).
5. Descend both this isomorphism and its inverse by clause (1) of
   `lem-sfb-constructible-module-affine-limit-hom`. Take a common upper bound for all
   resulting stages. Use the module inverse-image composition comparisons throughout.
6. Apply clause (2) of the same morphism-descent lemma to each of the two inverse
   identities. Constructible pullback and its module-sheaf comparison apply at later
   stages as well. A common upper bound makes both identities hold on every cover
   member, so the descended maps are module-sheaf isomorphisms.
7. The family remains covering after base change. The finite constant-value
   isomorphisms certify local constancy in precisely the original sense
   (`def-constructible-locally-constant`). Inverse-image composition identifies the
   pullback of the global descended sheaf with F. No gluing of trivializations is
   needed, since the sheaf itself was descended in step 1.
-/
theorem exists_finite_localSystem_affineLimit_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∃ d : LocallyConstantDatum F, ∀ a : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty (F.over (d.cover.etalePrecoverageToEtale a) ≅
          (constantSheaf
            (c.pt.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale a))
            (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ (i : I) (Fᵢ : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∃ d : LocallyConstantDatum Fᵢ, ∀ a : d.cover.I₀,
        ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty (Fᵢ.over (d.cover.etalePrecoverageToEtale a) ≅
            (constantSheaf
              ((D.obj (op i)).smallEtaleTopology.over (d.cover.etalePrecoverageToEtale a))
              (ModuleCat.{u + 1} Λ)).obj M)) ∧
      Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj Fᵢ ≅ F) := by
  sorry

end AlgebraicGeometry.Scheme
