/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemGammaProjectionTransport
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.SixFunctors.Coefficient.CoefficientHomZeroClass

/-! # Degree-zero coefficient gamma projection transport

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 08JA, 0D6E and 0941;
the H⁰ specialization of `enrichedSequenceProjectionFormula`
(blueprint: lem-coef-derived-system-hom-projection-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The finite projection of gamma acts on H⁰ by scalar extension and the finite
counit, after the specified evaluation transports.

Here Q is the total limit, M its finite evaluation, ρ the comparison at P, σ the
inverse comparison at Q, and ε the evaluated counit. The map γ is the actual
projected global-Hom map: `hγ` specifies its factorization through the projection
π and the scalar enriched map b. `hb` is the scalar Hom-zero normalization before
any system limit. Neither hypothesis asserts the conclusion about γ.

Source: Stacks 07A6, 08JA and 0941; the degree-zero calculation of the enriched
sequence projection identity (blueprint: lem-coef-derived-system-hom-projection-transport).

Proof: apply H⁰ to hγ. Naturality of the canonical finite Hom-zero equivalence
turns the last map into precomposition by ρ. Apply hb. Naturality of the integral
Hom-zero equivalence turns the first map into postcomposition by π. Substitute
hπ and use left naturality of the scalar adjunction to cancel its Hom bijection.
The resulting composite is ρ followed by F(h), σ and ε. No normalization,
boundedness or nonzero-object condition is used in this formal transport step. -/
theorem coefficientDerivedSystemHomProjectionTransport
    (F : (DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v
      u} RingCat.{max c v u})).obj R))) ⥤ (DerivedCategory (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj B)))) (G :
      (DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v u}
      RingCat.{max c v u})).obj B))) ⥤ (DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)))) (adj : F ⊣ G)
    (P Q : (DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c
      v u} RingCat.{max c v u})).obj R)))) (V VQ M : (DerivedCategory (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj B)))) (ρ : V ≅
      F.obj P) (σ : F.obj Q ≅ VQ)
    (ε : VQ ⟶ M) (π : Q ⟶ G.obj M)
    (hπ : π = adj.homEquiv Q M (σ.hom ≫ ε))
    (b : (coefficientGlobalSections.{u, c, v, w} J R).obj ((derivedInternalHomOfUniverses.{c, v, u,
      w} J R).obj (op P, G.obj M)) ⟶ (coefficientGlobalSections.{u, c, v, w} J B).obj
      ((derivedInternalHomOfUniverses.{c, v, u, w} J B).obj (op (F.obj P), M)))
    (hb : ∀ x, (coefficientHomZeroEquiv.{u, c, v, w} J B) (F.obj P) M
      ((@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _ (HasDerivedCategory.standard
      _) 0).map b x) =
      (adj.homEquiv P M).symm ((coefficientHomZeroEquiv.{u, c, v, w} J R) P (G.obj M) x))
    (γ : (coefficientGlobalSections.{u, c, v, w} J R).obj ((derivedInternalHomOfUniverses.{c, v, u,
      w} J R).obj (op P, Q)) ⟶ (coefficientGlobalSections.{u, c, v, w} J B).obj
      ((derivedInternalHomOfUniverses.{c, v, u, w} J B).obj (op V, M)))
    (hγ : γ = (coefficientGlobalSections.{u, c, v, w} J R).map ((derivedInternalHomOfUniverses.{c,
      v, u, w} J R).map (Prod.mkHom (𝟙 (op P)) π)) ≫ b ≫
      (coefficientGlobalSections.{u, c, v, w} J B).map ((derivedInternalHomOfUniverses.{c, v, u, w}
        J B).map (Prod.mkHom ρ.hom.op (𝟙 M)))) (h : P ⟶ Q) :
    (coefficientHomZeroEquiv.{u, c, v, w} J B) V M ((@DerivedCategory.homologyFunctor
      AddCommGrpCat.{max c v u} _ _ (HasDerivedCategory.standard _) 0).map γ
      (((coefficientHomZeroEquiv.{u, c, v, w} J R) P Q).symm h)) =
      ρ.hom ≫ F.map h ≫ σ.hom ≫ ε := by
  let H₀ := @DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
    (HasDerivedCategory.standard _) 0
  let ΦR := coefficientHomZeroEquiv.{u, c, v, w} J R
  let ΦB := coefficientHomZeroEquiv.{u, c, v, w} J B
  change ΦB V M (H₀.map γ ((ΦR P Q).symm h)) = _
  have hi := (coefficientHomZeroEquiv_exists.{u, c, v, w} J R).choose_spec.1.1
  have hf := (coefficientHomZeroEquiv_exists.{u, c, v, w} J B).choose_spec.1.1
  rw [hγ]
  simp only [Functor.map_comp, AddCommGrpCat.comp_apply]
  let x := H₀.map ((coefficientGlobalSections.{u, c, v, w} J R).map
    ((derivedInternalHomOfUniverses.{c, v, u, w} J R).map
      (Prod.mkHom (𝟙 (op P)) π))) ((ΦR P Q).symm h)
  have hfin := hf (F.obj P) M V M ρ.hom (𝟙 M) (H₀.map b x)
  change ΦB V M (H₀.map ((coefficientGlobalSections.{u, c, v, w} J B).map
    ((derivedInternalHomOfUniverses.{c, v, u, w} J B).map
      (Prod.mkHom ρ.hom.op (𝟙 M)))) (H₀.map b x)) =
    ρ.hom ≫ ΦB (F.obj P) M (H₀.map b x) ≫ 𝟙 M at hfin
  rw [hfin, hb]
  have hx : ΦR P (G.obj M) x = h ≫ π := by
    have hx := hi P Q P (G.obj M) (𝟙 P) π ((ΦR P Q).symm h)
    simpa only [x, H₀, ΦR, coefficientHomZeroEquiv, AddEquiv.apply_symm_apply,
      Category.id_comp, op_id] using hx
  rw [hx, hπ, ← adj.homEquiv_naturality_left]
  simp only [Equiv.symm_apply_apply, Category.comp_id]

end WeilConjectures
