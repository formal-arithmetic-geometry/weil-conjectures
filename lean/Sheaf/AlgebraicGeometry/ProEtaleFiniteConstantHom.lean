/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Module.FinitePresentation
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import Sheaf.CategoryTheory.SiteConstantModuleHom
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.LinearAlgebra.Pi
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage

/-! # Internal Hom and automorphisms of finite constant pro-etale modules

Source: current blueprint, sec-proetale-coefficients/sk-prop-pe-finite-local-systems,
`sk-prop-pe-finite-local-systems-hom.md`, clauses (1)--(3)
(blueprint: det-pe-finite-local-systems-hom).

Constant modules use the recorded module sheafification functor with its canonical
commutative-ring transport. The kernel is described sectionwise, including both
restriction naturality and naturality in the arbitrary target module sheaf.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Register Mathlib's explicitly constructed filtered group colimits.
Source: Mathlib, GrpCat.FilteredColimits.colimitCoconeIsColimit, used in the current
blueprint finite-local-systems Hom proof, paragraph (3)
(blueprint: det-pe-finite-local-systems-hom). -/
instance finiteConstantHomGrpFilteredColimits :
    HasFilteredColimitsOfSize.{u + 1, u + 1} GrpCat.{u + 1} where
  HasColimitsOfShape _I _ _ :=
    { has_colimit F := ⟨⟨⟨GrpCat.FilteredColimits.colimitCocone.{u + 1, u + 1} F,
        GrpCat.FilteredColimits.colimitCoconeIsColimit.{u + 1, u + 1} F⟩⟩⟩ }

/-- The same filtered colimits with the original site's smaller arrow universe.
Source: Mathlib's filtered-colimit universe transport, used in the current blueprint
finite-local-systems Hom proof, paragraph (3)
(blueprint: det-pe-finite-local-systems-hom). -/
instance finiteConstantHomGrpFilteredColimitsSite :
    HasFilteredColimitsOfSize.{u, u + 1} GrpCat.{u + 1} :=
  hasFilteredColimitsOfSize_of_univLE.{u, u + 1, u + 1, u + 1}

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- The comparison comma categories are filtered because the inclusion is flat.
Source: the existing representably flat site comparison, used in the current blueprint
finite-local-systems Hom proof, opening paragraph
(blueprint: det-pe-finite-local-systems-hom). -/
instance finiteConstantHomComparisonFiltered (V : X.ProEtᵒᵖ) :
    IsFiltered (CostructuredArrow (Scheme.toProEt X).op V) :=
  IsFiltered.of_equivalence (structuredArrowOpEquivalence (Scheme.toProEt X) V.unop)

/-- The genuine group-valued Kan extension exists by the filtered comma construction.
Source: Mathlib's pointwise Kan extension and filtered group colimits, used in the
current blueprint finite-local-systems Hom proof, paragraph (3)
(blueprint: det-pe-finite-local-systems-hom). -/
instance finiteConstantHomGrpPointwiseKan (F : X.Etaleᵒᵖ ⥤ GrpCat.{u + 1}) :
    (Scheme.toProEt X).op.HasPointwiseLeftKanExtension F :=
  fun _ ↦ inferInstance

/-- The constant commutative coefficient ring on the original small pro-etale site.
Source: current blueprint, finite-local-systems Hom detail, opening paragraph
(blueprint: det-pe-finite-local-systems-hom). -/
abbrev finiteConstantHomRing :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of Λ)

/-- The existing intrinsic category over the constant coefficient ring.
Source: current blueprint, finite-local-systems Hom detail, opening paragraph
(blueprint: det-pe-finite-local-systems-hom). -/
abbrev FiniteConstantHomModules :=
  ringedSiteModules.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (finiteConstantHomRing X Λ))

/-- The recorded constant-module functor; no second constant-module construction is made.
Source: current blueprint, finite-local-systems Hom detail, opening paragraph
(blueprint: det-pe-finite-local-systems-hom). -/
abbrev finiteConstantHomFunctor := constantModuleHomFunctor (Scheme.ProEt.topology X) Λ

/-- The scalar constant-section map, used for the coefficients of the transpose matrix.
Source: current blueprint, finite-local-systems Hom proof, paragraph (1)
(blueprint: det-pe-finite-local-systems-hom). -/
def finiteConstantHomScalar (U : X.ProEtᵒᵖ) : Λ →+* (finiteConstantHomRing X Λ).obj.obj U :=
  ((toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Λ))).app U).hom

/-- On sections the transpose sends `(x_i)` to `(sum_i a_ik x_i)_k`.
Source: current blueprint, finite-local-systems Hom detail, clause (1)
(blueprint: det-pe-finite-local-systems-hom). -/
def finiteConstantHomTranspose {m n : ℕ}
    (a : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ))
    (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ) :
    (Fin n → N.val.obj U) →ₗ[(finiteConstantHomRing X Λ).obj.obj U] (Fin m → N.val.obj U) :=
  LinearMap.pi fun k ↦ ∑ i : Fin n,
    finiteConstantHomScalar X Λ U (a (Pi.single k 1) i) • LinearMap.proj i

/-- The underlying set sheaf of an intrinsic module, using the existing forgetful functors.
Source: current blueprint, finite-local-systems Hom proof, opening paragraph
(blueprint: det-pe-finite-local-systems-hom). -/
abbrev finiteConstantHomUnderlying :
    FiniteConstantHomModules X Λ ⥤ Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  SheafOfModules.toSheaf _ ⋙ sheafCompose _ (forget AddCommGrpCat.{u + 1})

/-- The canonical composition map on constant set sheaves, obtained from the inverse
finite-product comparison and the ordinary composition function.
Source: current blueprint, finite-local-systems Hom proof, paragraph (2)
(blueprint: det-pe-finite-local-systems-hom). -/
def finiteConstantSetComposition (P Q T : ModuleCat.{u + 1} Λ) :
    (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj (P →ₗ[Λ] Q) ⨯
      (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj (Q →ₗ[Λ] T) ⟶
        (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj (P →ₗ[Λ] T) := by
  letI : PreservesFiniteLimits
      (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))) :=
    inferInstanceAs (PreservesFiniteLimits
      (Functor.const X.ProEtᵒᵖ ⋙ presheafToSheaf (Scheme.ProEt.topology X) (Type (u + 1))))
  exact inv (prodComparison (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (P →ₗ[Λ] Q) (Q →ₗ[Λ] T)) ≫
      (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).map
        ((Types.binaryProductIso (P →ₗ[Λ] Q) (Q →ₗ[Λ] T)).hom ≫
          (↾fun fg ↦ fg.2.comp fg.1))

/-- Pair two sections using the evaluation functor's finite-product comparison.
Source: current blueprint, finite-local-systems Hom proof, paragraph (2)
(blueprint: det-pe-finite-local-systems-hom). -/
def finiteConstantHomPair
    (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (U : X.ProEtᵒᵖ)
    (x : F.obj.obj U) (y : G.obj.obj U) : (F ⨯ G).obj.obj U :=
  (PreservesLimitPair.iso
    (sheafToPresheaf (Scheme.ProEt.topology X) (Type (u + 1)) ⋙
      (evaluation X.ProEtᵒᵖ (Type (u + 1))).obj U) F G).inv
        ((Types.binaryProductIso (F.obj.obj U) (G.obj.obj U)).inv (x, y))

/-- Composition of constant-module Hom sections, transported from composition of
constant set sections. The supplied set comparisons are characterized by their units
in the theorem below; they cannot be arbitrary maps.
Source: current blueprint, finite-local-systems Hom proof, paragraph (2)
(blueprint: det-pe-finite-local-systems-hom). -/
def finiteConstantModuleComposition
    (σ : ∀ M : ModuleCat.{u + 1} Λ,
      (finiteConstantHomUnderlying X Λ).obj ((finiteConstantHomFunctor X Λ).obj M) ≅
        (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj M)
    (P Q T : ModuleCat.{u + 1} Λ) (U : X.ProEtᵒᵖ)
    (f : ((finiteConstantHomFunctor X Λ).obj (ModuleCat.of Λ (P →ₗ[Λ] Q))).val.obj U)
    (g : ((finiteConstantHomFunctor X Λ).obj (ModuleCat.of Λ (Q →ₗ[Λ] T))).val.obj U) :
    ((finiteConstantHomFunctor X Λ).obj (ModuleCat.of Λ (P →ₗ[Λ] T))).val.obj U :=
  (σ (ModuleCat.of Λ (P →ₗ[Λ] T))).inv.hom.app U
    ((finiteConstantSetComposition X Λ P Q T).hom.app U
      (finiteConstantHomPair X _ _ U
        ((σ (ModuleCat.of Λ (P →ₗ[Λ] Q))).hom.hom.app U f)
        ((σ (ModuleCat.of Λ (Q →ₗ[Λ] T))).hom.hom.app U g)))

/-- A finite presentation gives the natural sectionwise kernel description of internal Hom.
The displayed basis-value formula specifies the canonical isomorphism. The following two
identities are its naturality for restriction and for every map of target sheaves.
Source: current blueprint, finite-local-systems Hom detail, clause (1)
(blueprint: det-pe-finite-local-systems-hom).
Proof, following steps 1--3 of the node:
1. Constant abelian sheafification is exact and preserves finite limits, by
   lem-pc-sites-module-sheafification-interface and lem-weil-pbc-sheafification-exact.
   The exact comparison inverse image of det-pe-classical-sheaves-modules gives the
   same constant module on the pro-etale site. Its free modules have the constant bases.
2. Restrict the presentation to each slice, using lem-weil-pbc-site-restriction-exact
   and lem-weil-pbc-module-sheaves-colimits-forgetful. A map from a finite free module
   is uniquely its tuple of basis values, also in rank zero.
3. The quotient is a cokernel by lem-weil-pbc-abelian-exact-epi-cokernel. A tuple factors
   through it exactly when every sum a_ik x_i vanishes. Cokernel uniqueness proves both
   naturality identities. This argument does not assume exactness of sections. -/
theorem finiteConstantHom_presentation {m n : ℕ}
    (M : ModuleCat.{u + 1} Λ)
    (a : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ)) (b : (Fin n → Λ) →ₗ[Λ] M)
    (hexact : Function.Exact a b) (hsurjective : Function.Surjective b) :
    ∃ e : ∀ (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ),
      (SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
        ((finiteConstantHomFunctor X Λ).obj M) N).val.obj U ≃ₗ[
          (finiteConstantHomRing X Λ).obj.obj U]
            LinearMap.ker (finiteConstantHomTranspose X Λ a N U),
      (∀ (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ)
          (φ : (SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
            ((finiteConstantHomFunctor X Λ).obj M) N).val.obj U) (i : Fin n),
        (e N U φ).1 i = (φ.app (op (Over.mk (𝟙 U.unop))))
          ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U
            (b (Pi.single i 1)))) ∧
      (∀ (N : FiniteConstantHomModules X Λ) (U V : X.ProEtᵒᵖ) (f : U ⟶ V)
          (φ : (SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
            ((finiteConstantHomFunctor X Λ).obj M) N).val.obj U) (i : Fin n),
        (e N V ((SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
          ((finiteConstantHomFunctor X Λ).obj M) N).val.map f φ)).1 i =
            N.val.map f ((e N U φ).1 i)) ∧
      (∀ (N N' : FiniteConstantHomModules X Λ) (g : N ⟶ N') (U : X.ProEtᵒᵖ)
          (φ : (SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
            ((finiteConstantHomFunctor X Λ).obj M) N).val.obj U) (i : Fin n),
        (e N' U ((SheafOfModules.homObjMap (R := finiteConstantHomRing X Λ)
          (𝟙 ((finiteConstantHomFunctor X Λ).obj M)) g).val.app U φ)).1 i =
            g.val.app U ((e N U φ).1 i)) := by
  sorry

/-- The canonical constant Hom comparison is invertible for two finitely presented
modules, and preserves composition on all sections and identity. The set comparisons
are fixed by their constant-section units, as is the linear comparison.
Source: current blueprint, finite-local-systems Hom detail, clause (2)
(blueprint: det-pe-finite-local-systems-hom).
Proof, following steps 1 and 4--6 of the node:
1. Abelian module sheafification and set sheafification agree on underlying sets by
   lem-pc-sites-sheafification-underlying-sets; their units give the displayed σ.
2. Apply the finite-product-preserving constant set functor to evaluation. Its
   linearity identities give the comparison, sending a constant f to C(f) on slices.
3. The presentation calculation identifies ordinary Hom with the finite kernel
   Q^n → Q^m. Exactness and finite-limit preservation of constant modules identify
   its sheafification with the kernel in clause (1). The coordinates agree by
   evaluation at b(e_i), proving invertibility. This is also the recorded
   lem-pur-site-constant-module-hom comparison.
4. Apply the constant set functor to ev(g comp f,x) = ev(g,ev(f,x)). Equality on
   every slice gives the displayed composition equation for arbitrary sections.
   The identity follows by applying it to ev(id,x) = x. -/
theorem finiteConstantHom_constant :
    ∃ σ : ∀ M : ModuleCat.{u + 1} Λ,
      (finiteConstantHomUnderlying X Λ).obj ((finiteConstantHomFunctor X Λ).obj M) ≅
        (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj M,
      (∀ (M : ModuleCat.{u + 1} Λ) (U : X.ProEtᵒᵖ) (x : M),
        (σ M).hom.hom.app U
          ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U x) =
            (toSheafify (Scheme.ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (M : Type (u + 1)))).app U x) ∧
      ∃ c : ∀ P Q : ModuleCat.{u + 1} Λ,
        (finiteConstantHomFunctor X Λ).obj (ModuleCat.of Λ (P →ₗ[Λ] Q)) ⟶
          SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
            ((finiteConstantHomFunctor X Λ).obj P) ((finiteConstantHomFunctor X Λ).obj Q),
        (∀ (P Q : ModuleCat.{u + 1} Λ) (U : X.ProEtᵒᵖ) (f : P →ₗ[Λ] Q),
          (c P Q).val.app U
            ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ
              (ModuleCat.of Λ (P →ₗ[Λ] Q))).app U f) =
                (PresheafOfModules.restrictOver (finiteConstantHomRing X Λ).obj U.unop).map
                  (((finiteConstantHomFunctor X Λ).map (ModuleCat.ofHom f)).val)) ∧
        (∀ (P Q : ModuleCat.{u + 1} Λ) [Module.FinitePresentation Λ P]
          [Module.FinitePresentation Λ Q], IsIso (c P Q)) ∧
        (∀ (P Q T : ModuleCat.{u + 1} Λ) [Module.FinitePresentation Λ P]
          [Module.FinitePresentation Λ Q] [Module.FinitePresentation Λ T]
          (U : X.ProEtᵒᵖ)
          (f : ((finiteConstantHomFunctor X Λ).obj (ModuleCat.of Λ (P →ₗ[Λ] Q))).val.obj U)
          (g : ((finiteConstantHomFunctor X Λ).obj (ModuleCat.of Λ (Q →ₗ[Λ] T))).val.obj U),
          (c P T).val.app U (finiteConstantModuleComposition X Λ σ P Q T U f g) =
            (c P Q).val.app U f ≫ (c Q T).val.app U g) ∧
        (∀ (P : ModuleCat.{u + 1} Λ) [Module.FinitePresentation Λ P] (U : X.ProEtᵒᵖ),
          (c P P).val.app U
            ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ
              (ModuleCat.of Λ (P →ₗ[Λ] P))).app U LinearMap.id) = 𝟙 _) := by
  sorry

/-- The automorphism sheaf is characterized by the actual groups of automorphisms on
slices and their restriction maps. Its constant group comparison is specified on every
constant automorphism, and it is the inverse image of the constant etale group sheaf.
Classicality is the recorded continuity predicate on the underlying set sheaf.
Source: current blueprint, finite-local-systems Hom detail, clause (3)
(blueprint: det-pe-finite-local-systems-hom).
Proof, following steps 1 and 7--8 of the node:
1. In End(M) squared take pairs (f,g) with fg = gf = 1. This is a finite equalizer
   of sets, not a submodule. By lem-weil-pbc-site-sheaf-sets-limits-sectionwise the
   same equalizer for local sheaf endomorphisms is a sheaf; it is precisely the
   groups of automorphisms on slices. Restriction acts on both inverse maps.
2. The Hom comparison of clause (2), including composition and identity, identifies
   this equalizer with the constant inverse-pair set. Projection identifies it with
   Aut(M). Multiplication is (f,g)(h,k) = (fh,kg), so the comparison preserves the
   group law and has the stated formula on constant automorphisms.
3. Constant etale sheaves pull back to constant pro-etale sheaves: both constant
   functors are left adjoint to global sections, since the inclusion of sites
   preserves their terminal object. The same statement holds for groups, giving
   the displayed group-sheaf isomorphism with the actual comparison inverse image.
4. Apply det-pe-classical-sheaves-image to its underlying sheaf of sets: this is in
   the comparison essential image, hence every affine-presentation continuity map
   is bijective. No finiteness or commutativity of Aut(M) is required. -/
theorem finiteConstantHom_automorphisms (M : ModuleCat.{u + 1} Λ)
    [Module.FinitePresentation Λ M] :
    ∃ A : Sheaf (Scheme.ProEt.topology X) GrpCat.{u + 1},
      ∃ e : ∀ U : X.ProEtᵒᵖ, A.obj.obj U ≃*
        Aut ((PresheafOfModules.restrictOver (finiteConstantHomRing X Λ).obj U.unop).obj
          ((finiteConstantHomFunctor X Λ).obj M).val),
        (∀ (U V : X.ProEtᵒᵖ) (f : U ⟶ V) (x : A.obj.obj U) (W : (Over V.unop)ᵒᵖ),
          (e V (A.obj.map f x)).hom.app W =
            (e U x).hom.app (op ((Over.map f.unop).obj W.unop))) ∧
        (∃ α : A ≅ (constantSheaf (Scheme.ProEt.topology X) GrpCat.{u + 1}).obj
            (GrpCat.of (Aut M)),
          ∀ (U : X.ProEtᵒᵖ) (a : Aut M),
            e U (α.inv.hom.app U
              ((toSheafify (Scheme.ProEt.topology X)
                ((Functor.const X.ProEtᵒᵖ).obj (GrpCat.of (Aut M)))).app U a)) =
              (PresheafOfModules.restrictOver (finiteConstantHomRing X Λ).obj U.unop).mapIso
                ((SheafOfModules.forget _).mapIso ((finiteConstantHomFunctor X Λ).mapIso a))) ∧
        Nonempty (A ≅
          (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X) GrpCat.{u + 1}
            X.smallEtaleTopology (Scheme.ProEt.topology X)).obj
              ((constantSheaf X.smallEtaleTopology GrpCat.{u + 1}).obj (GrpCat.of (Aut M)))) ∧
        IsClassical ((sheafCompose (Scheme.ProEt.topology X) (forget GrpCat.{u + 1})).obj A) := by
  sorry

end AlgebraicGeometry.ProEtale
