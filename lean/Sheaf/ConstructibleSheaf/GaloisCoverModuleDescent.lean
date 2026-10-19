/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.CategoryTheory.Action.Monoidal
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceDegree
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Mathlib.CategoryTheory.Galois.GaloisObjects
import Sheaf.CategoryTheory.Galois.StacksGaloisCategory
import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
import WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant
import Sheaf.CategoryTheory.SetSheafCoverDescent
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.FiniteTypeConstantExact
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Mathlib.CategoryTheory.Sites.CoverLifting
import Sheaf.AlgebraicGeometry.FiniteEtaleFiniteLimits

/-! # Arbitrary-coefficient module descent along a finite Galois cover

Source: ILO, Travaux de Gabber, Expose XVII, 7.2.3 and 7.4.6; Stacks Project,
Tags 04TR, 04TQ, 093J and 0GMW (blueprint: lem-per-galois-cover-module-descent).

We use the small model of the small etale site. Mixed tensors are written in the
canonically associated form `N ⊗_A (A ⊗_R V)`. This retains their A-module structure;
the usual balanced tensor associativity identifies this with `N ⊗_R V`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open SheafOfModules

namespace AlgebraicGeometry.GaloisModuleDescent

/-- Small representative of the etale site, as in the size convention in Step 1.
Source: Stacks 00XZ (blueprint: lem-per-galois-cover-module-descent). -/
abbrev Site (S : Scheme.{u}) := SmallModel.{u + 1, u, u + 1} S.Etale

/-- The existing small-model category, with all universes fixed explicitly.
Source: Stacks 00XZ (blueprint: lem-per-galois-cover-module-descent). -/
noncomputable instance siteCategory (S : Scheme.{u}) : SmallCategory (Site S) :=
  smallCategorySmallModel.{u + 1, u, u + 1} S.Etale

/-- The etale topology transported to the small representative.
Source: Stacks 00XZ (blueprint: lem-per-galois-cover-module-descent). -/
noncomputable def topology (S : Scheme.{u}) : GrothendieckTopology (Site S) :=
  (equivSmallModel.{u + 1} S.Etale).inverse.inducedTopology S.smallEtaleTopology


/-- Constant-coefficient module sheaves on the small etale representative.
Source: Stacks 093J (blueprint: lem-per-galois-cover-module-descent). -/
abbrev Modules (S : Scheme.{u}) (R : CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1} (constantCoefficientRing (topology S) R)

/-- The object of the small site represented by the finite etale cover.
Source: ILO XVII 7.4.6 (blueprint: lem-per-galois-cover-module-descent). -/
noncomputable def coverObject {S : Scheme.{u}} (c : S.FiniteEtale) : Site S :=
  (equivSmallModel.{u + 1} S.Etale).functor.obj c.obj

/-- A deck transformation regarded as a morphism of the small site.
Source: ILO XVII 7.4.6 (blueprint: lem-per-galois-cover-module-descent). -/
noncomputable def deckMap {S : Scheme.{u}} (c : S.FiniteEtale) (g : Aut c) :
    coverObject c ⟶ coverObject c :=
  (equivSmallModel.{u + 1} S.Etale).functor.map g.hom.hom

/-- The full subcategory cut out by constant inverse image along the cover.
For an etale map inverse image is restriction to the localized site.
Source: Stacks 00XR, 04TR (blueprint: lem-per-galois-cover-module-descent). -/
def Trivialized {S : Scheme.{u}} (c : S.FiniteEtale) (R : CommRingCat.{u + 1}) :
    ObjectProperty (Modules S R) := fun F ↦
  ∃ M : ModuleCat.{u + 1} R,
    Nonempty (F.over (coverObject c) ≅
      ((constantCoefficientModule (topology S) R).obj M).over (coverObject c))

/-- Forgetting only the full-subcategory wrapper of a descent equivalence.
Source: ILO XVII 7.4.6 (blueprint: lem-per-galois-cover-module-descent). -/
noncomputable abbrev realization {S : Scheme.{u}} (c : S.FiniteEtale)
    (R : CommRingCat.{u + 1})
    (E : Rep.{u + 1} R (Aut c) ≌ (Trivialized c R).FullSubcategory) :
    Rep.{u + 1} R (Aut c) ⥤ Modules S R :=
  E.functor ⋙ (Trivialized c R).ι

/-- The canonical constant section, using the module-sheafification unit.
Source: Stacks 093J (blueprint: lem-per-galois-cover-module-descent). -/
noncomputable def constantSection (S : Scheme.{u}) (R : CommRingCat.{u + 1})
    (M : ModuleCat.{u + 1} R) (U : Site S) (m : M) :
    ((constantCoefficientModule (topology S) R).obj M).val.obj (op U) :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1, u + 1, u + 1, u + 1}
    (constantCoefficientUnit (topology S) R)).unit.app
      ((strictPerfectConstantPresheaf.{u + 1} (C := Site S) R).obj M)).app (op U)) m

/-- Extension of scalars of a representation, using the existing action functor.
Source: ILO XVII 7.4.6, module operations
(blueprint: lem-per-galois-cover-module-descent). -/
noncomputable def extendRepresentation {R A : CommRingCat.{u + 1}}
    (φ : R ⟶ A) (G : Type u) [Group G] : Rep.{u + 1} R G ⥤ Rep.{u + 1} A G :=
  Rep.RepToAction R G ⋙ (ModuleCat.extendScalars φ.hom).mapAction G ⋙
    Rep.ActionToRep A G

/-- The mixed tensor representation in its canonically associated form.
Its action is `n ⊗ (a ⊗ v) ↦ n ⊗ (a ⊗ gv)`.
Source: ILO XVII 7.4.6, module operations
(blueprint: lem-per-galois-cover-module-descent). -/
noncomputable def mixedRepresentation {R A : CommRingCat.{u + 1}}
    (φ : R ⟶ A) (G : Type u) [Group G] :
    ModuleCat.{u + 1} A × Rep.{u + 1} R G ⥤ Rep.{u + 1} A G :=
  (Rep.trivialFunctor A G).prod (extendRepresentation φ G) ⋙ tensor (Rep.{u + 1} A G)

/-- The map of constant commutative ring sheaves induced by the coefficient map.
Source: Stacks 093J (blueprint: lem-per-galois-cover-module-descent). -/
noncomputable def coefficientMap (S : Scheme.{u}) {R A : CommRingCat.{u + 1}} (φ : R ⟶ A) :
    (constantSheaf.{u + 1, u + 1, u + 1, u + 2} (topology S) CommRingCat.{u + 1}).obj R ⟶
      (constantSheaf.{u + 1, u + 1, u + 1, u + 2} (topology S) CommRingCat.{u + 1}).obj A :=
  (constantSheaf.{u + 1, u + 1, u + 1, u + 2} (topology S) CommRingCat.{u + 1}).map φ

/-- The mixed sheaf tensor, retaining the A_S-linear structure by association.
Source: Stacks 03EK, 0GMW (blueprint: lem-per-galois-cover-module-descent). -/
noncomputable def mixedSheaf {S : Scheme.{u}} {R A : CommRingCat.{u + 1}}
    (φ : R ⟶ A) (N : ModuleCat.{u + 1} A) (F : Modules S R) : Modules S A :=
  (siteSheafTensorRight
    (A := (constantSheaf (topology S) CommRingCat.{u + 1}).obj A)
    (changeOfRingsOfUniverses (J := topology S)
      (R₁ := (constantSheaf (topology S) CommRingCat.{u + 1}).obj R)
      (R₂ := (constantSheaf (topology S) CommRingCat.{u + 1}).obj A)
      (coefficientMap S φ) F)).obj
    ((constantCoefficientModule (topology S) A).obj N)

/-- The map of mixed sheaf tensors induced by maps in both factors.
Source: Stacks 03EK, 0GMW (blueprint: lem-per-galois-cover-module-descent). -/
noncomputable def mixedSheafMap {S : Scheme.{u}} {R A : CommRingCat.{u + 1}}
    (φ : R ⟶ A) {N N' : ModuleCat.{u + 1} A} {F F' : Modules S R}
    (f : N ⟶ N') (h : F ⟶ F') : mixedSheaf φ N F ⟶ mixedSheaf φ N' F' :=
  (siteSheafTensorRight
    (A := (constantSheaf (topology S) CommRingCat.{u + 1}).obj A)
    (changeOfRingsOfUniverses (J := topology S)
      (R₁ := (constantSheaf (topology S) CommRingCat.{u + 1}).obj R)
      (R₂ := (constantSheaf (topology S) CommRingCat.{u + 1}).obj A)
      (coefficientMap S φ) F)).map
      ((constantCoefficientModule (topology S) A).map f) ≫
    siteSheafTensorSecondMap
      (A := (constantSheaf (topology S) CommRingCat.{u + 1}).obj A)
      ((constantCoefficientModule (topology S) A).obj N')
      (changeOfRingsHomOfUniverses (coefficientMap S φ) F h)

/-- Descent of arbitrary modules, including exactness, finite generation and mixed tensors.
The natural restriction comparison is normalized by the actual deck transformations;
thus the equivalence is the descent functor for the specified action. The inverse in the
deck formula comes from contravariance of sections, with `hg = h ∘ g`.
Source: ILO, Travaux de Gabber, Expose XVII 7.2.3 and the finite-quotient identification
in 7.4.6, pp. 301, 307; Stacks 04TR, 04TQ, 093J, 0GMW.
(blueprint: lem-per-galois-cover-module-descent).

Proof:
1. Finite etale degree is constant on connected S and positive since the Galois object
is connected and nonempty. Hence the cover is surjective. Slice localization computes
its inverse image; constants restrict canonically (finite-etale-trace-degree,
etale-site-localization-open, site-constant-restriction).
2. The graph map from the coproduct of copies of Y indexed by Aut_S(Y) to Y times_S Y
is an isomorphism: the geometric-fibre functor is conservative and the action on the
fibre is simply transitive (fet-finite-limits, fet-galois-category, galois-object).
Triple overlaps indexed by (y,gy,hgy) have pair coordinates g,h,hg.
3. Maps between arbitrary constant modules on connected nonempty Y are exactly linear
maps on values: global constant sections recover each value, and all sections are
locally constant (constant-sheaf-sections-connected, constant-module-locally-constant).
4. An action rho defines overlap maps rho(g), and the cocycle condition is precisely
rho(hg)=rho(h)rho(g). Equivariant linear maps are exactly maps of descent data.
5. Effective set-sheaf descent glues the module operations and maps. Module identities
hold locally and hence globally by morphism uniqueness (pe-set-sheaf-cover-descent).
6. Transporting the canonical descent datum of a sheaf with constant inverse image
recovers its representation. Step 3 and morphism descent prove full faithfulness;
effectivity proves essential surjectivity (etale-inverse-image-restriction).
7. Addition of maps and the trivial-action comparison descend uniquely, giving
additivity and the natural constant-sheaf identification.
8. Restriction to the cover is exact and detects zero sheaves. Constants are exact and
on connected nonempty Y detect zero modules. The kernel, homology and cokernel test
therefore preserves and reflects short exact sequences (constant-left-module-inverse-image,
finite-type-constant-exact, constant-sheaf-sections-connected).
9. A finite module gives a finite-type local system on the covering. Conversely a local
finite-type trivialization meets Y on a nonempty overlap; taking a geometric stalk
identifies the value module with its finitely generated model (constant-sheaf-geometric-stalk).
10. Tensor sheafification identifies the tensor of two constants with the constant tensor,
without flatness or finiteness. Localization commutes with tensor; on overlaps the action
is identity on N and rho(g) on V (sites-module-sheafification-tensor,
sfb-localized-site-tensor-restriction).
11. The pure-tensor comparison and inverse commute with descent, and hence glue to an
A_S-linear isomorphism. Naturality in both factors follows on pure tensors and descends
by uniqueness (pe-set-sheaf-cover-descent). Balanced tensor associativity identifies the
associated forms used here with the displayed mixed tensors in the node. -/
theorem exists_galoisCoverModuleDescent {S : Scheme.{u}} [ConnectedSpace S]
    (c : S.FiniteEtale) [PreGaloisCategory.IsGalois c] :
    ∃ E : ∀ R : CommRingCat.{u + 1},
        Rep.{u + 1} R (Aut c) ≌ (Trivialized c R).FullSubcategory,
      (∀ R : CommRingCat.{u + 1}, (realization c R (E R)).Additive) ∧
      (∀ R : CommRingCat.{u + 1},
        Nonempty (Rep.trivialFunctor R (Aut c) ⋙ realization c R (E R) ≅
          constantCoefficientModule (topology S) R)) ∧
      (∀ R : CommRingCat.{u + 1},
        ∀ K : ShortComplex (Rep.{u + 1} R (Aut c)),
          K.ShortExact ↔ (K.map (realization c R (E R))).ShortExact) ∧
      (∀ (R : CommRingCat.{u + 1}) (V : Rep.{u + 1} R (Aut c)),
        Module.Finite R V ↔ IsLocallyConstantFiniteTypeModules (topology S) R
          ((realization c R (E R)).obj V)) ∧
      (∀ R : CommRingCat.{u + 1}, ∃ e :
          forget₂ (Rep.{u + 1} R (Aut c)) (ModuleCat.{u + 1} R) ⋙
              constantCoefficientModule (topology S) R ⋙
                overFunctor (constantCoefficientRing (topology S) R) (coverObject c) ≅
            realization c R (E R) ⋙
              overFunctor (constantCoefficientRing (topology S) R) (coverObject c),
        ∀ (V : Rep.{u + 1} R (Aut c)) (g : Aut c) (v : V),
          (((realization c R (E R)).obj V).val.map (deckMap c g).op)
              (((e.app V).hom.val.app (op (Over.mk (𝟙 (coverObject c)))))
                (constantSection S R ((forget₂ _ (ModuleCat R)).obj V) (coverObject c) v)) =
            ((e.app V).hom.val.app (op (Over.mk (𝟙 (coverObject c)))))
              (constantSection S R ((forget₂ _ (ModuleCat R)).obj V) (coverObject c)
                (V.ρ g⁻¹ v))) ∧
      (∀ (R A : CommRingCat.{u + 1}) (φ : R ⟶ A),
        ∃ i : ∀ (N : ModuleCat.{u + 1} A) (V : Rep.{u + 1} R (Aut c)),
            (realization c A (E A)).obj ((mixedRepresentation φ (Aut c)).obj (N, V)) ≅
              mixedSheaf φ N ((realization c R (E R)).obj V),
          ∀ (N N' : ModuleCat.{u + 1} A) (V V' : Rep.{u + 1} R (Aut c))
            (f : N ⟶ N') (h : V ⟶ V'),
            (realization c A (E A)).map ((mixedRepresentation φ (Aut c)).map (f, h)) ≫
                (i N' V').hom =
              (i N V).hom ≫ mixedSheafMap φ f ((realization c R (E R)).map h)) := by
  sorry

end AlgebraicGeometry.GaloisModuleDescent
