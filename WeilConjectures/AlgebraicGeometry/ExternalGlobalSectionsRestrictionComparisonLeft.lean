/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.ExternalSectionsUnitMapLeft

/-! # Restriction compatibility of external global sections

Source: Stacks Project, Tag 0BED, the degree-zero cup product and its restriction maps.
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The presheaf of sections of the external coefficient above opens of the first factor.
Source: Stacks Project, Tag 0BED. -/
abbrev externalSectionsPushforwardLeft
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) : X.Opensᵒᵖ ⥤ ModuleCat.{w} k :=
  (TopologicalSpace.Opens.map (pullback.fst f g).base).op ⋙
    scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)

/-- Sections above the top open are global sections on the fibre product.
Source: Stacks Project, Tag 0BED. -/
def externalSectionsTopIsoLeft
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) :
    (externalSectionsPushforwardLeft f g F G).obj (op ⊤) ≅
      scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) (op ⊤) :=
  (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)).mapIso
    (eqToIso (by simp))

/-- The external section comparison is natural in opens of the first factor.
Its components agree, up to the indicated section isomorphisms, with the canonical
external comparisons on the open subschemes.
Source: Stacks Project, Tag 0BED, lemma-kunneth, degree-zero external products;
Tags 0096, 0097 and 01CD, restriction, composition and tensor pullback. -/
theorem exists_externalSectionsRestrictionComparisonLeft
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) :
    ∃ c : scalarPresheaf f F ⋙
        MonoidalCategory.tensorRight (scalarObj g G (op ⊤)) ⟶
        externalSectionsPushforwardLeft f g F G,
      c.app (op ⊤) ≫ (externalSectionsTopIsoLeft f g F G).hom =
        ModuleCat.ofHom (externalGlobalSectionsTensor f g F G) ∧
      ∀ V : X.Opens,
        ∃ eS : (scalarPresheaf f F ⋙
            MonoidalCategory.tensorRight (scalarObj g G (op ⊤))).obj (op V) ≅
            ModuleCat.of k (scalarObj (V.ι ≫ f) (F.restrict V.ι) (op ⊤) ⊗[k]
              scalarObj g G (op ⊤)),
        ∃ eT : (externalSectionsPushforwardLeft f g F G).obj (op V) ≅
            scalarObj (pullback.fst (V.ι ≫ f) g ≫ (V.ι ≫ f))
              (externalCupCoefficients (V.ι ≫ f) g (F.restrict V.ι) G) (op ⊤),
          c.app (op V) ≫ eT.hom = eS.hom ≫
            ModuleCat.ofHom
              (externalGlobalSectionsTensor (V.ι ≫ f) g (F.restrict V.ι) G) := by
  refine ⟨externalSectionsUnitLeft f g F G, externalSectionsUnitLeft_top f g F G, ?_⟩
  intro V
  obtain ⟨eS, eT, h⟩ := exists_externalSectionsUnitOpenTransportLeft f g F G V
  refine ⟨eS, eT, ?_⟩
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  exact h s t

end
end AlgebraicGeometry.Scheme.Modules
