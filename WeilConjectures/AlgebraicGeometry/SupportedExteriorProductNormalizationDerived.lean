/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedExteriorProductNormalization

/-!
# The derived supported exterior product

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
def-pur-supported-exterior-product.md (blueprint: def-pur-supported-exterior-product).

The supported exterior product κ is the unique morphism normalized on K-flat representatives
and injective support resolutions by `IsResolutionSupportedExteriorProduct`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

section Derived

/-- The direct supported-section pairing has a unique derived extension with its
K-flat/injective-resolution normalization. Source: the nested blueprint unit cited
above (blueprint: def-pur-supported-exterior-product).
Proof: choose K-flat representatives of the two inputs, resolve supported sections by
injectives, and totalize the ordinary pairing. The kernel vanishing on the two pulled-back
complements makes its target the product-support complex. The usual resolution comparison
maps identify the resulting morphisms for different resolutions. To check independence
and uniqueness one can use flat support-acyclic resolutions: these are obtained by the
flasque resolution of flat sheaves, with finite truncation using finite cohomological
dimension on the separated finite-type schemes. Comparison with injective support
resolutions makes the two input units invertible there. The normalization therefore
determines the map. Its comparison on arbitrary K-flat representatives is the same
chain-level pairing followed by the injective-resolution units. -/
theorem existsUnique_resolutionSupportedExteriorProduct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hF : ∃ c : ℤ, (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE c) :
    ∃! κ : (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A) i).obj K.obj ⊗
        (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A) j).obj L.obj ⟶
      (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A)
        (supportedProductImmersion f g i j)).obj
          (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj),
      IsResolutionSupportedExteriorProduct (ModuleCat.{u + 1} A) f g i j K.obj L.obj κ := by
  sorry

/-- The supported exterior product κ, defined anew by the unique derived extension
of pullback and tensor of supported sections, normalized on K-flat representatives
and injective support resolutions. Source: literature/blueprint/latest/blueprint/
part-duality-trace-formula/sec-smooth-purity/sec-the-trace-map-of-affine-space/
sk-prop-an/def-pur-supported-exterior-product.md
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def resolutionSupportedExteriorProduct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : ∃ c : ℤ, (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE c) :
    (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A) i).obj K.obj ⊗
        (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A) j).obj L.obj ⟶
      (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A)
        (supportedProductImmersion f g i j)).obj
          (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj) :=
  (existsUnique_resolutionSupportedExteriorProduct A k f g i j K L hF).exists.choose

/-- The representative characterization of κ. Source: the nested blueprint unit cited
above (blueprint: def-pur-supported-exterior-product).
Proof: take the normalized element of the unique-existence theorem used in the definition. -/
theorem resolutionSupportedExteriorProduct_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : ∃ c : ℤ, (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE c) :
    IsResolutionSupportedExteriorProduct (ModuleCat.{u + 1} A) f g i j K.obj L.obj
      (resolutionSupportedExteriorProduct A k f g i j K L hF) := by
  exact (existsUnique_resolutionSupportedExteriorProduct A k f g i j K L hF).exists.choose_spec

/-- Forgetting the output support after κ is the ordinary exterior product after
forgetting both input supports. Source: the nested blueprint unit cited above
(blueprint: def-pur-supported-exterior-product).
Proof: the ordinary kernel lift followed by its inclusion is the pullback and tensor
of sections. The same equality holds on every bidegree of the signed total complexes.
Apply the K-flat tensor localization and the injective-resolution units to this identity.
The support inclusions commute with these units by naturality of right derivation.
The resulting ordinary pairing is the recorded canonical Künneth map. Comparison on
support-acyclic resolutions gives the claimed identity for the derived objects. -/
theorem resolutionSupportedExteriorProduct_forgetSupport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : ∃ c : ℤ, (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE c) :
    resolutionSupportedExteriorProduct A k f g i j K L hF ≫
      (Functor.rightDerivedFunctorNatTrans
        (Sheaf.ΓSupportι (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)
          (op (Scheme.Etale.mk
            (supportedProductImmersion f g i j).openComplement.ι)))).app
          (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj) =
    tensorHom
      ((Functor.rightDerivedFunctorNatTrans
        (Sheaf.ΓSupportι X.smallEtaleTopology (ModuleCat.{u + 1} A)
          (op (Scheme.Etale.mk i.openComplement.ι)))).app K.obj)
      ((Functor.rightDerivedFunctorNatTrans
        (Sheaf.ΓSupportι Y.smallEtaleTopology (ModuleCat.{u + 1} A)
          (op (Scheme.Etale.mk j.openComplement.ι)))).app L.obj) ≫
      kunnethGlobalSectionsMap A (pullback.fst f g) (pullback.snd f g) f g
        pullback.condition.symm K.obj L.obj := by
  sorry

end Derived

end AlgebraicGeometry.Etale
