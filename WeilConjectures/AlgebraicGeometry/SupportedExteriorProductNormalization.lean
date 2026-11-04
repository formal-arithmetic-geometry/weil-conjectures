/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.KunnethGlobalSections
public import WeilConjectures.SixFunctors.Etale.SupportCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct

/-!
# Exterior products of supported sections, derived on resolutions

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
def-pur-supported-exterior-product.md (blueprint: def-pur-supported-exterior-product).

First pull back and tensor ordinary supported sections. Totalize this pairing with the
cochain sign convention, then derive it using K-flat tensor and the injective-resolution
units of the recorded support functors. The resolution characterization determines the
resulting morphism uniquely. No adjunction for supported coefficient objects is used.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

section Ordinary

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [HasSmallSiteSheafify C]

/-- Naturality of the pointwise tensor of two sections.
Source: the supported-section pairing of the nested blueprint unit cited above
(blueprint: def-pur-supported-exterior-product).
Proof: restrictions of the two global sections commute with every site morphism;
tensor those two identities and use naturality of the sheafification tensor map. -/
theorem exteriorSections_naturality (T : Scheme.{u})
    (F G : Sheaf T.smallEtaleTopology C) {U V : T.Etaleᵒᵖ} (a : U ⟶ V) :
    ((Functor.const T.Etaleᵒᵖ).obj
        ((Sheaf.Γ T.smallEtaleTopology C).obj F ⊗
          (Sheaf.Γ T.smallEtaleTopology C).obj G)).map a ≫
        (tensorHom (Sheaf.ΓRes F V) (Sheaf.ΓRes G V) ≫
          (Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology C) F G).app V) =
      (tensorHom (Sheaf.ΓRes F U) (Sheaf.ΓRes G U) ≫
        (Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology C) F G).app U) ≫
        (F ⊗ G).obj.map a := by
  sorry

/-- Tensor two global sections, using the actual pointwise tensor followed by
sheafification. Source: the nested blueprint unit cited above
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def exteriorSectionsTensor (T : Scheme.{u})
    (F G : Sheaf T.smallEtaleTopology C) :
    (Sheaf.Γ T.smallEtaleTopology C).obj F ⊗
      (Sheaf.Γ T.smallEtaleTopology C).obj G ⟶
        (Sheaf.Γ T.smallEtaleTopology C).obj (F ⊗ G) :=
  Sheaf.ΓHomEquiv
    { app := fun U ↦ tensorHom (Sheaf.ΓRes F U) (Sheaf.ΓRes G U) ≫
        (Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology C) F G).app U
      naturality := fun _ _ a ↦ exteriorSections_naturality C T F G a }

variable {B X Y Z W : Scheme.{u}}
  (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
  [IsClosedImmersion i] [IsClosedImmersion j]

/-- Pull back and tensor ordinary sections from the two factors.
Source: the nested blueprint unit cited above (blueprint: def-pur-supported-exterior-product). -/
noncomputable def exteriorSectionsMap
    (F : Sheaf X.smallEtaleTopology C) (G : Sheaf Y.smallEtaleTopology C) :
    (Sheaf.Γ X.smallEtaleTopology C).obj F ⊗
      (Sheaf.Γ Y.smallEtaleTopology C).obj G ⟶
        (Sheaf.Γ (pullback f g).smallEtaleTopology C).obj
          ((upperStar C (pullback.fst f g)).obj F ⊗
            (upperStar C (pullback.snd f g)).obj G) :=
  tensorHom (globalSectionsUpperStarMap C (pullback.fst f g) F)
      (globalSectionsUpperStarMap C (pullback.snd f g) G) ≫
    exteriorSectionsTensor C (pullback f g) _ _

/-- The tensor of pulled-back supported sections vanishes off the product support.
Source: the nested blueprint unit cited above (blueprint: def-pur-supported-exterior-product).
Proof: the complement of the product support is covered by the inverse images of the
two complements. On the first open the first factor restricts to zero, and on the
second the second factor does. Tensoring a zero morphism gives zero; the sheaf axiom
then gives vanishing on their union. -/
theorem exteriorSections_support (F : Sheaf X.smallEtaleTopology C)
    (G : Sheaf Y.smallEtaleTopology C) :
    (tensorHom
        ((Sheaf.ΓSupportι X.smallEtaleTopology C
          (op (Scheme.Etale.mk i.openComplement.ι))).app F)
        ((Sheaf.ΓSupportι Y.smallEtaleTopology C
          (op (Scheme.Etale.mk j.openComplement.ι))).app G) ≫
      exteriorSectionsMap C f g F G) ≫
      Sheaf.ΓRes _ (op (Scheme.Etale.mk
        (supportedProductImmersion f g i j).openComplement.ι)) = 0 := by
  sorry

/-- The ordinary supported exterior product is the kernel lift of the pullback and
tensor of sections. Source: the nested blueprint unit cited above
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def exteriorSupportedSections
    (F : Sheaf X.smallEtaleTopology C) (G : Sheaf Y.smallEtaleTopology C) :
    (globalSectionsWithSupport C i).obj F ⊗ (globalSectionsWithSupport C j).obj G ⟶
      (globalSectionsWithSupport C (supportedProductImmersion f g i j)).obj
        ((upperStar C (pullback.fst f g)).obj F ⊗
          (upperStar C (pullback.snd f g)).obj G) :=
  kernel.lift
      (Sheaf.ΓRes _ (op (Scheme.Etale.mk
        (supportedProductImmersion f g i j).openComplement.ι)))
      (tensorHom
        ((Sheaf.ΓSupportι X.smallEtaleTopology C
          (op (Scheme.Etale.mk i.openComplement.ι))).app F)
        ((Sheaf.ΓSupportι Y.smallEtaleTopology C
          (op (Scheme.Etale.mk j.openComplement.ι))).app G) ≫
        exteriorSectionsMap C f g F G)
      (exteriorSections_support C f g i j F G) ≫
    (PreservesKernel.iso ((evaluation _ C).obj _)
      (Sheaf.natTransΓRes (pullback f g).smallEtaleTopology C
        (op (Scheme.Etale.mk
          (supportedProductImmersion f g i j).openComplement.ι)))).inv


/-- The ordinary exterior product of two cochain complexes, with the signed total
tensor differential. Source: the nested blueprint unit cited above
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def exteriorSectionsComplexTarget
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) :
    CochainComplex (Sheaf (pullback f g).smallEtaleTopology C) ℤ :=
  ((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P ⊗
    ((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q

/-- The degreewise supported pairings extend uniquely to the signed total complexes.
Source: the nested blueprint unit cited above (blueprint: def-pur-supported-exterior-product).
Proof: in degree n use the coproduct of the pairings in bidegrees r+s=n, followed by
the inclusion of that bidegree in the sheaf tensor total. Naturality of pullback,
tensor and the support kernel makes this commute with both differentials. The second
one carries the sign (-1)^r on both sides. The coproduct inclusions determine the map. -/
theorem existsUnique_exteriorSupportedSectionsComplex
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) :
    ∃! φ : ((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((globalSectionsWithSupport C (supportedProductImmersion f g i j)).mapHomologicalComplex
        (.up ℤ)).obj (exteriorSectionsComplexTarget C f g P Q),
      ∀ (r s n : ℤ) (h : r + s = n),
        HomologicalComplex.ιTensorObj
            (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P)
            (((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q) r s n h ≫
          φ.f n =
        exteriorSupportedSections C f g i j (P.X r) (Q.X s) ≫
          (globalSectionsWithSupport C (supportedProductImmersion f g i j)).map
            (HomologicalComplex.ιTensorObj
              (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P)
              (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q)
              r s n h) := by
  sorry

/-- The totalized pairing of supported sections. It is the unique chain map whose
bidegree maps are the explicit kernel lifts above; no object is chosen by bare existence.
Source: the nested blueprint unit cited above (blueprint: def-pur-supported-exterior-product). -/
noncomputable def exteriorSupportedSectionsComplex
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) :
    ((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((globalSectionsWithSupport C (supportedProductImmersion f g i j)).mapHomologicalComplex
        (.up ℤ)).obj (exteriorSectionsComplexTarget C f g P Q) :=
  (existsUnique_exteriorSupportedSectionsComplex C f g i j P Q).exists.choose

/-- The canonical comparison from the derived exterior product to the localized
ordinary exterior complex: the two pullback counits followed by the tensor localization map.
Source: the nested blueprint unit cited above (blueprint: def-pur-supported-exterior-product). -/
noncomputable def exteriorProductResolutionComparison
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) :
    externalProduct C f g (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.obj (exteriorSectionsComplexTarget C f g P Q) :=
  derivedTensorHom C
      ((upperStar C (pullback.fst f g)).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj P))
      ((upperStar C (pullback.snd f g)).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj Q)) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q
      (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P)
      (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q)

/-- K-flat representatives compute the derived exterior product.
Source: the nested blueprint unit cited above (blueprint: def-pur-supported-exterior-product).
Proof: inverse image is exact and monoidal, so preserves K-flat complexes. Its derived
counit is invertible on K-flat representatives. Tensor localization is invertible on
a pair of K-flat complexes. Thus every factor in the displayed comparison is invertible. -/
theorem isIso_exteriorProductResolutionComparison
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ)
    (_hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (_hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q) :
    IsIso (exteriorProductResolutionComparison C f g P Q) := by
  sorry

/-- The canonical exterior-product comparison, inverted on K-flat representatives.
Source: the nested blueprint unit cited above (blueprint: def-pur-supported-exterior-product). -/
noncomputable def exteriorProductResolutionIso
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q) :
    externalProduct C f g (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj (exteriorSectionsComplexTarget C f g P Q) :=
  letI := isIso_exteriorProductResolutionComparison C f g P Q hP hQ
  asIso (exteriorProductResolutionComparison C f g P Q)

/-- The comparison from termwise supported sections to their injective right derivation.
It is the actual unit of the recorded support functor, and is invertible on injective
support resolutions. Source: the nested blueprint unit cited above
(blueprint: def-pur-supported-exterior-product). -/
noncomputable def exteriorSupportResolutionUnit
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) :
    DerivedCategory.Q.obj
        (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (rightDerivedSectionsWithSupport C i).obj (DerivedCategory.Q.obj P) :=
  (globalSectionsWithSupport C i).rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ _).obj P)


/-- Resolution normalization of the supported exterior product. On every pair of
K-flat representatives, compare termwise support sections to injective support
resolutions, and totalize the explicit pullback-and-tensor pairing above.
Source: the nested blueprint unit cited above (blueprint: def-pur-supported-exterior-product). -/
def IsResolutionSupportedExteriorProduct
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (κ : (rightDerivedSectionsWithSupport C i).obj K ⊗
        (rightDerivedSectionsWithSupport C j).obj L ⟶
      (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).obj
        (externalProduct C f g K L)) : Prop :=
  ∀ (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L),
    tensorHom
        (exteriorSupportResolutionUnit C i P ≫
          (rightDerivedSectionsWithSupport C i).map eP.hom)
        (exteriorSupportResolutionUnit C j Q ≫
          (rightDerivedSectionsWithSupport C j).map eQ.hom) ≫ κ =
      Functor.LaxMonoidal.μ DerivedCategory.Q
          (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P)
          (((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map (exteriorSupportedSectionsComplex C f g i j P Q) ≫
        exteriorSupportResolutionUnit C (supportedProductImmersion f g i j)
          (exteriorSectionsComplexTarget C f g P Q) ≫
        (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).map
          ((exteriorProductResolutionIso C f g P Q hP hQ).inv ≫
            derivedTensorHom C
              ((upperStar C (pullback.fst f g)).leftDerivedFunctor.map eP.hom)
              ((upperStar C (pullback.snd f g)).leftDerivedFunctor.map eQ.hom))

end Ordinary

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
  sorry

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
