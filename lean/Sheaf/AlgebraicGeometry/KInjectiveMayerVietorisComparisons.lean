/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisData
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen

/-! # Derived comparisons for the fixed open direct-image complexes

Source: Stacks Project, Cohomology, Tag 08BV, K-injective computation of
open direct image; Tag 08BS, preservation of K-injectivity by restriction.
(blueprint: lem-pc-kinjective-mayer-vietoris-comparisons).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

/-- The three canonical direct-image complexes compute the derived direct images,
compatibly with the U and V units and both nested restriction maps.
Source: Stacks Project, Cohomology, Tag 08BV (lemma-exact-sequence-j-star),
first paragraph of the proof; Tag 08BS (lemma-restrict-K-injective-to-open).
(blueprint: lem-pc-kinjective-mayer-vietoris-comparisons).

Proof: For A = U, V, U ∩ V, apply kInjective_of_restrict_open to I.
Transport the restricted complex by Scheme.Modules.overEquiv A; an additive
exact equivalence preserves K-injectivity, since its inverse carries acyclic
complexes to acyclic complexes and transports the homotopy groups testing
K-injectivity. Thus (schemeOpenRestriction X A)(I) is K-injective.
The inverse of rightDerivedFunctorObjQIso for underived direct image gives
Q(j_A*(I|A)) ≅ Rj_A*(Q(I|A)). Compose with the exact-restriction localization
comparison and Rj_A* applied to restriction of e. This defines the canonical
e_A. Derive schemeOpenModuleAdjunction X A, transporting the left derived
functor to the exact restriction functor. The derived unit on QI is the
localization of the underived unit followed by the K-injective computation
comparison. Naturality in e gives the two required unit identities.
For W ⊆ A, transpose the underived restriction map along the restriction
adjunction for W: by its definition this is the restricted A-counit conjugated
by schemeOpenRestrictionCompIso. Deriving this formula uses the exactness of
both restrictions and the K-injective computations just established. The
localized nested-restriction comparison is schemeDerivedOpenRestrictionCompIso,
so the result is precisely schemeDerivedOpenDirectImageRestriction.
Consequently Q(rho_AW) followed by e_W equals e_A followed by derived rho_AW.
For the supplied adjunctions use uniqueness of right adjoints: compare the
canonical derived adjunction to each supplied one by the unique right-adjoint
natural isomorphism compatible with its unit. Write beta_A for this isomorphism.
Its unit identity is eta_supplied = eta_canonical followed by beta_A; its counit
identity is epsilon_supplied = restriction(beta_A inverse) followed by
epsilon_canonical. Substitute these
in the displayed mate formula for rho_AW and use naturality of beta_W and of
the nested-restriction comparison. This gives rho_supplied = beta_A inverse
followed by rho_canonical followed by beta_W. Postcompose each canonical e_A
with beta_A at the restricted E. The unit identity gives the required unit
comparisons, and beta_A followed by rho_supplied = rho_canonical followed by
beta_W gives both restriction comparisons. There is no cover hypothesis
and no exactness assertion here; empty and repeated opens are included. -/
theorem schemeOpenModuleImageComplex_comparisons
    (X : Scheme.{u}) (U V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective]
    (E : schemeDerivedCategory X) (e : DerivedCategory.Q.obj I ≅ E)
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
    (adjUV : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
      schemeDerivedDirectImage (U ⊓ V).ι) :
    ∃ (eU : DerivedCategory.Q.obj (schemeOpenModuleImageComplex X U I) ≅
        (schemeDerivedDirectImage U.ι).obj
          ((schemeOpenRestriction X U).mapDerivedCategory.obj E))
      (eV : DerivedCategory.Q.obj (schemeOpenModuleImageComplex X V I) ≅
        (schemeDerivedDirectImage V.ι).obj
          ((schemeOpenRestriction X V).mapDerivedCategory.obj E))
      (eW : DerivedCategory.Q.obj (schemeOpenModuleImageComplex X (U ⊓ V) I) ≅
        (schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj E)),
      DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X U I) ≫ eU.hom =
        e.hom ≫ adjU.unit.app E ∧
      DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X V I) ≫ eV.hom =
        e.hom ≫ adjV.unit.app E ∧
      DerivedCategory.Q.map (schemeOpenModuleImageComplexRestriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U)) I) ≫ eW.hom =
          eU.hom ≫ schemeDerivedOpenDirectImageRestriction X
            (homOfLE inf_le_left) adjU adjUV E ∧
      DerivedCategory.Q.map (schemeOpenModuleImageComplexRestriction X
        (homOfLE (inf_le_right : U ⊓ V ≤ V)) I) ≫ eW.hom =
          eV.hom ≫ schemeDerivedOpenDirectImageRestriction X
            (homOfLE inf_le_right) adjV adjUV E := by sorry

end AlgebraicGeometry
