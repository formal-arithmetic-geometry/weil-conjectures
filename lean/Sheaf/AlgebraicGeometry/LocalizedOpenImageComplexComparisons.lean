/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisData

/-! # Localized-site comparisons for the concrete open-image complexes

Source: Stacks Project, Tags 08BV, 08BS, and 079W.
(blueprint: lem-pc-localized-open-image-complex-comparisons).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The concrete image complexes compute any supplied right adjoints to
localized-site restriction, compatibly with every nested restriction.

Source: Stacks Project, Tag 08BV, lemma-exact-sequence-j-star, first paragraph;
Tag 08BS, lemma-restrict-K-injective-to-open; Tag 079W, lemma-adjoint.
(blueprint: lem-pc-localized-open-image-complex-comparisons).

Proof: For every open T, obtain a derived localization of module sheaves on
the open subscheme in the prescribed Hom universe by
open_derived_localization_adjunction. Restriction of I to T is K-injective,
since exact extension by zero is its left adjoint. The equivalence
Scheme.Modules.overEquiv T carries this restricted complex to a K-injective
complex on the open subscheme. The inverse K-injective computation isomorphism
for ordinary direct image, followed by exact-restriction localization and
restriction of e, identifies Q(J_T) with the usual derived direct image of
E restricted to T. The derived equivalence of localized-site and open-scheme
categories identifies the left adjoint with the localized restriction R_T.
Transport the right adjoint through this equivalence and compare it with G_T
by the unique natural isomorphism of right adjoints compatible with their
adjunctions. Postcomposition gives e_T.
For an inclusion W into T, the comparison
schemeOpenModuleImageComplexComparison_restriction identifies Q of the fixed
underived restriction with the mate of the restricted T-counit. Exact derived
composition transports the nested-restriction comparison to the localized
one defining derivedOpenHomRestriction. The right-adjoint comparison preserves
counits and is natural. Thus the mate is the transpose under adj W of the
restriction of beta_T, where beta_T is the transpose under adj T of identity.
Naturality in e gives the equality for the supplied representative of E.
This argument uses neither termwise injectivity nor a cover nor exactness of
any sequence. Empty and repeated opens use the same adjunction identities. -/
theorem schemeOpenModuleImageComplex_localized_comparisons
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (G : ∀ W : X.Opens,
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W)) ⥤
        schemeDerivedCategory X)
    (adj : ∀ W : X.Opens,
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory ⊣
        G W)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective]
    (E : schemeDerivedCategory X) (e : DerivedCategory.Q.obj I ≅ E) :
    let R := fun W : X.Opens ↦
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    ∃ eT : ∀ T : X.Opens, DerivedCategory.Q.obj (schemeOpenModuleImageComplex X T I) ≅
        (G T).obj ((R T).obj E),
      ∀ (T W : X.Opens) (i : W ⟶ T),
        let A := (G T).obj ((R T).obj E)
        let β := ((adj T).homEquiv A ((R T).obj E)).symm (𝟙 A)
        DerivedCategory.Q.map (schemeOpenModuleImageComplexRestriction X i I) ≫
            (eT W).hom =
          (eT T).hom ≫ (adj W).homEquiv A ((R W).obj E)
            (derivedOpenHomRestriction X.toRingedSpace i β) := by sorry

end AlgebraicGeometry
