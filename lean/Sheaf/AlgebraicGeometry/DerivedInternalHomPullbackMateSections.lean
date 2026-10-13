/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.Algebra.Homology.RhomGlobalSections
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct
import Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
import Sheaf.Algebra.Homology.DerivedInternalHom

/-! # Evaluation mate and its zeroth hypercohomology

Source: Stacks Project, Cohomology, Remark 08I3 and Lemmas 079W, 08DJ
(blueprint: lem-pc-derived-internal-hom-pullback-mate-sections).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Construction of the evaluation mate, with compatible sections identifications.
No invertibility of the counit composite is asserted here.

Source: Stacks Project, Tags 08I3, 079W, 08DJ and 08JA
(blueprint: lem-pc-derived-internal-hom-pullback-mate-sections).

Proof: Choose the pullback/direct-image adjunction from the underived adjunction
by the K-flat and K-injective derived-functor construction of Tag 079W. The
canonical tensor-Hom bijections of Tag 08DJ give bS and bT by the Hom-equivalence
construction of an adjunction. Resolve both tensor factors by K-flat complexes.
Termwise pullback commutes with their tensor total complex, and localization
therefore gives t. Pull back evaluation and precompose with t.inv, transpose by
bT, and then transpose by a to obtain gamma. Naturality of evaluation and the
three transpositions proves naturality in both entries.

Compute global sections on K-injective representatives. Direct image followed
by sections on S is sections on T, so the derived comparison gives z after
zeroth cohomology. For eS and eT use the identification of degree-zero Hom
cocycles modulo homotopies with derived morphisms into a K-injective complex
(Tag 08JA). Composition of chain maps gives the two naturality equations.
With these specific compatible choices, transposing pulled-back evaluation
and postcomposing with the counit takes the class of phi to the class of
Lg*(phi) followed by the counit. This proves the last equation without using
invertibility of the internal-Hom composite. -/
theorem exists_derivedInternalHom_pullback_mate_sections
    {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    ∃ (a : derivedPullback g ⊣ schemeDerivedDirectImage g)
      (bS : ∀ K : schemeDerivedCategory S, tensorRight K ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf)).obj
            (op K))
      (bT : ∀ K : schemeDerivedCategory T, tensorRight K ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf)).obj
            (op K))
      (t : tensor (schemeDerivedCategory S) ⋙ derivedPullback g ≅
        (derivedPullback g).prod (derivedPullback g) ⋙ tensor (schemeDerivedCategory T))
      (γ : derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf ⟶
        (derivedPullback g).op.prod (derivedPullback g) ⋙
          derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf ⋙
            schemeDerivedDirectImage g)
      (z : schemeDerivedDirectImage g ⋙
          ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf ≅
        ringedSiteZerothHypercohomology (Opens.grothendieckTopology T) T.toRingedSpace.sheaf)
      (eS : ∀ P : (schemeDerivedCategory S)ᵒᵖ × schemeDerivedCategory S,
        (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf).obj
          ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).obj P) ≃+
          (P.1.unop ⟶ P.2))
      (eT : ∀ P : (schemeDerivedCategory T)ᵒᵖ × schemeDerivedCategory T,
        (ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
            T.toRingedSpace.sheaf).obj
          ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).obj P) ≃+
          (P.1.unop ⟶ P.2)),
      (∀ (P P' : (schemeDerivedCategory S)ᵒᵖ × schemeDerivedCategory S) (f : P ⟶ P')
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).obj P)),
        eS P' ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
            S.toRingedSpace.sheaf).map
              ((derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf).map f)
            x) = f.1.unop ≫ eS P x ≫ f.2) ∧
      (∀ (P P' : (schemeDerivedCategory T)ᵒᵖ × schemeDerivedCategory T) (f : P ⟶ P')
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
              T.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).obj P)),
        eT P' ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology T)
            T.toRingedSpace.sheaf).map
              ((derivedInternalHom (Opens.grothendieckTopology T) T.toRingedSpace.sheaf).map f)
            x) = f.1.unop ≫ eT P x ≫ f.2) ∧
      (∀ K L : schemeDerivedCategory S,
        (a.homEquiv
            ((derivedInternalHom (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj (op K, L))
            ((derivedInternalHom (Opens.grothendieckTopology T)
              T.toRingedSpace.sheaf).obj
                (op ((derivedPullback g).obj K), (derivedPullback g).obj L))).symm
            (γ.app (op K, L)) =
          (bT ((derivedPullback g).obj K)).homEquiv
            ((derivedPullback g).obj
              ((derivedInternalHom (Opens.grothendieckTopology S)
                S.toRingedSpace.sheaf).obj (op K, L))) ((derivedPullback g).obj L)
            (t.inv.app
                ((derivedInternalHom (Opens.grothendieckTopology S)
                  S.toRingedSpace.sheaf).obj (op K, L), K) ≫
              (derivedPullback g).map ((bS K).counit.app L))) ∧
      (∀ (M : schemeDerivedCategory S) (E : schemeDerivedCategory T)
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj
            ((derivedInternalHom (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj (op M, (schemeDerivedDirectImage g).obj E))),
        eT (op ((derivedPullback g).obj M), E)
          ((z.hom.app
              ((derivedInternalHom (Opens.grothendieckTopology T)
                T.toRingedSpace.sheaf).obj (op ((derivedPullback g).obj M), E)))
            ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology S)
                S.toRingedSpace.sheaf).map (γ.app (op M, (schemeDerivedDirectImage g).obj E) ≫
                  (schemeDerivedDirectImage g).map
                    ((derivedInternalHom (Opens.grothendieckTopology T)
                      T.toRingedSpace.sheaf).map
                      (X := (op ((derivedPullback g).obj M),
                        (derivedPullback g).obj ((schemeDerivedDirectImage g).obj E)))
                      (Y := (op ((derivedPullback g).obj M), E))
                      ((𝟙 ((derivedPullback g).obj M)).op, a.counit.app E))) x)) =
          (derivedPullback g).map
              (eS (op M, (schemeDerivedDirectImage g).obj E) x) ≫
            a.counit.app E) := by sorry

end AlgebraicGeometry
