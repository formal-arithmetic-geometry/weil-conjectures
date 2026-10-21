/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.RingedToposBinaryDescentDefs
import Sheaf.CategoryTheory.SiteModuleExtensionByZeroExact
import Sheaf.CategoryTheory.SiteModuleSliceSheafification

/-! # The natural lower-shriek triangle for a binary subterminal cover

Source: Stacks Project, Cohomology, Tag 08BU, extended to subterminal slice sites.
-/

@[expose] public section

universe u v r w s
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
set_option autoImplicit false

/-- The natural Mayer–Vietoris triangle for extension by zero on a ringed site.
Source: Stacks Project, Cohomology, Tag 08BU (lemma-exact-sequence-lower-shriek).
(blueprint: lem-sp-ringed-topos-lower-shriek-triangle).

Proof: Form extension by zero by sheafifying the presheaf which, at X, is the direct
sum over maps X → Z of the sections of the input at (X → Z). Subterminality makes
this a single summand when the map exists, and zero otherwise. The theorem
`SheafOfModules.siteModuleExtensionByZero_exact` gives exact extension by zero
left adjoint to exact slice restriction.
The proved comparison
`SheafOfModules.sliceSheafificationComparisonIndependent_isIso` shows that module
sheafification commutes with continuous cocontinuous restriction, at the chosen
independent universes. Therefore restriction of extension from V
to U equals extension from W to U after restriction to W, and restriction back to
the same slice is the identity. The sectionwise identity comparisons commute with
units and counits.

For a module F, take the nested-open maps (iU,-iV) from extension of F|W to the sum
of the extensions of F|U and F|V, followed by the two counits to F. Their composite
is zero: the two nested maps followed by counits have the same mate, the identity
of F|W. On U the sequence is L → F|U ⊕ L → F|U, with maps (i,-1) and (1,i).
The first map is monic and the second is split epic; its kernel consists of
(-i(y),y), the image of -y under the first map. On V the maps are (1,-i') and
(i',1); the kernel consists of (x,-i'(x)). Both restricted sequences are short exact.
Restriction detects exactness: the cohomology modules restrict to zero on U,V,
and separatedness on the pulled-back covering sieve makes them zero globally.

Apply this natural short exact sequence in every degree of a complex. The canonical
connecting map of a short exact sequence of complexes gives a distinguished triangle,
natural in chain maps. Exactness makes every vertex functor preserve quasi-isomorphisms;
the natural transformation descends through the localization Q, giving one delta
on the derived category. Transport the vertices and arrows through the unique
left-adjoint isomorphisms from these termwise extensions to the displayed lU,lV,lW.
The q isomorphisms identify restrictions and the two normalization equations fix
the composition comparisons; hence the transported first map is precisely the pair
of mates in the statement and the second is precisely the counit pair. Naturality
and distinguishedness survive this transport. The proof also covers empty overlap,
U = V, zero complexes, and the zero ring.
-/
theorem ringedTopos_binary_descent_triangle
    {C : Type u} [Category.{v} C] [HasTerminal C] [HasPullbacks C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (R : Sheaf J CommRingCat.{r})
    (U V : C) [Mono (terminal.from U)] [Mono (terminal.from V)]
    (hcover : Sieve.ofArrows (fun b : Bool => if b then U else V)
        (fun b => terminal.from (if b then U else V)) ∈ J (⊤_ C))
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
        (pullback (terminal.from U) (terminal.from V))))]
    (rU : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)))
    (rV : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)))
    (rW : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
          (pullback (terminal.from U) (terminal.from V)))))
    (rUW : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
          (pullback (terminal.from U) (terminal.from V)))))
    (rVW : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
          (pullback (terminal.from U) (terminal.from V)))))
    (lU : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (lV : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (lW : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
        (pullback (terminal.from U) (terminal.from V)))) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (bangAdjU : lU ⊣ rU) (bangAdjV : lV ⊣ rV) (bangAdjW : lW ⊣ rW)
    (compU : rW ≅ rU ⋙ rUW) (compV : rW ≅ rV ⋙ rVW)
    (qU : DerivedCategory.Q ⋙ rU ≅
      moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U ⋙
        DerivedCategory.Q)
    (qV : DerivedCategory.Q ⋙ rV ≅
      moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V ⋙
        DerivedCategory.Q)
    (qW : DerivedCategory.Q ⋙ rW ≅
      moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (pullback (terminal.from U) (terminal.from V)) ⋙ DerivedCategory.Q)
    (qUW : DerivedCategory.Q ⋙ rUW ≅
      moduleOverMapComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (pullback.fst (terminal.from U) (terminal.from V)) ⋙ DerivedCategory.Q)
    (qVW : DerivedCategory.Q ⋙ rVW ≅
      moduleOverMapComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (pullback.snd (terminal.from U) (terminal.from V)) ⋙ DerivedCategory.Q)
    (compU_on_complexes : ∀ K,
      compU.hom.app (DerivedCategory.Q.obj K) ≫
        rUW.map (qU.hom.app K) ≫
          qUW.hom.app
            ((moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U).obj K) =
      qW.hom.app K ≫ DerivedCategory.Q.map
        ((moduleOverComplexComp ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (pullback.fst (terminal.from U) (terminal.from V))).hom.app K))
    (compV_on_complexes : ∀ K,
      compV.hom.app (DerivedCategory.Q.obj K) ≫
        rVW.map (qV.hom.app K) ≫
          qVW.hom.app
            ((moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V).obj K) =
      qW.hom.app K ≫ DerivedCategory.Q.map
        ((moduleOverComplexComp ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (pullback.snd (terminal.from U) (terminal.from V))).hom.app K))  :
        (∃ (delta : 𝟭 _ ⟶ rW ⋙ lW ⋙ shiftFunctor _ (1 : ℤ)),
      ∀ (M : DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
        Pretriangulated.Triangle.mk
            (biprod.lift
              ((bangAdjW.homEquiv (rW.obj M) (lU.obj (rU.obj M))).symm
                (compU.hom.app M ≫ rUW.map (bangAdjU.unit.app (rU.obj M)) ≫
                  compU.inv.app (lU.obj (rU.obj M))))
              (-((bangAdjW.homEquiv (rW.obj M) (lV.obj (rV.obj M))).symm
                (compV.hom.app M ≫ rVW.map (bangAdjV.unit.app (rV.obj M)) ≫
                  compV.inv.app (lV.obj (rV.obj M))))))
            (biprod.desc (bangAdjU.counit.app M)
              (bangAdjV.counit.app M))
            (delta.app M) ∈ distTriang _)
    := by
  sorry

end CategoryTheory

end
