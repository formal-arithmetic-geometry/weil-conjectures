/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat

/-! # Local comparison factors

Source: Stacks Project, perfect.tex, Tags 0DJ7 and 0DJ9;
cohomology.tex, Tags 06YB and 0D5S.
(blueprint: lem-pc-open-flat-complex-stalk-counit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The stalk scalar-extension counit computes the local sheaf pullback counit
on a bounded-above flat sheaf complex, including transport of both local rings.

Proof: a bounded-above complex of flat sheaves is K-flat. Take its termwise stalk
at xS and transport through the inverse open-stalk isomorphism; exact stalks
preserve acyclic complexes and flat stalks give a K-flat complex P. The natural
tensor-pullback stalk isomorphism, conjugated by the open-stalk ring isomorphisms,
identifies ordinary pullback of K at xV with scalar extension of P along the
original stalk map of g. The resLE equation j ≫ S.ι = V.ι ≫ g proves equality of
these ring maps. Exact stalks commute with derived homology. Resolve sheaf
complexes by K-flat complexes and apply the tensor-stalk comparison to descend a
natural isomorphism between the stalk of derived pullback and derived scalar
extension. For the given universal pair LF, ε, uniqueness of the left-derived
functor transports this isomorphism while preserving its counit. On K the counit
is invertible, and its comparison with the sheaf counit is the ordinary tensor
stalk identity on pure tensors, followed by localization. Taking homology gives
l, r and their equation. Neither a direct image nor a coefficient module enters
this calculation. Zero complexes, zero rings and identity maps use the same
natural identities; no degree or nonzero-ring exception is needed.
Source: Stacks Project, cohomology.tex, Lemma lemma-check-K-flat-stalks (Tag 06YB),
Lemma lemma-derived-pullback-composition (Tag 0D5S); perfect.tex, equation-bc (Tag 0DJ7).
(blueprint: lem-pc-open-flat-complex-stalk-counit). -/
theorem openFlatComplex_stalk_counit
    {B A : Scheme.{u}} (g : A ⟶ B) (a : A)
    (S : B.Opens) (V : A.Opens) (hS : g a ∈ S) (hV : a ∈ V)
    (hVS : V ≤ g ⁻¹ᵁ S)
    (K : CochainComplex (SheafOfModules.{u}
      (moduleRings S.toScheme.toRingedSpace)) ℤ)
    (hbound : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let R := B.presheaf.stalk (g a)
    let T := A.presheaf.stalk a
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} T)
    let xS : S.toScheme := ⟨g a, hS⟩
    let xV : V.toScheme := ⟨a, hV⟩
    let P := ((ModuleCat.restrictScalars
      (S.stalkIso xS).inv.hom).mapHomologicalComplex (.up ℤ)).obj
      (((RingedSpace.moduleStalkFunctor S.toScheme.toRingedSpace xS).mapHomologicalComplex
         (.up ℤ)).obj K)
    let F := RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace xV ⋙
      ModuleCat.restrictScalars (V.stalkIso xV).inv.hom
    let j := g.resLE S V hVS
    let qK := (HomotopyCategory.quotient _ (.up ℤ)).obj K
    ∀ (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} T))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh)
      (hLF : LF.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))) (n : ℤ),
      ∃ (l : F.obj ((DerivedCategory.homologyFunctor _ n).obj
            ((derivedPullback j).obj (DerivedCategory.Qh.obj qK))) ≅
          (DerivedCategory.homologyFunctor _ n).obj
            (LF.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P))))
        (r : (DerivedCategory.homologyFunctor _ n).obj
            (DerivedCategory.Qh.obj
              (((ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory
                (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≅
          F.obj ((DerivedCategory.homologyFunctor _ n).obj
            (DerivedCategory.Qh.obj
              (((Scheme.Modules.tensorPullback j).mapHomotopyCategory (.up ℤ)).obj qK)))),
        F.map ((DerivedCategory.homologyFunctor _ n).map
            ((SingleComplexBaseChange.counit j).app qK)) =
          l.hom ≫ (DerivedCategory.homologyFunctor _ n).map
            (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ r.hom := by sorry

end AlgebraicGeometry
