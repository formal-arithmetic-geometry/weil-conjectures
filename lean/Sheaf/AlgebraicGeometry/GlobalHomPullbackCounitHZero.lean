/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitIsomorphism

/-! # The fixed pullback-counit composite on global derived Hom

Source: Stacks Project, cohomology.tex, Tags 079W, 08I3 and 0B6A.
-/

@[expose] public section

universe u w
open CategoryTheory Opposite TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Canonical H⁰ identifications carry the fixed counit composite to the adjunction map.
Source: Stacks Project, cohomology.tex, Section global-RHom (Tag 0B6A),
Remark 08I3 and Lemma 079W
(blueprint: lem-pc-global-hom-pullback-counit-hzero).

Proof: resolve the first input by a K-flat complex and the second by a
K-injective complex. Global sections of the internal Hom complex have
zero cocycles the chain maps and zero coboundaries the null-homotopic maps.
Localization identifies their quotient additively with derived morphisms,
which defines hS and hT for every pair of objects. Exact scalar restriction
commutes with degree-zero homology, and does not change this additive group.
The canonical tensor-Hom evaluation sends a cycle to its represented chain map.
Its pullback mate sends that map to its derived pullback. The canonical Leray
comparison is induced by the identity on underived global sections, so it
preserves this identification. Finally postcomposition by the derived counit
sends the pulled-back map to F(φ) followed by ε. Thus the displayed equation
holds. Common resolutions give independence of representatives and hence
simultaneous identifications for all inputs; no arbitrary identifications
are asserted to satisfy this equation. -/
theorem schemeGlobalHomPullbackCounitMap_hzero {T S : Scheme.{u}} (g : T ⟶ S) :
    ∃ (hS : ∀ M N : schemeDerivedCategory S,
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((moduleRings S.toRingedSpace).obj.obj (op ⊤))) 0).obj
            ((schemeGlobalDerivedHom S).obj (op M, N))) ≃+ (M ⟶ N))
      (hT : ∀ M N : schemeDerivedCategory T,
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((moduleRings S.toRingedSpace).obj.obj (op ⊤))) 0).obj
            (((ModuleCat.restrictScalars.{u}
              (R := (moduleRings S.toRingedSpace).obj.obj (op ⊤))
              (S := (moduleRings T.toRingedSpace).obj.obj (op ⊤))
              g.appTop.hom).mapDerivedCategory).obj
              ((schemeGlobalDerivedHom T).obj (op M, N)))) ≃+ (M ⟶ N)),
      (∀ (M : schemeDerivedCategory S) (E : schemeDerivedCategory T)
        (φ : M ⟶ (schemeDerivedDirectImage g).obj E),
        hT ((derivedPullback g).obj M) E
          ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((moduleRings S.toRingedSpace).obj.obj (op ⊤))) 0).map
              (schemeGlobalHomPullbackCounitMap g M E)
                ((hS M ((schemeDerivedDirectImage g).obj E)).symm φ)) =
          (derivedPullback g).map φ ≫ (schemeHomPullbackAdjunction g).counit.app E) := by
  sorry

end AlgebraicGeometry
