/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeGeometricFiber
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Morphism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleExchangeFormalism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint

/-!
# The geometric fibre as a morphism of exchange formalisms

The base change `X ↦ X̄ = X ×_k k̄` from separated `k`-schemes of finite type to separated
`k̄`-schemes of finite type is a functor `geometricFiberSepFinType : SepFinType k ⥤ SepFinType k̄`,
and the pullbacks `π_X^* : Dᵇc(X) ⥤ Dᵇc(X̄)` along the projections `π_X : X̄ ⟶ X`, together with
the composition isomorphisms `π_X^* f^* ≅ f̄^* π_Y^*`, form a morphism of exchange formalisms
`geometricFiberExchangeMorphism : boundedConstructibleExchangeFormalism ℓ k ⟶
boundedConstructibleExchangeFormalism ℓ k̄` in the sense of
`CategoryTheory.ExchangeFormalism.Morphism`. Its compatibility with the composition isomorphisms
of the pullbacks (`Morphism.pbIso_comp`) is a coherence law for the pseudofunctor `L(-)^*`,
proved first for the ambient derived categories of module objects
(`leftDerivedUpperStarComp'_pentagon_app`) and then restricted to bounded constructible
complexes.

Through `CategoryTheory.ExchangeFormalism.Morphism.compIso_shriekBaseChange`, this provides the
global, composition compatible compact-support base change maps
`π_Y^* Rf_! ⟶ Rf̄_! π_X^*` used in the local proof of `IsIso smoothUnitBaseChange`
(`isIso_smoothUnitBaseChange_geometricFiber_of_charts`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Coherence of the composition isomorphisms of the ambient pullbacks -/

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The composition isomorphism `Lh^* ≅ Lg^* ⋙ Lf^*` for `f ≫ g = h`. -/
noncomputable def leftDerivedUpperStarComp' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (w : f ≫ g = h) : L((h)^*⟦Λ⟧) ≅ L((g)^*⟦Λ⟧) ⋙ L((f)^*⟦Λ⟧) :=
  eqToIso (by rw [w]) ≪≫ leftDerivedUpperStarComp Λ f g

@[simp]
lemma leftDerivedUpperStarComp'_rfl {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    leftDerivedUpperStarComp' Λ f g (f ≫ g) rfl = leftDerivedUpperStarComp Λ f g := by
  simp [leftDerivedUpperStarComp']

/-- Associativity of the composition isomorphisms with explicit composites. -/
lemma leftDerivedUpperStarComp'_assoc_app {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : fg ≫ h = fgh)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (leftDerivedUpperStarComp' Λ f gh fgh
        (by rw [← hgh, ← hfgh, ← hfg, Category.assoc])).hom.app K ≫
      L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarComp' Λ g h gh hgh).hom.app K) =
    (leftDerivedUpperStarComp' Λ fg h fgh hfgh).hom.app K ≫
      (leftDerivedUpperStarComp' Λ f g fg hfg).hom.app (L((h)^*⟦Λ⟧).obj K) := by
  subst hfg hgh hfgh
  simp only [leftDerivedUpperStarComp', Iso.trans_hom, eqToIso.hom, NatTrans.comp_app,
    eqToHom_app, eqToHom_refl, Category.id_comp, Category.assoc]
  rw [leftDerivedUpperStarComp_assoc_app]

/-- **The coherence law behind `Morphism.pbIso_comp`** for the pullbacks along a commutative
diagram
```
X̄ ⟶[f'] Ȳ ⟶[g'] Z̄
↓a       ↓b       ↓c
X  ⟶[f]  Y  ⟶[g]  Z
```
of schemes. -/
lemma leftDerivedUpperStarComp'_pentagon_app {X' Y' Z' X Y Z : Scheme.{u}}
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : Z' ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (fg : X ⟶ Z) (fg' : X' ⟶ Z') (hfg : f ≫ g = fg) (hfg' : f' ≫ g' = fg')
    (wf : a ≫ f = f' ≫ b) (wg : b ≫ g = g' ≫ c)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (leftDerivedUpperStarComp' Λ a fg (a ≫ fg) rfl).inv.app K ≫
      (leftDerivedUpperStarComp' Λ fg' c (a ≫ fg)
        (by rw [← hfg', ← hfg, Category.assoc, ← wg, ← Category.assoc, ← wf,
          Category.assoc])).hom.app K ≫
      (leftDerivedUpperStarComp' Λ f' g' fg' hfg').hom.app (L((c)^*⟦Λ⟧).obj K) =
    L((a)^*⟦Λ⟧).map ((leftDerivedUpperStarComp' Λ f g fg hfg).hom.app K) ≫
      (leftDerivedUpperStarComp' Λ a f (a ≫ f) rfl).inv.app (L((g)^*⟦Λ⟧).obj K) ≫
      (leftDerivedUpperStarComp' Λ f' b (a ≫ f) wf.symm).hom.app (L((g)^*⟦Λ⟧).obj K) ≫
      L((f')^*⟦Λ⟧).map ((leftDerivedUpperStarComp' Λ b g (b ≫ g) rfl).inv.app K ≫
        (leftDerivedUpperStarComp' Λ g' c (b ≫ g) wg.symm).hom.app K) := by
  subst hfg hfg'
  have h1 := leftDerivedUpperStarComp'_assoc_app Λ a f g (a ≫ f) (f ≫ g) (a ≫ f ≫ g) rfl rfl
    (Category.assoc a f g) K
  have h2 := leftDerivedUpperStarComp'_assoc_app Λ f' b g (a ≫ f) (b ≫ g) (a ≫ f ≫ g) wf.symm
    rfl (Category.assoc a f g) K
  have h3 := leftDerivedUpperStarComp'_assoc_app Λ f' g' c (f' ≫ g') (b ≫ g) (a ≫ f ≫ g) rfl
    wg.symm (by rw [Category.assoc, ← wg, ← Category.assoc, ← wf, Category.assoc]) K
  rw [← cancel_epi ((leftDerivedUpperStarComp' Λ a (f ≫ g) (a ≫ f ≫ g) rfl).hom.app K)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% h1, Iso.hom_inv_id_app_assoc, ← reassoc_of% h2, Functor.map_comp,
    Functor.map_hom_inv_id_app_of_iso_assoc, h3]

end Ambient

/-! ### The composition isomorphisms with explicit composites on bounded constructible complexes -/

section OfMapComp'

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ k₃ : Type u} [Field k₁] [Field k₂] [Field k₃]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)] [Fact (ringChar k₃).Prime] [Fact (ringChar k₃ ≠ ℓ)]
  {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {Y : Over (Spec (.of k₂))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {W : Over (Spec (.of k₃))} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]

/-- The composition isomorphism `L(gh)^* ≅ Lg^* ⋙ Lh^*` of the pullbacks of bounded constructible
complexes along morphisms of schemes over possibly different fields, for `h ≫ g = gh`. -/
noncomputable def boundedConstructibleUpperStarOfMapComp' (g : Y.left ⟶ X.left)
    (h : W.left ⟶ Y.left) (gh : W.left ⟶ X.left) (w : h ≫ g = gh) :
    boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := W) gh ≅
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) g ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := W) h :=
  eqToIso (by rw [w]) ≪≫ boundedConstructibleUpperStarOfMapComp ℓ g h

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₂).Prime] [Fact (ringChar k₃).Prime]
  [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂ ≠ ℓ)] [Fact (ringChar k₃ ≠ ℓ)] in
@[simp]
lemma boundedConstructibleUpperStarOfMapComp'_hom_app_hom (g : Y.left ⟶ X.left)
    (h : W.left ⟶ Y.left) (gh : W.left ⟶ X.left) (w : h ≫ g = gh)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarOfMapComp' ℓ g h gh w).hom.app A).hom =
      (leftDerivedUpperStarComp' (Profinite.padicAlgClRingObj ℓ) h g gh w).hom.app A.obj := by
  subst w
  simp [boundedConstructibleUpperStarOfMapComp', leftDerivedUpperStarComp']

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₂).Prime] [Fact (ringChar k₃).Prime]
  [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂ ≠ ℓ)] [Fact (ringChar k₃ ≠ ℓ)] in
@[simp]
lemma boundedConstructibleUpperStarOfMapComp'_inv_app_hom (g : Y.left ⟶ X.left)
    (h : W.left ⟶ Y.left) (gh : W.left ⟶ X.left) (w : h ≫ g = gh)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarOfMapComp' ℓ g h gh w).inv.app A).hom =
      (leftDerivedUpperStarComp' (Profinite.padicAlgClRingObj ℓ) h g gh w).inv.app A.obj := by
  subst w
  simp [boundedConstructibleUpperStarOfMapComp', leftDerivedUpperStarComp',
    boundedConstructibleUpperStarOfMapComp]

end OfMapComp'

/-! ### The geometric fibre functor -/

section Functor

variable {k : Type u} [Field k] [Finite k]

/-- **The geometric fibre functor** `X ↦ X̄ = X ×_k k̄` on separated `k`-schemes of finite
type. -/
@[simps]
noncomputable def geometricFiberSepFinType : SepFinType k ⥤ SepFinType (AlgebraicClosure k) where
  obj X := SepFinType.mk (geometricFiberOver X.obj)
  map f := SepFinType.homMk (geometricFiberOverMap f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    ext1
    exact Scheme.Hom.geometricFiberMap_id X.obj.hom
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact geometricFiberOverMap_comp f.hom g.hom

/-- The geometric fibre of an open immersion is an open immersion. -/
instance {X Y : SepFinType k} (j : X ⟶ Y) [Fact (SepFinType.openImmersion j)] :
    Fact (SepFinType.openImmersion (geometricFiberSepFinType.map j)) :=
  ⟨inferInstanceAs (IsOpenImmersion (geometricFiberOverMap j.hom).left)⟩

end Functor

/-! ### The geometric fibre as a morphism of exchange formalisms -/

section Morphism

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- The pullback `π_X^* : Dᵇc(X) ⥤ Dᵇc(X̄)` along the projection of the geometric fibre. -/
noncomputable abbrev geometricFiberUpperStar (X : SepFinType k) :
    Dᵇc(X.obj.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((geometricFiberOver X.obj).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleUpperStarOfMap ℓ (X := X.obj) (Y := geometricFiberOver X.obj)
    X.obj.hom.geometricFiberProj

/-- The square `π_X ≫ f = f̄ ≫ π_Y` of the geometric fibre of `f`. -/
lemma geometricFiberProj_comp_left {X Y : SepFinType k} (f : X ⟶ Y) :
    X.obj.hom.geometricFiberProj ≫ f.hom.left =
      (geometricFiberOverMap f.hom).left ≫ Y.obj.hom.geometricFiberProj :=
  (isPullback_geometricFiberOverMap f.hom).w

/-- The isomorphism `π_X^* f^* ≅ f̄^* π_Y^*`. -/
noncomputable def geometricFiberPbIso {X Y : SepFinType k} (f : X ⟶ Y) :
    (boundedConstructibleExchangeFormalism ℓ k).pb f ⋙ geometricFiberUpperStar ℓ X ≅
      geometricFiberUpperStar ℓ Y ⋙
        (boundedConstructibleExchangeFormalism ℓ (AlgebraicClosure k)).pb
          (geometricFiberSepFinType.map f) :=
  (boundedConstructibleUpperStarOfMapComp' ℓ (X := Y.obj) (Y := X.obj)
      (W := geometricFiberOver X.obj) f.hom.left X.obj.hom.geometricFiberProj _ rfl).symm ≪≫
    boundedConstructibleUpperStarOfMapComp' ℓ (X := Y.obj) (Y := geometricFiberOver Y.obj)
      (W := geometricFiberOver X.obj) Y.obj.hom.geometricFiberProj
      (geometricFiberOverMap f.hom).left _ (geometricFiberProj_comp_left f).symm

/-- The composition isomorphism of the formalism is `boundedConstructibleUpperStarOfMapComp'`. -/
lemma boundedConstructibleExchangeFormalism_pbComp'_hom_app {k' : Type u} [Field k']
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {X Y Z : SepFinType k'} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) (M : Dᵇc(Z.obj.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleExchangeFormalism ℓ k').pbComp' f g h w).hom.app M =
      (boundedConstructibleUpperStarOfMapComp' ℓ (X := Z.obj) (Y := Y.obj) (W := X.obj)
        g.hom.left f.hom.left h.hom.left (by rw [← w]; rfl)).hom.app M := by
  subst w
  apply ObjectProperty.hom_ext
  simp [ExchangeFormalism.pbComp', boundedConstructibleUpperStarOfMapComp',
    leftDerivedUpperStarComp', boundedConstructibleUpperStarComp_hom_app_hom]

/-- **The geometric fibre as a morphism of exchange formalisms**: the pullbacks `π_X^*` along
the projections `X̄ ⟶ X`, with the composition isomorphisms `π_X^* f^* ≅ f̄^* π_Y^*`. -/
noncomputable def geometricFiberExchangeMorphism :
    ExchangeFormalism.Morphism (boundedConstructibleExchangeFormalism ℓ k)
      (boundedConstructibleExchangeFormalism ℓ (AlgebraicClosure k))
      (geometricFiberSepFinType (k := k)) where
  pull X := geometricFiberUpperStar ℓ X
  pbIso f := geometricFiberPbIso ℓ f
  pbIso_comp f g M := by
    rw [boundedConstructibleExchangeFormalism_pbComp'_hom_app,
      ← ExchangeFormalism.pbComp'_rfl, boundedConstructibleExchangeFormalism_pbComp'_hom_app]
    simp only [geometricFiberPbIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc]
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom,
      boundedConstructibleUpperStarOfMapComp'_hom_app_hom,
      boundedConstructibleUpperStarOfMapComp'_inv_app_hom, boundedConstructibleUpperStarOfMap_map,
      boundedConstructibleUpperStar_map_hom, ObjectProperty.homMk_hom]
    exact leftDerivedUpperStarComp'_pentagon_app (Profinite.padicAlgClRingObj ℓ)
      X.obj.hom.geometricFiberProj Y.obj.hom.geometricFiberProj Z.obj.hom.geometricFiberProj
      f.hom.left g.hom.left (geometricFiberOverMap f.hom).left (geometricFiberOverMap g.hom).left
      (f ≫ g).hom.left (geometricFiberOverMap (f ≫ g).hom).left rfl
      (congrArg CommaMorphism.left (geometricFiberOverMap_comp f.hom g.hom)).symm
      (geometricFiberProj_comp_left f) (geometricFiberProj_comp_left g) M.obj

end Morphism

end AlgebraicGeometry.ProEtale.CondensedRing
