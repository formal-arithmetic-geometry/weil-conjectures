/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Sheaf.Algebra.Homology.KFlat

/-! # Derived pullback of modules on schemes

Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-semicon/def-pc-derived-pullback.md, node def-pc-derived-pullback
  (blueprint: def-pc-derived-pullback).

The derived pullback is the functor obtained by applying derived change of rings to
termwise inverse image along the morphism of schemes.  Its K-flat representatives
are the termwise tensor pullbacks of K-flat resolutions; the comparison maps are
canonical and independent of the chosen resolution.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- Existence of the derived pullback functor associated with a morphism of schemes.

Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-semicon/def-pc-derived-pullback.md, node def-pc-derived-pullback;
  the functor is `L g^* = L(g^sharp)^* ∘ g⁻¹`, and on a K-flat resolution
  `P ⟶ E` it is represented by `𝒪_T ⊗_{g⁻¹𝒪_S} g⁻¹P`.
The functor `I` is the exact module inverse image, and `E` is the recorded tensor
pullback, on the shared module-sheaf category instances. The universal property and
K-flat counit specify the derived composite uniquely up to canonical isomorphism.
Source: Stacks Project, Cohomology, Tags 06YI and 06YJ.
Proof (the three steps of the node):
1. The inverse-image stalk isomorphism (lem-weil-pbc-topological-inverse-image-stalk)
   and stalkwise exactness show that `I` is exact and preserves quasi-isomorphisms
   (def-pc-quasi-iso-modules), hence induces a functor on derived categories.
2. Apply lem-pur-derived-change-of-rings to `tensorPullbackRingMap g`. Compose its
   derived functor with derived inverse image. Termwise the composite is the recorded
   `tensorPullback g`; the resolving-class universal property gives the counit below.
3. Choose a K-flat resolution (lem-pc-kflat-resolution). Inverse image preserves its
   quasi-isomorphism by step 1 and its K-flatness by lem-pc-kflat-pullback-preservation
   applied to `(T, g⁻¹𝒪_S) → (S, 𝒪_S)`. The change-of-rings counit is therefore an
   isomorphism. The canonical comparison for `s : P → G` is the inverse of `L(Q(s))`
   followed by this counit at `P`. Comparisons between resolutions factor through
   `L(Q(G))`, so are independent of choices and compatible with composition.
(blueprint: def-pc-derived-pullback). -/
theorem exists_derivedPullback {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    ∃ L : schemeDerivedCategory S ⥤ schemeDerivedCategory T,
      ∃ (I : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
          SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology T)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing g.base S.sheaf)))
        (hI : ∀ M, I.obj M = TopCat.Sheaf.inverseImageModule g.base S.sheaf M)
        (_ : ∀ {M N} (a : M ⟶ N),
          I.map a = eqToHom (hI M) ≫
            TopCat.Sheaf.inverseImageModuleMap g.base S.sheaf M a ≫
              eqToHom (hI N).symm)
        (_ : I.Additive),
        PreservesFiniteLimits I ∧ PreservesFiniteColimits I ∧
        (∀ {P G : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ}
          (s : P ⟶ G), CochainComplex.IsKFlatResolution (R := S.sheaf) s →
            CochainComplex.IsKFlatResolution
              (R := TopCat.Sheaf.inverseImageRing g.base S.sheaf)
              ((I.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) ∧
        ∃ (E : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings T.toRingedSpace))
          (h : ∀ M, E.obj M = Scheme.Modules.tensorPullbackObj g M)
          (_ : ∀ {M N} (a : M ⟶ N),
            E.map a = eqToHom (h M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
              eqToHom (h N).symm)
          (_ : E.Additive)
          (ε : DerivedCategory.Qh ⋙ L ⟶
            E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
          L.IsLeftDerivedFunctor ε
              (HomotopyCategory.quasiIso
                (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)) ∧
            (∃ (_ : L.CommShift ℤ), L.IsTriangulated) ∧
            ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ,
              CochainComplex.IsKFlat (R := S.sheaf) P →
                IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  sorry

/-- The derived pullback `L g^* : D(𝒪_S) ⥤ D(𝒪_T)`.

For `g : T ⟶ S`, this is the composite of termwise inverse image and derived change
of rings along `g^sharp`.  If `P ⟶ E` is any K-flat resolution, its canonical
representative is `g^*P = 𝒪_T ⊗_{g⁻¹𝒪_S} g⁻¹P`; the comparison isomorphisms supplied
by derived change of rings make this independent of `P`.
Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-semicon/def-pc-derived-pullback.md, node def-pc-derived-pullback
  (blueprint: def-pc-derived-pullback). -/
noncomputable def derivedPullback {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    schemeDerivedCategory S ⥤ schemeDerivedCategory T :=
  Classical.choose (exists_derivedPullback g)

end AlgebraicGeometry
