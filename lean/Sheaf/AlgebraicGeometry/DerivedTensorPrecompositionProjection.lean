/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # The direct-image factorization of a tensor precomposition

Source: Stacks Project, Tag 08EU and Tag 0E4G, Lemma 48.4.4.
(blueprint: lem-sc-derived-tensor-precomposition-projection).
-/

@[expose] public section

universe u wX wY

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The direct image of tensor precomposition factors through its base tensor map.
Source: Stacks Project, Tag 08EU, canonical projection formula and naturality,
and Tag 0E4G, Lemma 48.4.4, projection-formula paragraph.
(blueprint: lem-sc-derived-tensor-precomposition-projection).

Proof: For the canonical pullback unit identification e0, the perfect projection
formula, with the tensor symmetry, gives an isomorphism from Rf*(Lf*I tensor P)
to I tensor Rf*P. Naturality in i and unit coherence identify Rf* of the
precomposition map with that isomorphism followed by i tensor identity and the
left unitor. These identities are preserved by the localization equivalences
used in derivedPullbackAcrossUniverses. Conjugate the isomorphism by hF at R and P;
hF naturality identifies the resulting equality with F.map of the full-subcategory
morphism. For the supplied arbitrary unit isomorphism e, let c = e0.inv followed
by e.hom, an automorphism of the tensor unit on X, and let d be its action on P
via the left unitor. The map built with e equals the canonical map followed by d.
Modify the projection factor t0 by I tensor F(d). Tensor naturality moves F(d)
across i tensor identity, and left-unitor naturality gives precisely the displayed
factorization. Only existence of t is asserted; it is not chosen as definition data.
There is no adjunction, beta, Q, open or annihilation assumption in this statement.
Zero P and zero i obey the same naturality identities. -/
theorem exists_derivedTensor_precomposition_projection
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    [QuasiCompact f] [QuasiSeparated f]
    (F : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (hF : F ⋙ ObjectProperty.ι (schemeDerivedQCohProperty Y) ≅
      ObjectProperty.ι (schemeDerivedQCohProperty X) ⋙ schemeDerivedDirectImage f)
    (P : schemeDerivedQCohCategory X) (I : schemeDerivedCategory Y)
    (hI : Scheme.IsPerfect Y I) (i : I ⟶ 𝟙_ (schemeDerivedCategory Y))
    (e : (derivedPullbackAcrossUniverses f).obj (𝟙_ (schemeDerivedCategory Y)) ≅
      𝟙_ (schemeDerivedCategory X))
    (hR : schemeDerivedQCohProperty X
      ((derivedPullbackAcrossUniverses f).obj I ⊗ P.obj)) :
    ∃ t : (F.obj ⟨(derivedPullbackAcrossUniverses f).obj I ⊗ P.obj, hR⟩).obj ⟶
        I ⊗ (F.obj P).obj,
      (F.map (ObjectProperty.homMk
        ((derivedPullbackAcrossUniverses f).map i ▷ P.obj ≫
          e.hom ▷ P.obj ≫ (λ_ P.obj).hom))).hom =
        t ≫ i ▷ (F.obj P).obj ≫ (λ_ (F.obj P).obj).hom := by sorry

end AlgebraicGeometry
