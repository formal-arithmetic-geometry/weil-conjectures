/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-! # Normalized maps between constant coefficient sheaves

Source: Stacks Project, sites.tex, sheafification universal property, and
sites-cohomology.tex, Tag 06YY (blueprint: lem-asd-supported-constant-scalar-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Construct the coefficient map by sheafification of the sectionwise ring map.
Source: Stacks Project, sites-cohomology.tex, Tag 06YY.
(blueprint: lem-asd-supported-constant-scalar-map).
Proof: send a constant r to the constant section with value φ(r). This is R-linear
and natural in the etale object. The sheafification adjunction extends this map;
its factorization equation gives the asserted formula on every generator. -/
theorem exists_supported_constant_scalar_map
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) :
    ∃ η : ordinaryFiniteConstant R T ⟶
        (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (ordinaryFiniteConstant S T),
      ∀ (U : T.Etaleᵒᵖ) (r : R),
        η.hom.app U
          ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            (ModuleCat.of R R))).app U r) =
        (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of S S))).app U (φ r) := by
  let G := (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
    (ordinaryFiniteConstant S T)
  let c : (Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of R R) ⟶ G.obj :=
    { app := fun U ↦ ModuleCat.ofHom (X := ModuleCat.of R R) (Y := G.obj.obj U)
        { toFun := fun r ↦ (toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of S S))).app U (φ r)
          map_add' := by intros; simp
          map_smul' := by
            intro r x
            change (toSheafify T.smallEtaleTopology
              ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of S S))).app U (φ (r * x)) =
                φ r • (toSheafify T.smallEtaleTopology
                  ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of S S))).app U (φ x)
            rw [map_mul]
            exact ((toSheafify T.smallEtaleTopology
              ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of S S))).app U).hom.map_smul _ _ }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        have h := ConcreteCategory.congr_hom
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of S S))).naturality f) (φ r)
        exact h }
  refine ⟨⟨sheafifyLift T.smallEtaleTopology c G.property⟩, ?_⟩
  intro U r
  exact ConcreteCategory.congr_hom
    (congrArg (fun t ↦ t.app U) (toSheafify_sheafifyLift T.smallEtaleTopology c G.property)) r

end AlgebraicGeometry.Etale
