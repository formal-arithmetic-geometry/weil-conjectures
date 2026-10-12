/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties

/-! # Functoriality of cohomology maps induced by scheme maps

Source: Stacks Project, Cohomology of Sheaves, Section 01F7, Lemma 01F8 and Remark 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

The comparison maps below account for the canonical identifications of successive
pushforwards. The unit equations specify the pullback comparison and the restricted
module map without choosing another implementation of either notion.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- Source: Stacks Project, Tags 01F8 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

Proof: lifts with the same augmentation are homotopic by
lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, hence give equal maps on cohomology
by lem-weil-pbc-homotopic-maps-equal-cohomology. For fixed I and J choose a degreewise
monic lambda using lem-weil-pbc-complex-injective-resolution-mono; lift any other lambda
across it by lem-weil-pbc-lift-along-injective-quasi-iso. The augmentation equation and
homotopy uniqueness compare beta, and invertibility from
lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso cancels the comparison.
Changing J uses a lift of the identity from lem-weil-pbc-injective-resolution-lift-exists
and isoRightDerivedObj naturality (lem-weil-pbc-derived-functor-map-via-lift). Changing I
uses the same identity lift, then a comparison between the target complexes, cancelling
its sections map and the resolution isomorphisms. This proves independence.
For composition identify k_*h_* with (h followed by k)_* sectionwise. Choose compatible
resolutions of F, G, H and monic comparisons for the latter two systems. Resolve k_*K
into a common injective complex and lift both routes into it. Their augmentations agree,
so their cohomology maps agree; cancel the invertible vertical sections maps to obtain
composition. Taking an identity scheme morphism and using
lem-weil-pbc-module-cohomology-fmap-basic-properties gives the two module naturalities.
Apply composition to the two adjunction units: the unit equation characterizes the
canonical pullback comparison c, and target naturality supplies H(c).
For restriction the restricted map exists sectionwise: on T inside V it is psi_T.
Its unit square commutes since psi respects restrictions from T to T intersect V.
Apply composition to both routes around that square to obtain the cohomology square. -/
theorem moduleCohomologyFMap_independent {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : Y.Modules} {F : X.Modules} (φ : G ⟶ (pushforward h).obj F)
    (C C' : ModuleCohomologyFMapData h G F φ) (p : ℕ) :
    C.map p = C'.map p := by
  sorry

/-- Source: Stacks Project, Tags 01F8 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

Proof: lifts with the same augmentation are homotopic by
lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, hence give equal maps on cohomology
by lem-weil-pbc-homotopic-maps-equal-cohomology. For fixed I and J choose a degreewise
monic lambda using lem-weil-pbc-complex-injective-resolution-mono; lift any other lambda
across it by lem-weil-pbc-lift-along-injective-quasi-iso. The augmentation equation and
homotopy uniqueness compare beta, and invertibility from
lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso cancels the comparison.
Changing J uses a lift of the identity from lem-weil-pbc-injective-resolution-lift-exists
and isoRightDerivedObj naturality (lem-weil-pbc-derived-functor-map-via-lift). Changing I
uses the same identity lift, then a comparison between the target complexes, cancelling
its sections map and the resolution isomorphisms. This proves independence.
For composition identify k_*h_* with (h followed by k)_* sectionwise. Choose compatible
resolutions of F, G, H and monic comparisons for the latter two systems. Resolve k_*K
into a common injective complex and lift both routes into it. Their augmentations agree,
so their cohomology maps agree; cancel the invertible vertical sections maps to obtain
composition. Taking an identity scheme morphism and using
lem-weil-pbc-module-cohomology-fmap-basic-properties gives the two module naturalities.
Apply composition to the two adjunction units: the unit equation characterizes the
canonical pullback comparison c, and target naturality supplies H(c).
For restriction the restricted map exists sectionwise: on T inside V it is psi_T.
Its unit square commutes since psi respects restrictions from T to T intersect V.
Apply composition to both routes around that square to obtain the cohomology square. -/
theorem moduleCohomologyFMap_comp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    {H : Z.Modules} {G : Y.Modules} {F : X.Modules}
    (ψ : H ⟶ (pushforward k).obj G) (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    moduleCohomologyFMap (h ≫ k)
      (ψ ≫ (pushforward k).map φ ≫ (pushforwardComp h k).hom.app F) p =
        moduleCohomologyFMap k ψ p ≫ moduleCohomologyFMap h φ p := by
  sorry

/-- Source: Stacks Project, Tags 01F8 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

Proof: lifts with the same augmentation are homotopic by
lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, hence give equal maps on cohomology
by lem-weil-pbc-homotopic-maps-equal-cohomology. For fixed I and J choose a degreewise
monic lambda using lem-weil-pbc-complex-injective-resolution-mono; lift any other lambda
across it by lem-weil-pbc-lift-along-injective-quasi-iso. The augmentation equation and
homotopy uniqueness compare beta, and invertibility from
lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso cancels the comparison.
Changing J uses a lift of the identity from lem-weil-pbc-injective-resolution-lift-exists
and isoRightDerivedObj naturality (lem-weil-pbc-derived-functor-map-via-lift). Changing I
uses the same identity lift, then a comparison between the target complexes, cancelling
its sections map and the resolution isomorphisms. This proves independence.
For composition identify k_*h_* with (h followed by k)_* sectionwise. Choose compatible
resolutions of F, G, H and monic comparisons for the latter two systems. Resolve k_*K
into a common injective complex and lift both routes into it. Their augmentations agree,
so their cohomology maps agree; cancel the invertible vertical sections maps to obtain
composition. Taking an identity scheme morphism and using
lem-weil-pbc-module-cohomology-fmap-basic-properties gives the two module naturalities.
Apply composition to the two adjunction units: the unit equation characterizes the
canonical pullback comparison c, and target naturality supplies H(c).
For restriction the restricted map exists sectionwise: on T inside V it is psi_T.
Its unit square commutes since psi respects restrictions from T to T intersect V.
Apply composition to both routes around that square to obtain the cohomology square. -/
theorem moduleCohomologyFMap_source_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G' G : Y.Modules} {F : X.Modules} (a : G' ⟶ G)
    (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).map
      ((RingedSpace.moduleCohomology Y.toRingedSpace p).map a) ≫
        moduleCohomologyFMap h φ p = moduleCohomologyFMap h (a ≫ φ) p := by
  have hi := (moduleCohomologyFMap_basic_properties (𝟙 Y) a p).2.2.1 Y G' G a
  have hh := moduleCohomologyFMap_comp h (𝟙 Y) a φ p
  rw [hi] at hh
  have he : a ≫ (pushforward (𝟙 Y)).map φ ≫
      (pushforwardComp h (𝟙 Y)).hom.app F = a ≫ φ := by
    ext U
    rfl
  rw [he] at hh
  exact hh.symm

/-- Source: Stacks Project, Tags 01F8 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

Proof: lifts with the same augmentation are homotopic by
lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, hence give equal maps on cohomology
by lem-weil-pbc-homotopic-maps-equal-cohomology. For fixed I and J choose a degreewise
monic lambda using lem-weil-pbc-complex-injective-resolution-mono; lift any other lambda
across it by lem-weil-pbc-lift-along-injective-quasi-iso. The augmentation equation and
homotopy uniqueness compare beta, and invertibility from
lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso cancels the comparison.
Changing J uses a lift of the identity from lem-weil-pbc-injective-resolution-lift-exists
and isoRightDerivedObj naturality (lem-weil-pbc-derived-functor-map-via-lift). Changing I
uses the same identity lift, then a comparison between the target complexes, cancelling
its sections map and the resolution isomorphisms. This proves independence.
For composition identify k_*h_* with (h followed by k)_* sectionwise. Choose compatible
resolutions of F, G, H and monic comparisons for the latter two systems. Resolve k_*K
into a common injective complex and lift both routes into it. Their augmentations agree,
so their cohomology maps agree; cancel the invertible vertical sections maps to obtain
composition. Taking an identity scheme morphism and using
lem-weil-pbc-module-cohomology-fmap-basic-properties gives the two module naturalities.
Apply composition to the two adjunction units: the unit equation characterizes the
canonical pullback comparison c, and target naturality supplies H(c).
For restriction the restricted map exists sectionwise: on T inside V it is psi_T.
Its unit square commutes since psi respects restrictions from T to T intersect V.
Apply composition to both routes around that square to obtain the cohomology square. -/
theorem moduleCohomologyFMap_target_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : Y.Modules} {F F' : X.Modules} (b : F ⟶ F')
    (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    moduleCohomologyFMap h φ p ≫ (forget₂ _ AddCommGrpCat.{u}).map
      ((RingedSpace.moduleCohomology X.toRingedSpace p).map b) =
        moduleCohomologyFMap h (φ ≫ (pushforward h).map b) p := by
  have hi := (moduleCohomologyFMap_basic_properties (𝟙 X) b p).2.2.1 X F F' b
  have hh := moduleCohomologyFMap_comp (𝟙 X) h φ b p
  rw [hi] at hh
  have he : φ ≫ (pushforward h).map b ≫
      (pushforwardComp (𝟙 X) h).hom.app F' = φ ≫ (pushforward h).map b := by
    ext U
    rfl
  rw [he] at hh
  exact hh.symm

/-- Source: Stacks Project, Tags 01F8 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

Proof: lifts with the same augmentation are homotopic by
lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, hence give equal maps on cohomology
by lem-weil-pbc-homotopic-maps-equal-cohomology. For fixed I and J choose a degreewise
monic lambda using lem-weil-pbc-complex-injective-resolution-mono; lift any other lambda
across it by lem-weil-pbc-lift-along-injective-quasi-iso. The augmentation equation and
homotopy uniqueness compare beta, and invertibility from
lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso cancels the comparison.
Changing J uses a lift of the identity from lem-weil-pbc-injective-resolution-lift-exists
and isoRightDerivedObj naturality (lem-weil-pbc-derived-functor-map-via-lift). Changing I
uses the same identity lift, then a comparison between the target complexes, cancelling
its sections map and the resolution isomorphisms. This proves independence.
For composition identify k_*h_* with (h followed by k)_* sectionwise. Choose compatible
resolutions of F, G, H and monic comparisons for the latter two systems. Resolve k_*K
into a common injective complex and lift both routes into it. Their augmentations agree,
so their cohomology maps agree; cancel the invertible vertical sections maps to obtain
composition. Taking an identity scheme morphism and using
lem-weil-pbc-module-cohomology-fmap-basic-properties gives the two module naturalities.
Apply composition to the two adjunction units: the unit equation characterizes the
canonical pullback comparison c, and target naturality supplies H(c).
For restriction the restricted map exists sectionwise: on T inside V it is psi_T.
Its unit square commutes since psi respects restrictions from T to T intersect V.
Apply composition to both routes around that square to obtain the cohomology square. -/
theorem moduleCohomologyPullback_comp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    (H : Z.Modules)
    (c : (tensorPullback h).obj ((tensorPullback k).obj H) ⟶
      (tensorPullback (h ≫ k)).obj H)
    (hc : (Classical.choose (exists_tensorPullbackAdjunction k)).unit.app H ≫
      (pushforward k).map
        ((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app
          ((tensorPullback k).obj H)) ≫
      (pushforwardComp h k).hom.app
        ((tensorPullback h).obj ((tensorPullback k).obj H)) ≫
      (pushforward (h ≫ k)).map c =
        (Classical.choose (exists_tensorPullbackAdjunction (h ≫ k))).unit.app H)
    (p : ℕ) :
    moduleCohomologyPullback (h ≫ k) H p = moduleCohomologyPullback k H p ≫
      moduleCohomologyPullback h ((tensorPullback k).obj H) p ≫
      (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.moduleCohomology X.toRingedSpace p).map c) := by
  unfold moduleCohomologyPullback
  rw [← Category.assoc]
  rw [← moduleCohomologyFMap_comp h k]
  rw [moduleCohomologyFMap_target_naturality]
  simp only [Category.assoc, hc]

/-- Source: Stacks Project, Tags 01F8 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-functorial).

Proof: lifts with the same augmentation are homotopic by
lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, hence give equal maps on cohomology
by lem-weil-pbc-homotopic-maps-equal-cohomology. For fixed I and J choose a degreewise
monic lambda using lem-weil-pbc-complex-injective-resolution-mono; lift any other lambda
across it by lem-weil-pbc-lift-along-injective-quasi-iso. The augmentation equation and
homotopy uniqueness compare beta, and invertibility from
lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso cancels the comparison.
Changing J uses a lift of the identity from lem-weil-pbc-injective-resolution-lift-exists
and isoRightDerivedObj naturality (lem-weil-pbc-derived-functor-map-via-lift). Changing I
uses the same identity lift, then a comparison between the target complexes, cancelling
its sections map and the resolution isomorphisms. This proves independence.
For composition identify k_*h_* with (h followed by k)_* sectionwise. Choose compatible
resolutions of F, G, H and monic comparisons for the latter two systems. Resolve k_*K
into a common injective complex and lift both routes into it. Their augmentations agree,
so their cohomology maps agree; cancel the invertible vertical sections maps to obtain
composition. Taking an identity scheme morphism and using
lem-weil-pbc-module-cohomology-fmap-basic-properties gives the two module naturalities.
Apply composition to the two adjunction units: the unit equation characterizes the
canonical pullback comparison c, and target naturality supplies H(c).
For restriction the restricted map exists sectionwise: on T inside V it is psi_T.
Its unit square commutes since psi respects restrictions from T to T intersect V.
Apply composition to both routes around that square to obtain the cohomology square. -/
theorem moduleCohomologyFMap_restriction {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    {H : Z.Modules} {G : Y.Modules} (ψ : H ⟶ (pushforward k).obj G) (V : Z.Opens) :
    ∃ ψV : (restrictFunctor V.ι).obj H ⟶
      (pushforward (k.resLE V (k ⁻¹ᵁ V) le_rfl)).obj
        ((restrictFunctor (k ⁻¹ᵁ V).ι).obj G),
      (restrictAdjunction V.ι).unit.app H ≫ (pushforward V.ι).map ψV ≫
        (pushforwardComp (k.resLE V (k ⁻¹ᵁ V) le_rfl) V.ι).hom.app
          ((restrictFunctor (k ⁻¹ᵁ V).ι).obj G) ≫
        (pushforwardCongr (k.resLE_comp_ι (U := V) (V := k ⁻¹ᵁ V) le_rfl)).hom.app
          ((restrictFunctor (k ⁻¹ᵁ V).ι).obj G) =
        ψ ≫ (pushforward k).map ((restrictAdjunction (k ⁻¹ᵁ V).ι).unit.app G) ≫
          (pushforwardComp (k ⁻¹ᵁ V).ι k).hom.app
            ((restrictFunctor (k ⁻¹ᵁ V).ι).obj G) ∧
      ∀ p : ℕ, moduleCohomologyFMap k ψ p ≫
        moduleCohomologyRestriction (k ⁻¹ᵁ V) G p =
        moduleCohomologyRestriction V H p ≫
          moduleCohomologyFMap (k.resLE V (k ⁻¹ᵁ V) le_rfl) ψV p := by
  sorry

end AlgebraicGeometry.Scheme.Modules
