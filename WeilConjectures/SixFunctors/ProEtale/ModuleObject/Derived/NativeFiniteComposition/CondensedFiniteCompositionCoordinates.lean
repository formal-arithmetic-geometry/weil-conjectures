/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.SepFinType

/-! # Native finite compact-support composition coordinates

Source: latest blueprint, sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, coherence sentence; and
sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md, pentagon paragraph.
(blueprint: def-sf-native-finite-composition-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

attribute [local irreducible] DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

namespace AlgebraicGeometry.ProEtale.CondensedRing.NativeFiniteComposition

open CompactificationReindexing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- On invertible refinement components the total formula is the existing comparison.
Source: latest blueprint compactification independence, common-refinement construction
(blueprint: def-sf-native-finite-composition-coordinates).
Proof: unfold both formulas; the total inverse is the categorical inverse. -/
theorem change_eq_comparison {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) (K : D Λ X)
    [IsIso ((refinement Λ (Compactification.infFst c d)).app K)]
    [IsIso ((refinement Λ (Compactification.infSnd c d)).app K)] :
    change Λ c d K =
      (comparison Λ (Compactification.infFst c d) (Compactification.infSnd c d) K).hom := by
  classical
  simp only [change, CondensedOpenProper.comparisonInverse, dif_pos (inferInstance :
    IsIso ((refinement Λ (Compactification.infSnd c d)).app K)), comparison,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]

/-- Common-refinement transport is invertible when its two specified legs are.
Source: latest blueprint compactification independence
(blueprint: def-sf-native-finite-composition-coordinates).
Proof: identify the map with the hom of the existing common-refinement isomorphism. -/
theorem change_isIso {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) (K : D Λ X)
    [IsIso ((refinement Λ (Compactification.infFst c d)).app K)]
    [IsIso ((refinement Λ (Compactification.infSnd c d)).app K)] :
    IsIso (change Λ c d K) := by
  rw [change_eq_comparison]
  infer_instance

/-- Common-refinement transport is natural between inputs on which the inverse leg is
invertible. No invertibility of either compact-support image of the input arrow is needed.
Source: latest blueprint compactification independence, naturality of refinement maps
(blueprint: def-sf-native-finite-composition-coordinates).
Proof: postcompose with the second refinement at the target input. Its naturality moves
it through the compact-support image of the arrow, and the two inverse pairs cancel.
The remaining equation is naturality of the first refinement. -/
theorem change_naturality {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) {K L : D Λ X} (a : K ⟶ L)
    [IsIso ((refinement Λ (Compactification.infSnd c d)).app K)]
    [IsIso ((refinement Λ (Compactification.infSnd c d)).app L)] :
    (F Λ c).map a ≫ change Λ c d L = change Λ c d K ≫ (F Λ d).map a := by
  classical
  let r := refinement Λ (Compactification.infFst c d)
  let t := refinement Λ (Compactification.infSnd c d)
  apply (cancel_mono (t.app L)).1
  change ((F Λ c).map a ≫
      (r.app L ≫ CondensedOpenProper.comparisonInverse (t.app L))) ≫ t.app L =
    ((r.app K ≫ CondensedOpenProper.comparisonInverse (t.app K)) ≫
      (F Λ d).map a) ≫ t.app L
  simp only [CondensedOpenProper.comparisonInverse,
    dif_pos (inferInstance : IsIso (t.app K)),
    dif_pos (inferInstance : IsIso (t.app L))]
  calc
    ((F Λ c).map a ≫ (r.app L ≫ inv (t.app L))) ≫ t.app L =
        (F Λ c).map a ≫ r.app L := by simp
    _ = r.app K ≫ (F Λ (Compactification.inf c d)).map a := r.naturality a
    _ = ((r.app K ≫ inv (t.app K)) ≫ (F Λ d).map a) ≫ t.app L := by
      simp only [Category.assoc]
      rw [t.naturality a, IsIso.inv_hom_id_assoc]

/-- The native common-refinement map preserves the specified projection morphism.
Only refinement maps, and no projection maps, are assumed invertible.
Source: latest blueprint projection coherence, refinement paragraph
(blueprint: def-sf-native-finite-composition-coordinates).
Proof: identify each total inverse with its categorical inverse and apply the
common-refinement projection square already proved in CompactificationReindexing. -/
theorem change_projection {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) (K : D Λ X) (L : D Λ Y)
    [IsIso ((refinement Λ (Compactification.infFst c d)).app K)]
    [IsIso ((refinement Λ (Compactification.infSnd c d)).app K)]
    [IsIso ((refinement Λ (Compactification.infFst c d)).app (K ⊗ (P Λ f).obj L))]
    [IsIso ((refinement Λ (Compactification.infSnd c d)).app (K ⊗ (P Λ f).obj L))] :
    pf Λ c K L ≫ change Λ c d (K ⊗ (P Λ f).obj L) =
      (change Λ c d K ▷ L) ≫ pf Λ d K L := by
  simpa only [change_eq_comparison, MonoidalCategory.tensorHom_id] using
    comparison_projection Λ (Compactification.infFst c d) (Compactification.infSnd c d) K L

/-- The specified tower interchange restricts to the inverse of its native restriction map.
Source: latest blueprint composition, proper/open interchange normalization
(blueprint: def-sf-native-finite-composition-coordinates).
Proof: apply the adjunction Hom equivalence to its inverse image, then use the
invertible branch of the total inverse and its inverse identity. -/
theorem towerInterchange_normalized {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (M : D Λ T.cf.Z)
    [IsIso (towerRestriction Λ T M)] :
    (oa Λ T.cg.i).homEquiv _ _ (towerInterchange Λ T M) ≫
        towerRestriction Λ T M = 𝟙 _ := by
  classical
  simp only [towerInterchange, Equiv.apply_symm_apply,
    CondensedOpenProper.comparisonInverse,
    dif_pos (inferInstance : IsIso (towerRestriction Λ T M)), IsIso.inv_hom_id]

/-- The restriction normalization uniquely determines the native tower interchange.
Source: latest blueprint composition, canonicity paragraph
(blueprint: def-sf-native-finite-composition-coordinates).
Proof: cancel the invertible restriction map and use injectivity of the open-adjunction
Hom equivalence. This does not assume invertibility of the proposed interchange. -/
theorem towerInterchange_unique {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (M : D Λ T.cf.Z)
    [IsIso (towerRestriction Λ T M)]
    (m : (J Λ T.cg.i).obj ((R Λ T.cf.g).obj M) ⟶
      (R Λ T.p).obj ((J Λ T.q).obj M))
    (hm : (oa Λ T.cg.i).homEquiv _ _ m ≫ towerRestriction Λ T M = 𝟙 _) :
    m = towerInterchange Λ T M := by
  apply ((oa Λ T.cg.i).homEquiv _ _).injective
  apply (cancel_mono (towerRestriction Λ T M)).1
  exact hm.trans (towerInterchange_normalized Λ T M).symm

/-- The native tower is invertible once its proper/open interchange is invertible.
Source: latest blueprint composition, tower construction
(blueprint: def-sf-native-finite-composition-coordinates).
Proof: every remaining factor is the component of an open or proper composition
isomorphism, an equality transport, or its image under a functor. -/
theorem tower_isIso {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (K : D Λ X)
    [IsIso (towerInterchange Λ T ((J Λ T.cf.i).obj K))] :
    IsIso (tower Λ T K) := by
  unfold tower
  infer_instance

/-- Invertibility of the forward compositor reduces to its two common-refinement
changes and the chosen tower. Source: latest blueprint composition, choice independence
(blueprint: def-sf-native-finite-composition-coordinates).
Proof: the specified arrow is exactly the composite of these three factors, with the
first change carried by the second compact-support functor. -/
theorem forward_isIso {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (K : D Λ X)
    [IsIso (change Λ c (Compactification.Triangle.ofRestrict d (e.ofComp d)).cf K)]
    [IsIso (tower Λ (Compactification.Triangle.ofRestrict d (e.ofComp d)) K)]
    [IsIso (change Λ (Compactification.Triangle.ofRestrict d (e.ofComp d)).cfg e K)] :
    IsIso (forward Λ c d e K) := by
  unfold forward
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing.NativeFiniteComposition

namespace AlgebraicGeometry.ProEtale.CondensedRing.FiniteProjectionComposition

open CompactificationReindexing

/-- The residue characteristic is nilpotent in the actual level-n coefficient ring.
Source: coefficient-extension definition and its DVR theorem, maximal-ideal clause
(blueprint: def-sf-native-finite-composition-coordinates).
Proof: ell has absolute value strictly below one, so belongs to the recorded maximal
ideal. That ideal is generated by the chosen uniformizer. Its nth power contains
ell^n, which therefore vanishes in the quotient defining the coefficient ring.
This argument includes n=0, where the quotient is the zero ring. -/
theorem coefficientExtensionRing_pow_eq_zero (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) :
    (ell : Padic.coefficientExtensionRing ell E n) ^ n = 0 := by
  let R := Padic.coefficientExtensionIntegers ell E
  let m := Padic.coefficientExtensionMaximalIdeal ell E
  have h := (Padic.extension_integers_dvr ell E
    (Padic.coefficientExtensionAbsoluteValue ell E)
    (spectralNorm_extends (K := ℚ_[ell]) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer ell E} : Set R) = m :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : (ell : R) ∈ m := by
    apply h.2.1 _ |>.mpr
    change spectralNorm ℚ_[ell] E (ell : E) < 1
    rw [← map_natCast (algebraMap ℚ_[ell] E) ell, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hmem : (ell : R) ^ n ∈ Padic.coefficientExtensionIdeal ell E n := by
    change (ell : R) ^ n ∈ Ideal.span ({Padic.coefficientExtensionUniformizer ell E} :
      Set R) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hm n
  simpa only [map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem

end AlgebraicGeometry.ProEtale.CondensedRing.FiniteProjectionComposition
