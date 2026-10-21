/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.DerivedNakayamaResolution
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Normalized derived principal quotient cones

Source: blueprint main-20261015, derived Nakayama resolution proof, On X paragraph,
and first-reduction proof, Cones paragraph.
(blueprint: lem-pe-principal-reduction-derived-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PrincipalNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The canonical extension followed by restriction, with positive level n+1.
Source: blueprint Cones paragraph
(blueprint: lem-pe-principal-reduction-derived-normalization). -/
abbrev reduction (n : ℕ) :=
  AdicCompletion.derivedReduction l E X n ⋙ AdicCompletion.restrict l E X n

/-- The scalar principal cone computes the canonical derived quotient functor,
with the quotient maps and adjunction units, and with its standard signed shifts.

Source: blueprint main-20261015, derived Nakayama resolution proof, On X paragraph,
and first-reduction proof, Cones paragraph.
(blueprint: lem-pe-principal-reduction-derived-normalization).

Proof: the scalar formula identifies d with multiplication by the uniformizer.
The resolution theorem gives the short exact sequence R --d^(n+1)--> R --> B_n.
Its cone augments to B_n[0], and its two free terms make it K-flat. Tensoring an
arbitrary complex with this resolution gives the scalar cone, by the signed
cone--tensor interchange. On K-flat complexes, tensoring the augmentation is a
quasi-isomorphism and agrees with extension of scalars followed by restriction:
both balanced maps send a tensor of coefficients and a module section to its
scalar extension. The universal left-derived comparison extends this equality
to all complexes and all derived morphisms. The quotient coefficient map lifts
to (d,id) on the two-term resolutions, so the normalized tensor comparison
identifies its cone map with integralStep. The degree-zero inclusion is the
ordinary scalar-extension unit and hence descends to the specified derived
adjunction unit. The tensor shift comparison has coordinates (x,(-1)^r y),
which is the inverse of mappingCone.shiftIso. Its coherence descends through
localization and gives sF. Tensoring is additive and takes cone triangles to
cone triangles with this boundary sign, proving exactness. These constructions
include zero complexes and empty sites and use no boundedness assumption. -/
theorem derived_principal_normalization
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (hd : ∀ (S : Profinite.{u}ᵒᵖ) (a : (DerivedNakayama.integerRing l E).obj.obj S)
      (s : S.unop), ((d.hom.hom.app S) a).down s =
        Padic.coefficientExtensionUniformizer l E * a.down s)
    (hs : ∀ (n : ℕ) (M : CochainComplex (AdicCompletion.Modules l E X) ℤ),
      DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1 + 1)) M =
        DerivedNakayama.scalarOnComplex l E X d M ≫
          DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M) :
    ∃ (sF : ∀ n : ℕ, (reduction l E X n).CommShift ℤ)
      (κ : ∀ n : ℕ, DerivedNakayama.coneFunctor l E X (d ^ (n + 1)) ≅
        DerivedCategory.Q ⋙ reduction l E X n),
      (∀ n : ℕ, (reduction l E X n).Additive ∧
        @Functor.IsTriangulated _ _ _ _ _ _ (reduction l E X n)
          (sF n) _ _ _ _ _ _ _ _) ∧
      (∀ (n : ℕ) (M : CochainComplex (AdicCompletion.Modules l E X) ℤ),
        DerivedCategory.Q.map (CochainComplex.mappingCone.map
          (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1 + 1)) M)
          (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M)
          (DerivedNakayama.scalarOnComplex l E X d M) (𝟙 M)
          ((Category.comp_id _).trans (hs n M))) ≫ (κ n).hom.app M =
            (κ (n + 1)).hom.app M ≫
              AdicCompletion.integralStep l E X (DerivedCategory.Q.obj M) n) ∧
      (∀ (n : ℕ) (M : CochainComplex (AdicCompletion.Modules l E X) ℤ),
        DerivedCategory.Q.map (CochainComplex.mappingCone.inr
          (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M)) ≫
            (κ n).hom.app M =
          (Mod.derivedExtendMapDerivedCategoryAdjunction
            (AdicCompletion.quotient l E X n)).unit.app (DerivedCategory.Q.obj M)) ∧
      (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (AdicCompletion.Modules l E X) ℤ),
        DerivedCategory.Q.map
            (CochainComplex.mappingCone.shiftIso
              (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M) r).inv ≫
            (DerivedCategory.Q.commShiftIso r).hom.app
              (CochainComplex.mappingCone
                (DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M)) ≫
            ((κ n).hom.app M)⟦r⟧' =
          (κ n).hom.app (M⟦r⟧) ≫
            (reduction l E X n).map ((DerivedCategory.Q.commShiftIso r).hom.app M) ≫
            (Functor.commShiftIso (self := sF n) (reduction l E X n) r).hom.app
              (DerivedCategory.Q.obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale.PrincipalNormalization
