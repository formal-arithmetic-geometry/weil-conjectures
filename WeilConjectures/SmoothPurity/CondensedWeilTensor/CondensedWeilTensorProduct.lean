/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Tensor Frobenius for ordinary condensed Weil complexes

Source: latest blueprint def-wf-tensor-product, both sentences
(blueprint: def-wf-tensor-product).

This interface uses the existing relative derived tensor and its normalized pullback
comparison. It makes the current definition available without the withdrawn imports of
the previously recorded module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedWeilTensor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (g : X ⟶ X)

/-- The existing K-flat relative derived tensor, evaluated on its two arguments.
Source: latest blueprint def-wf-tensor-product, first sentence
(blueprint: def-wf-tensor-product). -/
abbrev tensor (K L : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  K ⊗ L

/-- The canonical tensor comparison for exact termwise Frobenius pullback, obtained
from the existing K-flat comparison by the exact-to-total-derived identification.
Source: latest blueprint def-wf-tensor-product, monoidal isomorphism
(blueprint: def-wf-tensor-product). -/
def comparison (K L : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (CondensedRing.upperStar Λ g).mapDerivedCategory.obj (K ⊗ L) ≅
      (CondensedRing.upperStar Λ g).mapDerivedCategory.obj K ⊗
        (CondensedRing.upperStar Λ g).mapDerivedCategory.obj L :=
  let ε := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g
  (ε.app (K ⊗ L)).symm ≪≫
    ((CondensedRing.leftDerivedUpperStarTensorIso Λ g).app K).app L ≪≫
      tensorIso (ε.app K) (ε.app L)

/-- The prescribed tensor Frobenius: comparison followed by the tensor of the
supplied structure isomorphisms. Restricting the carriers to bounded constructible
objects gives the tensor Frobenius of Weil complexes; no preservation is assumed.
Source: latest blueprint def-wf-tensor-product, second sentence
(blueprint: def-wf-tensor-product). -/
def frobenius
    (K L : CategoryTheory.Endofunctor.IsoAlgebra
      (CondensedRing.upperStar Λ g).mapDerivedCategory) :
    (CondensedRing.upperStar Λ g).mapDerivedCategory.obj (K.carrier ⊗ L.carrier) ≅
      K.carrier ⊗ L.carrier :=
  comparison Λ g K.carrier L.carrier ≪≫ tensorIso K.str L.str

/-- The recorded tensor Frobenius at the two field coefficients and the geometric
Frobenius of the finite-field model. Actual derived Weil complexes supply these
strict pairs by the recorded realization functor.
Source: latest blueprint def-wf-tensor-product, both sentences
(blueprint: def-wf-tensor-product). -/
abbrev geometricFrobenius (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D₀.p)
    (_hcoeff : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (X₀ : Over (Spec (.of D₀.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (K L : WeilConjectures.condensedStrictWeilComplex Λ (D₀.geometricFrobenius X₀).hom) :
    (CondensedRing.upperStar Λ (D₀.geometricFrobenius X₀).hom).mapDerivedCategory.obj
      (K.obj.carrier ⊗ L.obj.carrier) ≅ K.obj.carrier ⊗ L.obj.carrier :=
  frobenius Λ (D₀.geometricFrobenius X₀).hom K.obj L.obj

end WeilConjectures.CondensedWeilTensor
