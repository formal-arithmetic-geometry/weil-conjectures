/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.CategoryTheory.SiteModuleSheafGluing

/-!
# Gluing local finite coefficient models after enlarging the field

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) descent paragraph,
overlap and gluing steps (blueprint: lem-weil-pbc-condensed-local-model-gluing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Finite affine local coefficient models glue after one finite enlargement.

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) descent paragraph;
Stacks Tags 04TR, 04TQ and 03EL
(blueprint: lem-weil-pbc-condensed-local-model-gluing).

Proof: the pairwise and triple overlaps of the finite affine cover are qcqs since X
is quasi-separated. The coefficient colimit and the Hom part of the qcqs section
calculus, with tensor adjunction, descend the overlap comparisons induced by the
local isomorphisms to M and their inverses. A common finite enlargement contains
all these maps and enforces the inverse, diagonal and cocycle equations, by eventual
equality in the Hom colimit. The ringed-site gluing theorem constructs the module
and its local identifications. The existing equivalence
`CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence` transports
this gluing statement between internal module objects and sectionwise module sheaves.
Its forward functor keeps the underlying abelian sheaves and restrictions. It sends
the regular module to the regular sectionwise module and, being an equivalence,
preserves coproducts and cokernels, hence finite presentations. Compatibility with
restriction is sectionwise; compatibility with extension of scalars follows by
identifying their restriction-of-scalars right
adjoints. Weakly-etale localization identifies slice restrictions with the covering
schemes. The pullback-tensor
comparison makes the extended local maps agree. Sheaf-Hom gluing applied to these
maps and their inverses gives the global scalar-extension isomorphism. Uniqueness
proves both inverse identities. The local identifications are retained explicitly;
no finite-presentation assertion for the glued module is assumed in this lemma.
An empty cover glues the zero module, so it is included. -/
theorem exists_finiteCoefficient_gluing_of_local_models
    (T X : Scheme.{u}) [QuasiSeparatedSpace X]
    (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hfinite : Finite U.I₀) (haffine : ∀ i, IsAffine (U.X i))
    (N : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
    (hN : ∀ i, Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (N i))
    (e : ∀ i, Nonempty ((Mod.extendScalars
      ((upperStar Ab.{u + 1} (U.f i)).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj
          (N i) ≅
      ((upperStar Ab.{u + 1} (U.f i)).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)) :
    ∃ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F)
      (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))),
      (∀ i, Nonempty (
        ((upperStar Ab.{u + 1} (U.f i)).mapMod
          ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))).obj P ≅
        (Mod.extendScalars ((upperStar Ab.{u + 1} (U.f i)).map
          ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))).obj (N i))) ∧
      Nonempty ((Mod.extendScalars
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj P ≅ M) := by
  sorry

end AlgebraicGeometry.ProEtale
