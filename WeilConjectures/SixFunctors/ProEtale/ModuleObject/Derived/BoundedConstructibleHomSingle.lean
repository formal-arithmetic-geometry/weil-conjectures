/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

/-! # Internal Hom of constructible sheaves in degree zero -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

/-! ### The coefficient ring `ℚ̲̄_ℓ` -/

/-- Internal Hom of two constructible `ℚ̄_ℓ`-sheaves placed in degree `0` is bounded
constructible. This is the case of single sheaves in blueprint `lem-sfb-dc-hom-preserves`.

Source: Bhatt--Scholze, Remark 6.8.15 and Propositions 6.6.11 and 6.8.11(3);
SGA 4½, Th. finitude 1.6, for finite-coefficient internal Hom on finite-type
schemes over a field with the coefficient prime invertible.

Proof: For integral coefficients, the finite scalar local models identify each input
with a derived complete complex with constructible residue. Derived Hom into a
complete object remains complete. Its derived residue is the residue internal Hom
by the evaluation-transpose reduction comparison. Finite-coefficient internal-Hom
finiteness on a finite-dimensional finite-type scheme gives bounded constructible
residue with finite Tor amplitude. The cohomological adic criterion gives bounded
constructible integral Hom. This includes torsion finitely presented integral
modules, which have two-term finite free scalar resolutions. For finite field
extensions of Q_l, choose integral constructible lattices, apply the integral case,
and use the canonical internal-Hom comparison after inverting l. For Qbar_l,
descend both inputs to one finite extension and apply the internal-Hom coefficient
comparison and constructible Hom continuity. Characteristic
zero is included: the finite-coefficient finiteness theorem requires invertibility
of l, which follows from the characteristic condition. Empty schemes and zero
modules use the same comparisons and vanishing bounds. -/
theorem boundedConstructible_hom_single
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [Fact (ringChar k ≠ ℓ)]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) F)
    (hG : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) G) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
      (((derivedHom (Profinite.padicAlgClRingObj ℓ) X.left).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj F))).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) := by sorry

/-! ### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj

/-- Internal Hom of two constructible `E`-sheaves placed in degree `0` is bounded constructible,
for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. This is the case of single sheaves in blueprint
`lem-sfb-dc-hom-preserves`; see the `ℚ̲̄_ℓ` case
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_hom_single` for the sources and
the proof sketch. -/
theorem boundedConstructible_hom_single (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [Fact (ringChar k ≠ ℓ)]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left) F)
    (hG : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left) G) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X.left)
      (((derivedHom (Profinite.continuousMapRingObj E) X.left).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj F))).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) := by sorry

end ContinuousMapRingObj

/-! ### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj

/-- Internal Hom of two constructible `𝒪_E`-sheaves placed in degree `0` is bounded
constructible, for a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. This is the case of single sheaves in
blueprint `lem-sfb-dc-hom-preserves`; see the `ℚ̲̄_ℓ` case
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_hom_single` for the sources and
the proof sketch. -/
theorem boundedConstructible_hom_single (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [Fact (ringChar k ≠ ℓ)]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) F)
    (hG : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) G) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)
      (((derivedHom (Profinite.padicIntegersRingObj ℓ E) X.left).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj F))).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) := by sorry

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
