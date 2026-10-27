/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
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

/-- Internal Hom of two constructible sheaves is bounded constructible.

Source: Bhatt--Scholze, Remark 6.8.15 and Propositions 6.6.11 and 6.8.11(3);
SGA 4½, Th. finitude 1.6, for finite-coefficient internal Hom on finite-type
schemes over a field with the coefficient prime invertible.
(blueprint: lem-sfb-dc-hom-single)

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
comparison and constructible Hom continuity. Isometric coefficient isomorphisms
cover arbitrary finite normed extensions and their closed unit balls. Characteristic
zero is included: the finite-coefficient finiteness theorem requires invertibility
of l, which follows from the characteristic condition. Empty schemes and zero
modules use the same comparisons and vanishing bounds. -/
theorem boundedConstructible_hom_single
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))
    (hF : IsConstructibleModuleObject (condensedRingObj Λ X.left) F)
    (hG : IsConstructibleModuleObject (condensedRingObj Λ X.left) G) :
    boundedConstructible (condensedRingObj Λ X.left)
      (((derivedHom Λ X.left).obj (op ((DerivedCategory.singleFunctor _ 0).obj F))).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
