/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed

/-! # Tate twists of condensed Weil complexes

Source: latest blueprint, def-wf-tate-twist, Tate twists and their morphism action
(blueprint: def-wf-tate-twist).

The coefficient line, signed powers and root-normalized Weil structure are the
recorded constructions in `StrictWeilCondensed`. This module tensors with that
specified line, including the inverse tensorator in the Weil structure.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed

/-- Every integer Tate line is locally free of rank one. This uses exactly the
recorded internal/sectionwise module equivalence, with the same underlying sheaf.
Source: latest blueprint, signed lines and local freeness (blueprint: def-wf-tate-twist).
Proof: choose the compatible primitive-root cover. Its root bases trivialize the
finite lines, their integral inverse limits and their rational scalar extensions.
The bases commute with the finite-extension transition maps, so their sheafified
colimit trivializes the algebraic-closure line too. On this same cover each tensor
power, the coefficient unit and each internal dual are the unit. Local rank one
descends, including the zero finite coefficient ring and the empty scheme. -/
theorem tateLine_locallyFree (T : Scheme.{u})
    (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)
    [∀ x : T, Invertible (ell : T.residueField x)] (m : ℤ) :
    (spSignedTwist T (condensedRingObj (c.obj ell) T)
      (c.firstLine ell T) m).IsFiniteLocallyFreeOfRank 1 := by
  sorry

/-- Invertibility of ell on the geometric fibre follows from ell distinct from p.
This constructs the residue-field instances needed by the recorded root lines.
Source: latest blueprint, finite-field datum and ell distinct from p
(blueprint: def-wf-tate-twist). -/
@[instance_reducible] def modelTateEllInvertible (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (T₀ : Over (Spec (.of D.k₀))) :
    ∀ x : (pullback T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) : Scheme.{u}),
      Invertible (ell : (pullback T₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).residueField x) := by
  classical
  letI : Fintype D.k₀ := Fintype.ofFinite _
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (p := D.p) (f := D.a)
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  intro x
  let T := pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  let a : CommRingCat.of D.k₀ ⟶ T.residueField x :=
    (Scheme.ΓSpecIso (.of D.k₀)).inv ≫
      (pullback.fst T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        T₀.hom).appTop ≫ T.Γevaluation x
  exact (show IsUnit (ell : T.residueField x) from by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr
        (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : ell.Prime) hEll.symm)).map
          a.hom).invertible

/-- The finite-field Tate-twist functor of the node. Its geometric automorphism is
exactly id on the model times inverse q-power on the algebraic closure. The coefficient
presentations include finite ell-primary rings, integral and rational finite extensions,
and the finite-subextension-valued algebraic closure. No invertibility assumption beyond
ell distinct from p is imposed on this specialization.
Source: latest blueprint, finite-field setting and displayed twist formula
(blueprint: def-wf-tate-twist). -/
def modelTateTwist (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom]
    [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (c : PurityTransport.Coefficient ell) (m : ℤ) :
    WeilConjectures.condensedStrictWeilComplex (c.obj ell) (modelFrobenius D T₀).hom ⥤
      WeilConjectures.condensedStrictWeilComplex (c.obj ell) (modelFrobenius D T₀).hom :=
  letI := modelTateEllInvertible D ell hEll T₀
  tateTwistFunctor (modelFrobenius D T₀) ell c m

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed
