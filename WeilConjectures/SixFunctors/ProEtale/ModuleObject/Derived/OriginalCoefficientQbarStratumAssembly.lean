/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Assembly of finite coefficient models on a qcqs scheme

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes,
Proposition 5.2 and Lemma 7.9, finite coefficient descent.
(blueprint: lem-sp-original-coefficient-qbar-stratum-assembly)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Finite coefficient models on constructible strata assemble, including their extension data.
Source: Hemo--Richarz--Scholbach, Proposition 5.2 and Lemma 7.9.
(blueprint: lem-sp-original-coefficient-qbar-stratum-assembly)

Proof: refine the finite constructible locally closed partition to a finite filtration
by quasi-compact opens with constructible closed complements. All pieces and their
intersections are qcqs. The given stratum models restrict to models on each new piece;
coefficient-compatible pullback and invariance under a surjective closed immersion
handle the possible nonreduced scheme structures. Take a common finite compositum
of the finitely many fields. Induct over the filtration, using the exact open-closed
sequence to express the next module as an extension of closed direct image by open
extension by zero. These two functors preserve constructibility for these constructible
immersions and commute with finite coefficient extension and its filtered union.
Use abelian recollement to express the gluing by a morphism Q -> i^*j_*P between
the closed model and the closed restriction of the open direct image. Qcqs section
continuity identifies the latter coefficient extension with the filtered union of
its finite coefficient extensions. Finite presentation on strata and finite
open-closed devissage make Hom into this diagram commute with that filtered union:
on presentation charts this is a finite equalizer of section groups; gluing maps
and their equalities impose further finite equalizers. Thus the gluing map descends
to a larger finite field. Form the recollement pullback there. Flat coefficient
extension preserves the pullback, and the two restriction isomorphisms identify
its scalar extension with the original module. Its restrictions to the refined
strata give its constructibility.
There are finitely many filtration steps, so one final compositum suffices. Empty
strata and the empty scheme use zero models and the base coefficient field. -/
theorem originalCoefficientQbarStratumAssembly
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ))
    (S : Scheme.Stratification T)
    (hS : ∀ a : Fin S.n,
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (M_E : Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj (padicSubfieldRingObj T ℓ E))),
        IsLocallyFinitelyPresented
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj (padicSubfieldRingObj T ℓ E)) M_E ∧
        Nonempty ((Mod.extendScalars ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).map
          (padicSubfieldRingObjToPadicAlgCl T ℓ E))).obj M_E ≅
            (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod
              (padicAlgClRingObj T ℓ)).obj M))) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (M_E : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)),
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) M_E ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).obj M_E ≅ M) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
