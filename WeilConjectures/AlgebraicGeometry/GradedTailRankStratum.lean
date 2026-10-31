/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GradedSheafGeneration
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Rat.Floor
import WeilConjectures.Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # The simultaneous graded tail rank stratum

Source: Grothendieck, Bourbaki Expose 221, Lemmas 3.4--3.6, printed pp.262--264
(blueprint: lem-sfb-graded-tail-rank-stratum).

The test schemes and the schemes used for base change have no Noetherian hypothesis.
The natural floor of P(d) just reads its nonnegative integral value; integrality is
an explicit hypothesis, so no rounding enters the asserted rank condition.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The rank condition on the ordinary pullbacks of all pieces in degrees at least m.
Source: Bourbaki Expose 221, Lemma 3.4
(blueprint: lem-sfb-graded-tail-rank-stratum). -/
def gradedTailRankCondition {U T : Scheme.{u}} (K : ℕ → U.Modules)
    (P : Polynomial ℚ) (m : ℕ) (g : T ⟶ U) : Prop :=
  ∀ d : ℕ, m ≤ d →
    ((Scheme.Modules.tensorPullback g).obj (K d)).IsFiniteLocallyFreeOfRank
      ⌊P.eval (d : ℚ)⌋₊

/-- Simultaneous prescribed tail ranks are represented by a unique finite-type immersion.
Source: Bourbaki Expose 221, Lemmas 3.4--3.6, printed pp.262--264
(blueprint: lem-sfb-graded-tail-rank-stratum).

Proof: (1) Apply lem-sfb-graded-fibre-hilbert-functions-finite to obtain coherence
of every piece and a finite set H of complete fibre Hilbert functions; no flatness
of the graded module over U is assumed. (2) For each function in H exceeding P
somewhere in the tail, select one offending degree. The intersection of the finitely
many upper-rank opens in lem-sfb-coherent-universal-rank-locus is the open V on
which every tail fibre dimension is at most P. If there are no offending functions,
take V=U. (3) On V the same lemma imposes each rank by a closed subscheme with
quasi-coherent ideal I_d. (4) The sum of these ideals is quasi-coherent, since sums
commute with localization. The construction in
lem-weil-pbc-quasi-coherent-ideal-closed-subscheme gives Z closed in V. Noetherianity
and a finite affine cover show that this ideal sum already uses finitely many degrees.
(5) For any T, the rank tests first force a map into V. Thereafter they say exactly
that its affine ring maps kill all I_d, equivalently their sum. The unique affine
factorizations through the quotient rings glue, giving the stated equivalence for
arbitrary test schemes. (6) Z to V to U is an immersion. Over a Noetherian affine
of U, the open V has a finite principal-open cover; the closed pieces are spectra
of quotients R_f/I, finite-type R-algebras. Thus j is locally of finite type and
quasi-compact, using pqf-lem-affine-open-locnoeth and def-weil-pbc-noetherian-ring.
(7) Immersions are monomorphisms; the universal property identifies the same
subfunctor for any two representatives. Apply lem-pc-representable-unique to obtain
the unique isomorphism over U. (8) Base change the closed and open factors, using
lem-weil-pbc-closed-immersion-base-change. The fibre-product universal property
identifies factorization after base change with factorization of the composite.
The composition comparison of def-pc-module-pullback identifies its rank tests
with the iterated pullbacks displayed below, without a Noetherian assumption on U'. -/
theorem exists_gradedTailRankStratum
    (U : Scheme.{u}) [IsNoetherian U] (B K : ℕ → U.Modules)
    (A : GradedSheafAlgebra B) (M : GradedSheafModule A K)
    (hB : ∀ d : ℕ, SheafOfModules.IsQuasicoherent.{u} (B d))
    (hzero : IsIso A.unit)
    (hone : RingedSpace.IsCoherent U.toRingedSpace (B 1))
    (hgen : A.IsGeneratedInDegreeOne)
    (hK : ∀ d : ℕ, SheafOfModules.IsQuasicoherent.{u} (K d))
    (hM : M.IsLocallyFinitelyGenerated)
    (m : ℕ) (P : Polynomial ℚ)
    (hP : ∀ d : ℕ, m ≤ d → ∃ r : ℕ, P.eval (d : ℚ) = (r : ℚ)) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ U),
      IsImmersion j ∧ LocallyOfFiniteType j ∧ QuasiCompact j ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ U),
        (∃! h : T ⟶ Z, h ≫ j = g) ↔ gradedTailRankCondition K P m g) ∧
      (∀ (Z' : Scheme.{u}) (j' : Z' ⟶ U), IsImmersion j' →
        (∀ (T : Scheme.{u}) (g : T ⟶ U),
          (∃ h : T ⟶ Z', h ≫ j' = g) ↔ gradedTailRankCondition K P m g) →
        ∃! e : Z ≅ Z', e.hom ≫ j' = j) ∧
      (∀ (U' : Scheme.{u}) (b : U' ⟶ U),
        IsImmersion (pullback.snd j b) ∧
        ∀ (T : Scheme.{u}) (t : T ⟶ U'),
          (∃! h : T ⟶ pullback j b, h ≫ pullback.snd j b = t) ↔
            gradedTailRankCondition
              (fun d : ℕ ↦ (Scheme.Modules.tensorPullback b).obj (K d)) P m t) := by
  sorry

end AlgebraicGeometry
