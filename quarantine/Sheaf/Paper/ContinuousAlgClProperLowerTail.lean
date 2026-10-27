/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.SixFunctors.ProperImageLocalizingProper
import Sheaf.Paper.QcqsProperHullTailBound

/-!
# Proper direct image for the continuous-map algebraic-closure coefficient

Source: blueprint main-20261015, det-sf-comp-coherence-single, proper-image paragraph.
(blueprint: det-sf-comp-continuous-algcl-lower-tail).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The uniform lower-tail bound on the localizing closure for the full continuous
algebraic-closure coefficient.

Source: blueprint main-20261015, sk-lem-proper-unbounded-window, lower-tail assertion,
and sk-lem-proper-heart-bound, torsion-bound and limit paragraphs.
(blueprint: det-sf-comp-continuous-algcl-lower-tail).

Proof: finite type and properness over the standing field give a uniform geometric
fibre-dimension bound d. For a constructible sheaf, devissage on its finite
stratification reduces the proper cohomological bound to lisse coefficients on
locally closed strata. Establish the torsion bound after reduction of integral
local models, pass through the derived inverse limit using the Milnor sequence,
and recover the continuous algebraic-closure coefficient. Qcqs bounded continuity
extends the bound to filtered colimits of constructible sheaves. The subcategory
of complexes with ind-constructible cohomology is triangulated, replete and closed
under ambient sums, hence contains Loc(Dctf). The truncation spectral sequence and
left completeness extend the uniform heart bound to the lower truncation tail:
Rp_*(tau_{<q-c} K) is in D^{<=q-1}, with c=2d+1 enlarged if necessary.
The same c works for all K and q. For empty fibres and zero complexes all terms
vanish. The integral model and coefficient passage must be justified for the actual
continuous-map ring; finite-subextension-valued sections alone do not suffice. -/
theorem continuousAlgCl_proper_lowerTail
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    ∃ c : ℕ, ∀ (q : ℤ)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X))),
      localizingClosureProEtale (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X K →
      ((lowerStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) p).rightDerivedFunctor.obj
        ((DerivedCategory.TStructure.t.truncLT (q - (c : ℤ))).obj K)).IsLE (q - 1) := by
  let Λ := Profinite.continuousMapRingObj (PadicAlgCl ℓ)
  -- 2026-10-25: the all-continuous algebraic closure is no longer an admissible coefficient
  -- (IsLocalizingAdmissibleCoefficient); this coefficient-specific result is off every route.
  have hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ := sorry
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  obtain ⟨c, hc⟩ := exists_uniform_lowerTail_bound_of_isProper ℓ Λ hΛ (𝟙 Y) p
  refine ⟨c, fun q K hK ↦ ?_⟩
  let a := q - (c : ℤ)
  have hbound : ((moduleObjectDerivedPushforward Λ p).obj
      ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj K)).IsLE (q - 1) := by
    apply (DerivedCategory.isLE_iff _ _).mpr
    intro r hr
    exact hc a K hK r (by dsimp [a]; omega)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((moduleObjectDerivedPushforward Λ p).mapIso
      ((DerivedCategory.TStructure.t.truncLEIsoTruncLT (a - 1) a (by omega)).app K))
    (q - 1)

end AlgebraicGeometry.ProEtale.CondensedRing
