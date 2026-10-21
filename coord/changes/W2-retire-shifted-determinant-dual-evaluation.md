# AlgebraicGeometry.shiftedDeterminant_dual_evaluation

## Reason

Complete the explicit retirement assignment in coord/retire-items.tsv:1911,
under coord/changes/retire-sheaf-twins-20261020.md. This is a zero-hole item.
The duplicate differs from the adopted theorem only in using exteriorSheaf
rather than exteriorPower. The existing exteriorSheafPowerIso identifies the
sheafified exterior powers, and mapping each comparison through the single
functor and the respective shift transports the upstream evaluation to exactly
the legacy statement, with the independent universes u and w retained.

There are no active Lean importers. The one listed consumer is preserved at
quarantine/Sheaf/AlgebraicGeometry/SmoothProperRelativeDualizing.lean, as its
current coord/rework.tsv row records. It is NOT unused or withdrawn: its Lean
attachment, existing theorem, dependency edges and archive remain intact.
Its evaluation input is itself quarantined, and restoring its import chain would
require 64 additional quarantined modules. This packet does not restore that
unrelated rework cluster or change its archives. The exact needed restoration
edit and a compiled verification of the mathematical API conversion follow.

The node lem-sc-shifted-determinant-dual-evaluation retains its mathematical
statement, all incoming references and unit membership. Its Lean attachment now
points to the adopted theorem. Its proof follows the same ordinary determinant,
K-flat single-complex, and cancelling-shift route. The comparison is needed at
the legacy consumer boundary, not in the adopted theorem itself. No target,
definition or upstream source file changes. Degree zero, the empty scheme, and
independent derived universes remain covered by the uniform comparison.

## Old

In Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation:

```lean
theorem shiftedDeterminant_dual_evaluation
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : X.Modules) (d : ℕ) (hfree : M.IsFiniteLocallyFreeOfRank d) :
    Nonempty ((((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
        (Scheme.Modules.exteriorSheaf
          (SheafOfModules.homObj (R := X.sheaf) M
            (SheafOfModules.unit X.ringCatSheaf)) d))⟦-(d : ℤ)⟧ ⊗
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (Scheme.Modules.exteriorSheaf M d))⟦(d : ℤ)⟧) ≅
      𝟙_ (schemeDerivedCategory X))
```

The archived consumer privately imports that module and calls:

```lean
  obtain ⟨v⟩ := shiftedDeterminant_dual_evaluation X f.relativeDifferentials d hfree
```

## New

Use the already proved theorem in
WeilConjectures.AlgebraicGeometry.ShiftedDeterminantDualEvaluation:

```lean
theorem shiftedDeterminant_dual_evaluation
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : X.Modules) (d : ℕ) (hfree : M.IsFiniteLocallyFreeOfRank d) :
    Nonempty ((((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
        (Scheme.Modules.exteriorPower
          (SheafOfModules.homObj (R := X.sheaf) M
            (SheafOfModules.unit X.ringCatSheaf)) d))⟦-(d : ℤ)⟧ ⊗
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (Scheme.Modules.exteriorPower M d))⟦(d : ℤ)⟧) ≅
      𝟙_ (schemeDerivedCategory X))
```

Withdraw only the assigned active duplicate using deleted.txt. Preserve the
quarantine archive. When its independent rework restores the consumer, replace
its private import with:

```lean
import WeilConjectures.AlgebraicGeometry.ShiftedDeterminantDualEvaluation
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison
```

Add MonoidalCategory to the consumer's open namespaces for the tensor notation.
Replace only the call above by this block; N and D are the consumer's unchanged
legacy shifted determinant objects. Its final monoidal cancellation is unchanged:

```lean
  obtain ⟨vPower⟩ := shiftedDeterminant_dual_evaluation X f.relativeDifferentials d hfree
  let T := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
  let v : N ⊗ D ≅ 𝟙_ (schemeDerivedCategory X) :=
    MonoidalCategory.tensorIso
      ((shiftFunctor _ (-(d : ℤ))).mapIso
        (T.mapIso (Scheme.Modules.exteriorSheafPowerIso
          (SheafOfModules.homObj (R := X.sheaf) f.relativeDifferentials
            (SheafOfModules.unit X.ringCatSheaf)) d)))
      ((shiftFunctor _ (d : ℤ)).mapIso
        (T.mapIso (Scheme.Modules.exteriorSheafPowerIso f.relativeDifferentials d))) ≪≫ vPower

```

The following complete scratch verification derives the exact old statement
from the new one. It compiled through lcompile.py in 3.6 seconds, exit 0,
with no warnings; its printed axioms are exactly propext, Classical.choice,
and Quot.sound. It is recorded here for the independent reader and restoration,
not added as a new library declaration or a renamed copy of the obligation.

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import WeilConjectures.AlgebraicGeometry.ShiftedDeterminantDualEvaluation
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison

/-! # The shifted determinant of the dual evaluates against the determinant

Source: Stacks Project, Tag 0BRT, determinant inversion in the conclusion of the proof.
(blueprint: lem-sc-shifted-determinant-dual-evaluation).
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The shifted top exterior powers of a finite locally free sheaf and its dual are
mutually inverse derived tensor objects.
Source: Stacks Project, Tag 0BRT, final determinant inversion.
(blueprint: lem-sc-shifted-determinant-dual-evaluation).

Proof: on an open cover trivializing M as O_X^d, use a basis e₁,...,e_d and its dual.
The determinant evaluation pairs their top wedges to 1 and is therefore an isomorphism
from wedge^d M^dual tensor wedge^d M to O_X on that cover. A basis change multiplies
the two determinant generators by inverse determinants, so this evaluation is
independent of the chosen bases and glues. Sectionwise exterior powers sheafify to
these local determinant lines, and internal Hom restricts to the dual free module.
Both determinant lines are locally free of rank one, hence flat, so their ordinary
product computes their derived tensor product. The single functor in degree zero
therefore carries the evaluation to an isomorphism with the derived unit. Compatibility
of derived tensor with shifts identifies the displayed product with that unshifted
product shifted by -d+d=0. Compose with the zero-shift isomorphism. When d=0 the empty
wedge is the structure sheaf and the evaluation is multiplication; the same argument
works on an empty scheme as well. -/
theorem shiftedDeterminant_dual_evaluation_transport_check
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : X.Modules) (d : ℕ) (hfree : M.IsFiniteLocallyFreeOfRank d) :
    Nonempty ((((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
        (Scheme.Modules.exteriorSheaf
          (SheafOfModules.homObj (R := X.sheaf) M
            (SheafOfModules.unit X.ringCatSheaf)) d))⟦-(d : ℤ)⟧ ⊗
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (Scheme.Modules.exteriorSheaf M d))⟦(d : ℤ)⟧) ≅
      𝟙_ (schemeDerivedCategory X)) := by
  obtain ⟨vPower⟩ := shiftedDeterminant_dual_evaluation X M d hfree
  let T := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
  exact ⟨tensorIso
    ((shiftFunctor _ (-(d : ℤ))).mapIso
      (T.mapIso (Scheme.Modules.exteriorSheafPowerIso
        (SheafOfModules.homObj (R := X.sheaf) M
          (SheafOfModules.unit X.ringCatSheaf)) d)))
    ((shiftFunctor _ (d : ℤ)).mapIso
      (T.mapIso (Scheme.Modules.exteriorSheafPowerIso M d))) ≪≫ vPower⟩

end AlgebraicGeometry

#print axioms AlgebraicGeometry.shiftedDeterminant_dual_evaluation_transport_check

```

The exact final consumer cancellation also passed lcompile.py in 4.4 seconds,
with only propext, Classical.choice and Quot.sound. In this scratch verification,
the sole quarantined dependency is represented by its exact output isomorphism e;
all scheme, smoothness, adjunction, universe and legacy conclusion binders remain.
This check is not substituted for the consumer theorem or delivered as a lemma.
It confirms the consumer edit once its independent evaluation input is restored:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ShiftedDeterminantDualEvaluation
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison
/-! # The dualizing complex of a smooth proper morphism

Source: Stacks Project, Tag 0BRT, Lemma 48.15.7
(blueprint: lem-sc-smooth-proper-relative-dualizing-general).
-/

@[expose] public section

set_option linter.unusedVariables false

universe u wX wS

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- For a smooth proper morphism of relative dimension `d` over a Noetherian scheme,
the right adjoint of derived pushforward takes the structure sheaf to `Ωᵈ[d]`.
Source: Stacks Project, Tag 0BRT, Lemma 48.15.7
(blueprint: lem-sc-smooth-proper-relative-dualizing-general).

`R` and `comparison` specify the restriction of the recorded derived direct image to
quasi-coherent complexes; `adj` identifies `a` as its right adjoint. `O` and `hO` specify
the structure sheaf in degree zero in that full subcategory. Relative differentials are
the shared sheaf `f.relativeDifferentials`, canonically the diagonal conormal sheaf
(Tag 08S2); `exteriorSheaf` is its sheafified sectionwise exterior power.

Proof, following the node:
1. Properness implies finite type, so `X` and `X ×_S X` are Noetherian
(lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-proper-base-change).
The Noetherian adjoint theorem supplies right adjoints `a` and `c` for `f` and its diagonal
(lem-pc-noetherian-derived-direct-image-right-adjoint).
2. The diagonal is a Koszul-regular immersion of codimension `d`, hence perfect and proper
(lem-sc-smooth-proper-diagonal-koszul-regular).
3. Smoothness implies flatness (lem-pc-smooth-flat). The diagonal evaluation identity gives
`O_X ≅ c(Lpr₁* a(O_S))` (lem-sc-smooth-proper-diagonal-pushforward-structure, Tag 0E2Q).
4. The perfect-immersion projection formula identifies this with
`LΔ* Lpr₁* a(O_S) ⊗ᴸ c(O_{X ×_S X})`
(lem-sc-smooth-proper-diagonal-tensor-formula, Tag 0A9U).
5. Koszul duality identifies `c(O_{X ×_S X})` with `⋀ᵈ N_Δ[-d]`
(lem-sc-smooth-proper-diagonal-koszul-dual, Tag 0BR0).
6. The diagonal conormal sheaf is `Ω¹_{X/S}`
(lem-sc-smooth-proper-diagonal-conormal-differentials, Tag 08S2).
7. Since `pr₁ ∘ Δ = id`, these give `O_X ≅ a(O_S) ⊗ᴸ ⋀ᵈ N_Δ[-d]`.
The conormal sheaf is finite locally free of rank `d`
(lem-sc-smooth-omega-finite-locally-free), so its dual has invertible top exterior power.
Cancel that shifted invertible object. Its inverse is `⋀ᵈ C_Δ[d] = Ωᵈ_{X/S}[d]`, giving
the asserted isomorphism. -/
theorem smoothProper_dualizing_retirement_check
    (X S : Scheme.{u}) [CompactSpace S] [IsLocallyNoetherian S]
    (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory S)
    (comparison : R ⋙ (schemeDerivedQCohProperty S).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory X)
    (adj : R ⊣ a) (O : schemeDerivedQCohCategory S)
    (hO : O.obj ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings S.toRingedSpace))) :
    ∀ e : ((a.obj O).obj ⊗
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (Scheme.Modules.exteriorSheaf
            (SheafOfModules.homObj (R := X.sheaf) f.relativeDifferentials
              (SheafOfModules.unit X.ringCatSheaf)) d))⟦-(d : ℤ)⟧ ≅
        𝟙_ (schemeDerivedCategory X)),
    Nonempty ((a.obj O).obj ≅
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (Scheme.Modules.exteriorSheaf f.relativeDifferentials d))⟦(d : ℤ)⟧) := by
  intro e
  let A := (a.obj O).obj
  let N := ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
      (Scheme.Modules.exteriorSheaf
        (SheafOfModules.homObj (R := X.sheaf) f.relativeDifferentials
          (SheafOfModules.unit X.ringCatSheaf)) d))⟦-(d : ℤ)⟧
  let D := ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
      (Scheme.Modules.exteriorSheaf f.relativeDifferentials d))⟦(d : ℤ)⟧
  have hfree := f.isFiniteLocallyFreeOfRank_relativeDifferentials d
  obtain ⟨vPower⟩ := shiftedDeterminant_dual_evaluation X f.relativeDifferentials d hfree
  let T := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
  let v : N ⊗ D ≅ 𝟙_ (schemeDerivedCategory X) :=
    MonoidalCategory.tensorIso
      ((shiftFunctor _ (-(d : ℤ))).mapIso
        (T.mapIso (Scheme.Modules.exteriorSheafPowerIso
          (SheafOfModules.homObj (R := X.sheaf) f.relativeDifferentials
            (SheafOfModules.unit X.ringCatSheaf)) d)))
      ((shiftFunctor _ (d : ℤ)).mapIso
        (T.mapIso (Scheme.Modules.exteriorSheafPowerIso f.relativeDifferentials d))) ≪≫ vPower
  exact ⟨(MonoidalCategory.rightUnitor A).symm ≪≫
    MonoidalCategory.tensorIso (Iso.refl A) v.symm ≪≫
    (MonoidalCategory.associator A N D).symm ≪≫
    MonoidalCategory.tensorIso e (Iso.refl D) ≪≫ (MonoidalCategory.leftUnitor D)⟩

end AlgebraicGeometry

#print axioms AlgebraicGeometry.smoothProper_dualizing_retirement_check

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | W2 | Retire the duplicate; zero direct holes. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed; quarantined | Preserve archive and statement; exact shifted comparison transport above applies on restoration. |
| WeilConjectures.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Adopted replacement, unchanged. |

The active downstream scan has zero importers. A search including quarantine/
finds exactly the archived consumer above. Its parent node still cites the same
shifted-determinant node and resolves through the new attachment. The unit record
sk-thm-picard-duality realizes neither of these helper nodes as an independent
unit step; the mathematical determinant-cancellation step remains unchanged.
The adopted theorem passed an independent lcompile.py import-and-axiom check in
2.0 seconds, with only propext, Classical.choice and Quot.sound.
The replacement's project source closure has 337 modules, no missing sources,
no Sheaf modules, and therefore no Sheaf/upstream twin pair.

## Status

landed 20261021T154105-L-2792525 2026-10-21 (merge of deliver/W2/Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation)
