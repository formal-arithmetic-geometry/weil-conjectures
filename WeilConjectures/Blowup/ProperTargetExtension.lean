/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.PartialSectionExtension
public import WeilConjectures.Blowup.QuasiDomination

/-!

# Extension of a morphism to a proper target after an admissible blow-up

If `X` is quasi-compact and quasi-separated, `U ⊆ X` is a dense quasi-compact open and
`y : Y ⟶ S` is proper, then every morphism `U ⟶ Y` over `S` extends to the whole of a
`U`-admissible blow-up `X'` of `X`:

```text
   π⁻¹(U) ──π∣_U──→ U ──f──→ Y
      │                      │
    ι │                      │ y
      ↓                      ↓
      X' ───π───→ X ───x───→ S
```

with `g : X' ⟶ Y` satisfying `g ≫ y = π ≫ x` and `ι ≫ g = (π ∣_ U) ≫ f`.

The two inputs are:

- the partial-section extension theorem
  `AlgebraicGeometry.exists_admissibleBlowup_extend_section`, which is a statement about a
  *section* of a morphism `p : Y' ⟶ X` to the base `X` and has no auxiliary base `S`. To
  apply it here one first performs Conrad's reduction `Y ⇝ Y ×ₛ X`: take
  `p := pullback.snd y x : Y ×ₛ X ⟶ X`, which is separated, locally of finite type and
  quasi-compact as a base change of the proper `y`, with qcqs source because `X` is qcqs and
  `p` is quasi-compact and separated; the morphism `f` then becomes the section
  `pullback.lift f U.ι hf` of `p`. The theorem produces an extension over *some* open
  `W ⊆ X'` containing `π⁻¹(U)`, together with the closedness of its graph;
- `AlgebraicGeometry.QuasiDomination.U_eq_top`, which turns that closed graph into `W = X'`:
  the extension is a quasi-domination of `X'` over `Y`, and a quasi-domination over a
  universally closed target is defined everywhere.

## Main results

- `AlgebraicGeometry.exists_admissibleBlowup_extend_of_isProper`: the extension statement
  above.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Blueprint `sk-cor-nagata-sketch-proper-extension`: Extension to a proper target.

Let `X` be quasi-compact and quasi-separated over `S`, let `U ⊆ X` be a dense quasi-compact
open and let `y : Y ⟶ S` be proper. Then every `S`-morphism `f : U ⟶ Y` extends to a
morphism `g` defined on all of a `U`-admissible blow-up `π : X' ⟶ X` of `X`.

```text
   π⁻¹(U) ──π∣_U──→ U ──f──→ Y
      │                      │
    ι │                      │ y
      ↓                      ↓
      X' ───π───→ X ───x───→ S
```

with `g : X' ⟶ Y` satisfying `g ≫ y = π ≫ x` and `ι ≫ g = (π ∣_ U) ≫ f`.
-/
theorem exists_admissibleBlowup_extend_of_isProper {S X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (x : X ⟶ S) (y : Y ⟶ S) [IsProper y] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hUdense : Dense (U : Set X)) (f : U.toScheme ⟶ Y)
    (hf : f ≫ y = U.ι ≫ x) :
    ∃ (B : IsAdmissible X U) (g : B.I.blowup ⟶ Y), g ≫ y = B.I.blowupMap ≫ x ∧
      (B.I.blowupMap ⁻¹ᵁ U).ι ≫ g = (B.I.blowupMap ∣_ U) ≫ f := by
  sorry

end AlgebraicGeometry
