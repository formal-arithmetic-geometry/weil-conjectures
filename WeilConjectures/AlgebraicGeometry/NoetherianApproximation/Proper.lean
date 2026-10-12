/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.FinitePresentation

/-!
# Properness descends to a finite stage of a cofiltered limit

Let `{Dⱼ}` be a cofiltered system of quasi-compact quasi-separated schemes with affine transition
morphisms and limit `lim Dⱼ`, and let `p : Y ⟶ Dᵢ` be separated, quasi-compact and of finite
presentation. If the base change of `p` to `lim Dⱼ` is proper, then so is its base change to
some stage `Dⱼ` (Stacks, Tag 081F; EGA IV₃, 8.10.5 (xii)).

## Proof

By Nagata's compactification theorem `p` factors as an open immersion `Y ⟶ Ȳ` followed by a
proper morphism `Ȳ ⟶ Dᵢ`. Over the limit, the open immersion of the base change of `Y` into the
base change of `Ȳ` is proper, so its image `U` is clopen; the complement `W` is a quasi-compact
open. Both `W` and the relations `U ∩ W = ∅`, `U ∪ W = ⊤` descend to a finite stage
(Stacks, Tag 01Z4), where `Y ×_{Dᵢ} Dⱼ` becomes a clopen, hence closed, subscheme of the proper
`Dⱼ`-scheme `Ȳ ×_{Dᵢ} Dⱼ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}

/-- **Properness descends to a finite stage** (Stacks, Tag 081F). Let `{Dⱼ}` be a cofiltered
system of quasi-compact quasi-separated schemes with affine transition morphisms and limit cone
`c`, and let `p : Y ⟶ Dᵢ` be separated, quasi-compact and of finite presentation. If the base
change of `p` to `lim Dⱼ` is proper, then the base change of `p` to some stage `Dⱼ` is proper. -/
theorem Scheme.exists_isProper_pullback_snd_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (hc : IsLimit c) {i : I} {Y : Scheme.{u}}
    (p : Y ⟶ D.obj i) [IsSeparated p] [LocallyOfFinitePresentation p] [QuasiCompact p]
    [IsProper (pullback.snd p (c.π.app i))] :
    ∃ (j : I) (f : j ⟶ i), IsProper (pullback.snd p (D.map f)) :=
  sorry

end AlgebraicGeometry
