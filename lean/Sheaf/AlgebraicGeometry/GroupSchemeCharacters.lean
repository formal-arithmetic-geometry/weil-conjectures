module

public import Sheaf.AlgebraicGeometry.PointedTorsorLineCharacterDescent

/-! # Characters of group schemes on arbitrary parameter schemes

Source: Milne, Algebraic Groups (2017), Section 11c, printed pp.213--214,
definition preceding Theorem 11.12 and the Cartier pairing paragraph.
(blueprint: def-sfb-group-scheme-characters)

This definition interface reuses the existing character hom-set and Laurent-coordinate
value without introducing a second construction. It requires no torsor, line module,
finiteness, or classification theorem. Its two abbreviations are definitionally the
existing `PointedTorsor.Characters` and `PointedTorsor.value`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.GroupSchemeCharacters

/-- The hom-set of T-group schemes G_T → Gₘ,T, with the canonical pulled-back group laws.
This is the existing hom-set, exposed through a definition-node interface.
Source: Milne, Section 11c, p.213, definition before Theorem 11.12.
(blueprint: def-sfb-group-scheme-characters) -/
abbrev Characters {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    (T : Over (Spec (.of k))) :=
  PointedTorsor.Characters G T

/-- Pull back the Laurent coordinate t along a character and an arbitrary scheme-valued
point of G_T. The projection Gₘ,T → Gₘ is the canonical first pullback projection.
Source: Milne, Section 11c, pp.213--214, character values and Cartier pairing.
(blueprint: def-sfb-group-scheme-characters) -/
abbrev value {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
    {T S : Over (Spec (.of k))} (χ : Characters G T) (z : S ⟶ G ⊗ T) : Γ(S.left, ⊤) :=
  PointedTorsor.value χ z

end AlgebraicGeometry.GroupSchemeCharacters
