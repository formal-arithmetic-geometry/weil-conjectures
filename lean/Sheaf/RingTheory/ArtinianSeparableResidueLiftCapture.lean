module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Artinian.Defs

@[expose] public section

set_option autoImplicit false
universe u v z

namespace Algebra

/-- The finite étale local residue capture data, before deriving Artinianness.
Source: Stacks Project, Smoothing Ring Maps, Tag 07FI, finite étale and henselian
factorization paragraphs.  The omitted Artinian conclusion is derived from finiteness.
(blueprint: lem-weil-pbc-artinian-separable-residue-lift-capture).

Proof: Construct the finite étale lift of the finite separable subextension of the
residue fields, then use henselian factorization and lift the chosen residue element.
This is the construction part of the core theorem; Artinianness of the lifted ring is
separate and follows from its finite module structure over the Artinian base. -/
theorem exists_finiteEtale_artinian_residue_lift_capture
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (b : IsLocalRing.ResidueField S)
    (hb : IsSeparable (IsLocalRing.ResidueField D) b) :
    ∃ (D' : Type (max u v z)) (_ : CommRing D') (_ : Algebra D D') (g' : D' →+* S),
      IsLocalRing D' ∧
      IsLocalHom (algebraMap D D') ∧ IsLocalHom g' ∧
      Etale D D' ∧ Module.Finite D D' ∧
      g'.comp (algebraMap D D') = algebraMap D S ∧
      ∃ d : D', IsLocalRing.residue S (g' d) = b := by
  sorry

end Algebra
