module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.ShortExact

/-! # Finite-free internal Hom exactness in arbitrary universes

Source: Stacks Project, Tag 0GM8 via Tag 0GM7; the explicit proof is the
agent-written calculation described below
(blueprint: lem-sc-finite-free-internal-hom-exact-sequence). -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Internal Hom from a finite free module preserves exactness, allowing different
universes for the site and the module sections.
Source: Stacks Project, cohomology.tex, Tag 0GM8, case (2), finite free Hom calculation.
(blueprint: lem-sc-finite-free-internal-hom-exact-sequence)

Proof: choose the displayed finite free basis. On each localized site, evaluate a
linear map on its basis to identify internal Hom with a finite product of the target
module, with the necessary universe lift. Under this identification both maps become
coordinatewise maps. Finite products preserve exact sequences in module sheaves:
a cycle is a finite tuple of cycles; exactness of the original sequence supplies a
local preimage of each coordinate. Refine the finitely many coverings together and
assemble these preimages into the tuple giving a boundary. The universe lift changes
neither the underlying sections nor this local exactness criterion. For rank zero,
all three internal Homs are zero and the assertion is immediate. -/
theorem finiteFree_internalHom_exact_sequence
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    {R : Sheaf J CommRingCat.{w}}
    (P : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (r : ℕ) (e : P ≅ SheafOfModules.free
      (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
      (ULift.{w} (Fin r)))
    (S : ShortComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)))
    (hS : S.Exact) :
    ∃ hz : SheafOfModules.homObjMap (𝟙 P) S.f ≫
        SheafOfModules.homObjMap (𝟙 P) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (𝟙 P) S.f)
        (SheafOfModules.homObjMap (𝟙 P) S.g) hz).Exact := by
  sorry

end CochainComplex
