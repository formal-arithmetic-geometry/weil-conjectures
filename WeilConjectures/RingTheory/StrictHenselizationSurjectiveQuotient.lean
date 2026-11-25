/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
import WeilConjectures.RingTheory.PointedEtaleQuotientFinal

/-! # Strict henselization and surjective local quotients

If `A → B` is a surjection of local rings with kernel `I` and `C` is a strict henselization of
`A`, then `C ⧸ IC` is a strict henselization of `B`.

## Implementation details

Base change of pointed étale algebras along `A → B` is final, and extension of scalars is a
left adjoint, so it carries the universal cocone presenting `C` to a universal cocone with
vertex `B ⊗[A] C ≅ C ⧸ IC`.

## References

* [Stacks, Tag 05WS]
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

/-- Let `π : A → B` be a surjection of local rings with kernel
`I`, and let `C` be the strict henselization of `A` with respect to `K`. Then `C ⧸ I C`,
with the `B`-algebra structure induced by `π` (the hypothesis `hcomp`; it is unique since
`π` is surjective), is the strict henselization of `B` with respect to any separable
closure `L` of the residue field of `B`. Since `κ(A) ≅ κ(B)`, `L` may be taken to be `K`. -/
theorem IsStrictHenselization.surjective_quotient
    (A K C B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C)
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π) (I : Ideal A) (hker : RingHom.ker π = I)
    [Algebra B (C ⧸ I.map (algebraMap A C))]
    (hcomp : (algebraMap B (C ⧸ I.map (algebraMap A C))).comp π =
      (Ideal.Quotient.mk _).comp (algebraMap A C)) :
    IsStrictHenselization B L (C ⧸ I.map (algebraMap A C)) := by
  obtain ⟨c, ⟨hc⟩, ⟨e⟩⟩ := hC
  obtain ⟨F, hF, ⟨α⟩⟩ := pointedEtaleQuotient_final A K B L π hπ
  have : F.Final := hF
  let t := (Cocone.precompose α.inv).obj ((quotientBaseChange π).mapCocone c)
  have ht : IsColimit t :=
    (IsColimit.precomposeInvEquiv α _).symm
      (isColimitOfPreserves (quotientBaseChange π) hc)
  let d := (Functor.Final.extendCocone (F := F)).obj t
  have hd : IsColimit d := (Functor.Final.isColimitExtendCoconeEquiv F t).symm ht
  exact ⟨d, ⟨hd⟩,
    ⟨(quotientBaseChange π).mapIso e ≪≫
      quotientBaseChangeObjIso A B C π hπ I hker hcomp⟩⟩

end Algebra
