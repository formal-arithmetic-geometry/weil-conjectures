/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ScalarSixPullback

/-! # Scalar change commutes with the canonical image-factorization extension.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (3), thickness and scalar induction.
(blueprint: lem-sfb-scalar-six-canonical-extension-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exactPushTransport.{v, w}
    {A B C D : Type w}
    [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{v} A] [HasDerivedCategory.{v} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [hK : Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (P : C ⥤ D) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (e : A ≌ C) (h : B ≌ D)
    [e.functor.Additive] [e.inverse.Additive]
    [h.functor.Additive] [h.inverse.Additive]
    (r : F ⋙ h.functor ≅ e.functor ⋙ P) :
    Nonempty (F.rightDerivedFunctor ≅
      e.functor.mapDerivedCategory ⋙ P.mapDerivedCategory ⋙ h.inverse.mapDerivedCategory) := by
  let q := r.isoCompInverse (H := h)
  let : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso q.symm
  let : PreservesFiniteColimits F := preservesFiniteColimits_of_natIso q.symm
  let d : F.mapDerivedCategory ⋙ h.mapDerivedCategory.functor ≅
      e.mapDerivedCategory.functor ⋙ P.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso F h.functor).symm ≪≫
      Functor.mapDerivedCategoryNatIso r ≪≫
      Functor.mapDerivedCategoryCompIso e.functor P
  exact ⟨F.rightDerivedFunctorIsoMapDerivedCategory ≪≫
    d.isoCompInverse (H := h.mapDerivedCategory) ≪≫ Functor.associator _ _ _⟩

private theorem canonicalClosedPushComparison
    (E : LocallyClosedExtensionData.{u}) (G : ScalarSixGeometry.{u})
    (Λ : ScalarSixRing.{u}) {k : Type u} [Field k]
    {Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (c : Z ⟶ X) [IsClosedImmersion c.left] :
    Nonempty ((lowerStar Λ.X c.left).rightDerivedFunctor ≅
      scalarSixClosedPush E G Λ c) := by
  let : Abelian (ModuleRingedComparison.modules Λ.X Z.left) :=
    @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1}
      Z.left.ProEt inferInstance (ProEt.topology Z.left)
      ((sheafCompose (ProEt.topology Z.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (scalarSixSectionRing Λ Z.left))
      SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1}
      SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}
  let : Abelian (ModuleRingedComparison.modules Λ.X X.left) :=
    @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1}
      X.left.ProEt inferInstance (ProEt.topology X.left)
      ((sheafCompose (ProEt.topology X.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (scalarSixSectionRing Λ X.left))
      SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1}
      SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}
  let b := scalarSixImmersion G Λ c
  let e := E.closedComparison b (inferInstanceAs (IsClosedImmersion c.left))
  let : b.push.Additive := Functor.additive_of_iso e
  let : PreservesFiniteLimits b.push := preservesFiniteLimits_of_natIso e
  let : PreservesFiniteColimits b.push := preservesFiniteColimits_of_natIso e
  let : (ModuleRingedComparison.equivalence Λ.X Z.left).functor.Additive :=
    scalarSixEquivalenceAdditive Λ Z.left
  let : (ModuleRingedComparison.equivalence Λ.X Z.left).inverse.Additive :=
    scalarSixEquivalenceInverseAdditive Λ Z.left
  let : (ModuleRingedComparison.equivalence Λ.X X.left).functor.Additive :=
    scalarSixEquivalenceAdditive Λ X.left
  let : (ModuleRingedComparison.equivalence Λ.X X.left).inverse.Additive :=
    scalarSixEquivalenceInverseAdditive Λ X.left
  exact exactPushTransport.{u + 1, u + 2}
    (hK := Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1})
    (A := ModuleRingedComparison.internalModules Λ.X Z.left)
    (B := ModuleRingedComparison.internalModules Λ.X X.left)
    (C := ModuleRingedComparison.modules Λ.X Z.left)
    (D := ModuleRingedComparison.modules Λ.X X.left)
    (lowerStar Λ.X c.left) b.push
    (ModuleRingedComparison.equivalence Λ.X Z.left)
    (ModuleRingedComparison.equivalence Λ.X X.left) (G.push Λ c.left)

/-- Scalar change commutes with the canonical image-factorization extension.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (3), thickness and scalar induction.
(blueprint: lem-sfb-scalar-six-canonical-extension-comparison).

Proof in words: give S and the image closure the induced k-structures. The immersion
into the Noetherian finite-type X makes them separated finite type and
quasi-compact. Apply scalarSixPullback, clause (2), to the induced immersion in the
over-category. Its normalized comparison uses the published section-module locally
closed extension. The internal/sectionwise equivalence carries this extension to
openImmersionLowerShriek along i.toImage followed by the closed module pushforward
along i.imageι: the coefficient action is restriction along the published adjunct,
as fixed by ScalarSixGeometry.pushNormalization. Exactness identifies its termwise
derived functor with the ordinary open derived functor followed by the closed right
derived functor. Conjugate the normalized beta comparison by these two canonical
identifications, and evaluate at Q. This gives the stated isomorphism for arbitrary
coefficient maps, without flatness or a constructibility assumption on Q. -/
theorem sfbCanonicalExtensionScalarComparison
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (S : Scheme.{u}) (i : S ⟶ X.left) (hi : IsImmersion i)
    (Q : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S)) :
    Nonempty ((scalarSixChange a X.left).obj
        ((sfbLocallyClosedDerivedExtension Λ i hi).obj Q) ≅
      (sfbLocallyClosedDerivedExtension Λ' i hi).obj ((scalarSixChange a S).obj Q)) := by
  classical
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := {}
  let : IsImmersion i := hi
  let : TopologicalSpace.NoetherianSpace S := i.isEmbedding.isInducing.noetherianSpace
  obtain ⟨G, C, h⟩ := scalarSixPullback.{u}
  obtain ⟨E, _hE, D, O, ⟨B⟩⟩ := h ell k
  let Z : Over (Spec (.of k)) := Over.mk (i.imageι ≫ X.hom)
  let c : Z ⟶ X := Over.homMk i.imageι rfl
  let : IsClosedImmersion c.left := inferInstanceAs (IsClosedImmersion i.imageι)
  let : LocallyOfFiniteType Z.hom :=
    inferInstanceAs (LocallyOfFiniteType (i.imageι ≫ X.hom))
  let : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (i.imageι ≫ X.hom))
  let : IsSeparated Z.hom := inferInstanceAs (IsSeparated (i.imageι ≫ X.hom))
  obtain ⟨d⟩ := canonicalClosedPushComparison E G Λ c
  obtain ⟨d'⟩ := canonicalClosedPushComparison E G Λ' c
  let e := Functor.isoWhiskerRight d (scalarSixChange a X.left) ≪≫
    B.closed a c ≪≫ Functor.isoWhiskerLeft (scalarSixChange a Z.left) d'.symm
  let t := Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (openImmersionLowerShriek Λ.X i.toImage).mapDerivedCategory e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scalarSixOpenScalarIso a i.toImage)
      (lowerStar Λ'.X i.imageι).rightDerivedFunctor ≪≫
    Functor.associator _ _ _
  exact ⟨t.app Q⟩

end AlgebraicGeometry.ProEtale.CondensedRing
