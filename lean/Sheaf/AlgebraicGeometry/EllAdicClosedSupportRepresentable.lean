/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.Paper.CondensedOpenClosedRecollement
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import all Sheaf.Paper.CondensedFiniteModelProofAPI
import Sheaf.Paper.IntegralConstructibleSerre
import all Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Closed support calculation for adic compact support -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

omit [IsCommMonObj Λ] in
private theorem bc_iso {X : Scheme.{u}}
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (e : K ≅ L)
    (hK : boundedConstructible (condensedRingObj Λ X) K) :
    boundedConstructible (condensedRingObj Λ X) L :=
  ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e hK.1,
    fun n ↦ constructible_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK.2 n)⟩

include ℓ in
private theorem bc_pullback
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left))) (hK : boundedConstructible (condensedRingObj Λ Y.left) K) :
    boundedConstructible (condensedRingObj Λ X.left) (D((f.left)^*⟦Λ⟧).obj K) :=
  bc_iso Λ ((leftDerivedUpperStarIsoMapDerivedCategory Λ f.left).app K)
    (boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K hK)

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private theorem continuous_field_lf
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hM : IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.continuousMapRingObj E) X) M) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod _).obj M) := by
  let E' := ULift.{u} E
  let : NormedField E' :=
    { (inferInstance : NormedCommRing E'), (inferInstance : Field E') with
      norm_mul a b := norm_mul a.down b.down }
  have : IsCommMonObj (Profinite.continuousCoefficientRingObj E') :=
    Sheaf.isCommMonObj_sheafCompose_obj
      (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf E')
      (by
        intro S a b
        apply ULift.ext
        change (a.down * b.down : C(S.unop, E')) = b.down * a.down
        exact mul_comm a.down b.down)
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (liftCoefficientIso E)
  let φ := (upperStarFromPoint X).map e.hom
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (liftCoefficientIso E).hom
  have : IsMonHom φ := inferInstance
  have h := exists_finiteFree_cover_of_condensedField_lfp ℓ E' X
    ((Mod.comap (inv φ)).obj M) (lfp_comap (inv φ) hM)
  exact locally_free_of_iso (locally_free_comap φ h)
    ((Mod.comapEquivalenceOfIsIso φ).counitIso.app M)

private theorem adic_bc_triangulated (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructible (condensedRingObj Λ X)).IsTriangulated := by
  cases hΛ with
  | continuous E =>
    obtain ⟨hk, he⟩ := condensed_constructible_serre_of_locally_free freeEpiLocalSplitting
      (Profinite.continuousMapRingObj E) (continuous_field_lf ℓ E) X
    exact bounded_tri_of_serre _ hk he
  | integral E =>
    let := PadicAlgCl.normedFieldOfAlgebra ℓ E
    let : NormedAlgebra ℚ_[ℓ] E :=
      { norm_smul_le c x := by
          change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
            ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
            PadicAlgCl.norm_extends] }
    obtain ⟨hk, hc, he⟩ := integralConstructible_serre ℓ E X
    change ObjectProperty.IsClosedUnderKernels
      (IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) at hk
    change ObjectProperty.IsClosedUnderCokernels
      (IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) at hc
    change ObjectProperty.IsClosedUnderExtensions
      (IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) at he
    exact isTriangulated_boundedConstructible_of_serre _
  | algebraicClosure =>
    obtain ⟨hk, he⟩ := isConstructibleModuleObject_serre_padicAlgCl X ℓ
    exact bounded_tri_of_serre _ hk he

include ℓ in
/-- The closed-support representative of a bounded constructible complex is bounded
constructible, for each certified adic coefficient ring.

Source: blueprint `sk-thm-existence/sk-thm-existence.proof.md`, geometric restriction
paragraph; `sk-prop-closed-adjoint-constructible/`
`sk-prop-closed-adjoint-constructible-support.proof.md`, localization argument;
`sk-thm-int-restriction/sk-thm-int-restriction-closed.proof.md`.
Proof: the schemes are Noetherian, so the complementary open is quasi-compact.
Open/closed recollement supplies the exact closed pushforward, its bounded-below right
adjoint, and the triangle `i_* Ri! K → K → Rj_* j* K`. The last term is bounded constructible
by exact pullback and the existing direct-image finiteness theorem. The constructible
subcategory is triangulated: for continuous fields use local finite freeness of finitely
presented modules; for integral coefficients use the constructible Serre theorem; for the
algebraic closure use its finite-subextension-valued constructible Serre theorem.
Consequently the first term is bounded constructible. Applying exact `i*` and the invertible
counit `i* i_* ≅ id` shows that `Ri! K` itself is bounded constructible. Include its
bounded-below adjunction counit into the ordinary derived category. Full faithfulness of
the bounded-below inclusion identifies the resulting postcomposition maps with the
adjunction Hom equivalences. Torsion is permitted in the integral case.
(blueprint: lem-sfb-adic-closed-support-representable) -/
theorem closed_support_representable
    {Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (K : (boundedConstructible (condensedRingObj Λ X.left)).FullSubcategory) :
    Exists fun [_hclosed : PreservesFiniteColimits ((i.left)_*⟦Λ⟧)] ↦
      ∃ L : (boundedConstructible (condensedRingObj Λ Z.left)).FullSubcategory,
        ∃ ε : D((i.left)_*⟦Λ⟧).obj L.obj ⟶ K.obj,
          ∀ M : (boundedConstructible (condensedRingObj Λ Z.left)).FullSubcategory,
            Function.Bijective (fun a : M.obj ⟶ L.obj ↦
              D((i.left)_*⟦Λ⟧).map a ≫ ε) := by
  classical
  have : IsFinitenessCoefficient ℓ Λ := by cases hΛ <;> infer_instance
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have : (boundedConstructible (condensedRingObj Λ X.left)).IsTriangulated :=
    adic_bc_triangulated Λ ℓ hΛ X.left
  let W : X.left.Opens :=
    ⟨(Set.range i.left)ᶜ, i.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let V : Over (Spec (.of k)) := Over.mk (W.ι ≫ X.hom)
  let j : V ⟶ X := Over.homMk W.ι rfl
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian W.ι
  have : LocallyOfFiniteType V.hom := by
    change LocallyOfFiniteType (W.ι ≫ X.hom)
    infer_instance
  have : QuasiCompact V.hom := by
    change QuasiCompact (W.ι ≫ X.hom)
    infer_instance
  have : IsSeparated V.hom := by
    change IsSeparated (W.ι ≫ X.hom)
    infer_instance
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion W.ι)
  have : QuasiCompact j.left := inferInstanceAs (QuasiCompact W.ι)
  obtain ⟨hclosed, hr⟩ := condensed_open_closed_recollement Λ i.left j.left W.range_ι
  let _ := hclosed
  rcases hr.2.2.2.2.2.2.2.2.2.2.2.2 with
    ⟨H, hadd, hleft, ash, aj, bj, ai, bi, hjshift, hishift, hrest⟩
  have hcounit := hrest.2.2.2.2.2.2.2.2.2.2.1
  have htri := hrest.2.2.2.2.2.2.2.2.2.2.2.2
  let _ := hadd
  let _ := hleft
  let _ := hjshift
  let _ := hishift
  obtain ⟨δ, ε, htri⟩ := htri
  have hT := htri.2.2.2.1
  let Kp : DerivedCategory.Plus _ := ⟨K.obj, K.property.1.1⟩
  let Lp := H.rightDerivedFunctorPlus.obj Kp
  let T := DerivedCategory.Plus.ι.mapTriangle.obj
    (Pretriangulated.Triangle.mk (bi.counit.app Kp) (bj.unit.app Kp) (ε.app Kp))
  have hTd : T ∈ Pretriangulated.distinguishedTriangles :=
    DerivedCategory.Plus.ι.map_distinguished _ (hT Kp)
  have hthird : boundedConstructible (condensedRingObj Λ X.left) T.obj₃ := by
    have hR := boundedConstructible_rightDerivedLowerStar_obj Λ ℓ j _
      (bc_pullback Λ ℓ j K.obj K.property)
    exact bc_iso Λ
      ((lowerStar Λ j.left).rightDerivedFunctorPlusCompatibility.app
        (D+(upperStar Λ j.left).obj Kp)).symm hR
  have : (boundedConstructible (condensedRingObj Λ X.left)).IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ bc_iso Λ e h⟩
  have hfirst : boundedConstructible (condensedRingObj Λ X.left) T.obj₁ :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₁ _ hTd K.property hthird
  have hpull := bc_pullback Λ ℓ i T.obj₁ hfirst
  have : IsIso (ai.counit.app Lp) := hcounit Lp
  have hL : boundedConstructible (condensedRingObj Λ Z.left) Lp.obj :=
    bc_iso Λ (DerivedCategory.Plus.ι.mapIso (asIso (ai.counit.app Lp))) hpull
  refine ⟨hclosed, ⟨Lp.obj, hL⟩, DerivedCategory.Plus.ι.map (bi.counit.app Kp), ?_⟩
  intro M
  let Mp : DerivedCategory.Plus _ := ⟨M.obj, M.property.1.1⟩
  let e := (ObjectProperty.fullyFaithfulι (DerivedCategory.TStructure.t.plus)).homEquiv.symm
    |>.trans (bi.homEquiv Mp Kp).symm
    |>.trans (ObjectProperty.fullyFaithfulι (DerivedCategory.TStructure.t.plus)).homEquiv
  exact e.bijective

end AlgebraicGeometry.ProEtale.CondensedRing
