module

public import Sheaf.AlgebraicGeometry.SpaceGroupTorsion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.NormalEtaleComponentsClopen
import WeilConjectures.RingTheory.EtaleNormalRing
import WeilConjectures.AlgebraicGeometry.NormalConstantOpenUnit
import WeilConjectures.AlgebraicGeometry.EtaleSetConstantPullbackComparison

/-! # Extension of torsion frames over a normal base

Source: Deligne, Le lemme de Gabber, Lemma 3.5.2, printed p.140.
(blueprint: lem-sfb-normal-base-torsion-frame-extension)
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The restriction unit is injective and every open torsion frame extends uniquely
as a monomorphism into the constant label sheaf. The uniqueness quantifies over all
module-sheaf morphisms, so in particular identifies any transported extension whose
open frame is the specified one; labels are transported by the identity comparison.

Source: Deligne, Lemma 3.5.2, printed p.140
(blueprint: lem-sfb-normal-base-torsion-frame-extension).

Proof:
1. Apply `lem-a1-normal-etale-components-clopen` to the identity of S. Its normal
locally Noetherian components are disjoint integral open-and-closed subschemes, and
V meets each nonempty component. The empty base gives the zero sheaf case.
2. An etale test T is normal, by `lem-weil-pbc-etale-over-normal-ring-normal` and
`lem-weil-pbc-affine-open-stalk-localization`; thus T is reduced.
3. The open T_V is dense because etale maps are open
(`lem-weil-pbc-etale-morphism-open-map`). Two sections agreeing there have a closed
equalizer by the separated diagonal. Its ideal is contained in every prime, hence
zero on reduced T. This proves injectivity of the restriction unit, using
`lem-weil-pbc-etale-inverse-image-restriction` to identify it with restriction.
4. On each integral normal component, `lem-weil-pbc-normal-constant-generic-open-unit`
makes the constant-label unit an isomorphism. Glue the unique inverses on the
disjoint component cover, including infinitely many components.
5. Compose the torsion unit, the direct image of alpha and the inverse constant-label
unit. This is a linear monomorphism restricting to alpha.
6. Restriction of a label section is injective by step 4, so any other linear map
restricting to alpha equals this composite. A base isomorphism and group isomorphism
preserving the open frame transport an extension to another such map. Uniqueness
identifies them, with identity on the constant labels. -/
theorem normal_base_torsion_frame_extension
    {S V : Scheme.{u}} [IsLocallyNoetherian S]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (j : V ⟶ S) [IsOpenImmersion j] (hdense : DenseRange j.base)
    (N : AlgebraicSpace S) (H : CommutativeSpaceGroup N)
    (hsmooth : MapIsLocally (@Smooth) (groupSpaceProjection N))
    (hseparated : MapIsSeparated (groupSpaceProjection N))
    (hfp : MapIsLocallyOfFinitePresentation (groupSpaceProjection N) ∧
      MapIsQuasiCompact (groupSpaceProjection N).hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal (groupSpaceProjection N).hom.hom))
    (hsemiabelian : HasSemiabelianSpaceFibres H) (habelian : IsAbelianOn H j)
    (n : ℕ) (hn : 1 ≤ n)
    (hinvertible : ∀ s : S, IsUnit (n : S.presheaf.stalk s)) (r : ℕ) :
    Mono ((Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) j).unit.app (spaceTorsionSheaf H n)) ∧
    ∀ α : (Etale.localizationRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) j inferInstance).obj
          (spaceTorsionSheaf H n) ≅ torsionLabels V n r,
      ∃ β : spaceTorsionSheaf H n ⟶ torsionLabels S n r,
        Mono β ∧
        (Etale.localizationRestriction
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) j inferInstance).map β ≫
            (torsionLabelsRestriction j n r).hom = α.hom ∧
        (∀ γ : spaceTorsionSheaf H n ⟶ torsionLabels S n r,
          (Etale.localizationRestriction
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) j inferInstance).map γ ≫
              (torsionLabelsRestriction j n r).hom = α.hom → γ = β) ∧
        (∀ (S' : Scheme.{u}) (h : S ≅ S') (N' : AlgebraicSpace S')
          (H' : CommutativeSpaceGroup N')
          (e : H.points ≅ (Over.map h.hom).op ⋙ H'.points)
          (β' : spaceTorsionSheaf H' n ⟶ torsionLabels S' n r),
          (Etale.localizationRestriction
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) j inferInstance).map
              (spaceTorsionTransport h H H' e n ≫
                (Etale.localizationRestriction
                  (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) h.hom inferInstance).map β' ≫
                  (torsionLabelsRestriction h.hom n r).hom) ≫
                    (torsionLabelsRestriction j n r).hom = α.hom →
          β = spaceTorsionTransport h H H' e n ≫
            (Etale.localizationRestriction
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) h.hom inferInstance).map β' ≫
              (torsionLabelsRestriction h.hom n r).hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
