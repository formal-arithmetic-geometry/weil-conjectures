/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.EtaleTensorUnitSectionsNatural
import Sheaf.AlgebraicGeometry.EtaleQcoherentULiftFiniteCechComparison
import Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalData
import Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalTransfer

/-! # Étale additive cohomology in ordinary Čech coordinates

Source: Stacks Project, Tags 03P2 and 01FD.
(blueprint: lem-pbc-etale-additive-cech-inverse-image)
-/

@[expose] public section

universe u
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Affine-intersection Čech coordinates compute lifted additive étale cohomology.
The coordinates respect multiplication and represent inverse-image classes by
matching structural-function cocycles. No ordinary Ext comparison occurs here.

Source: Stacks Project, Tag 03P2, separated-case proof of
etale-cohomology-theorem-zariski-fpqc-quasi-coherent; Tag 01FD,
cohomology-lemma-cech-functorial, augmented double-complex diagram.
(blueprint: lem-pbc-etale-additive-cech-inverse-image)

Proof: Regard the open covers as covers in the small étale sites. The unit module
has canonical structural-function sections, and the fixed additive sheaf is their
coefficient lift. Every tuple intersection is affine. Affine quasi-coherent étale
acyclicity, also with lifted coefficients, makes the coefficient augmentation of
the injective Čech double complex a quasi-isomorphism. The global-sections
augmentation is a quasi-isomorphism by injective Čech acyclicity. Their inverses
on cohomology identify Ext cohomology with the ordered section Čech homology.
Lower every lifted coordinate; structural-function restrictions identify this
complex with cechOver for the unit and the canonical map to Spec of global
functions. In each degree the tuple index is finite. Lowering commutes with these finite
products, kernels, images and alternating differentials.
Multiplication acts coordinatewise, so this identification carries the stipulated
endomorphism to scalar multiplication on homology. For g use the refined-cover
structural pullback map of section complexes. The adjunction unit defining its
étale coefficient map gives precisely structural pullback on each intersection.
Use exists_resolutionSection_canonical_comparison to normalize the resolution
section comparisons on cocycles. The augmented double-complex diagram of 01FD
and resolutionSection_canonical_transfer identify the inverse-image homology map
with exact étale inverse image. Compose with an augmentation-preserving resolution
lift of the adjoint coefficient map; the extMk cocycle formula identifies its
homology map with Sheaf.H.map of that coefficient map. These constructions fix
the edge maps; naturality is not inferred from an arbitrary Nonempty comparison.
Choose a
cycle representing the source class and take its image under this section chain
map as the target cycle. This gives both homology equalities and the displayed
coordinate matching. Degree zero is gluing of sections with structural pullback.
Empty intersections have zero sections; an empty covering index forces both
schemes empty. Neither flatness nor affineness of g is used. -/
theorem exists_etaleAdditive_cech_inverseImage
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    [CompactSpace X] [CompactSpace Y] [X.IsSeparated] [Y.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hV : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, V (y l)))
    (hcover : iSup U = ⊤) (hcover' : iSup V = ⊤)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (μX : Γ(X, ⊤) → (X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf))
    (μY : Γ(Y, ⊤) → (Y.etaleAdditiveSheaf ⟶ Y.etaleAdditiveSheaf))
    (hμX : ∀ r (W : X.Etaleᵒᵖ) (x : X.etaleAdditiveSheaf.obj.obj W),
      (μX r).hom.app W x =
        ULift.up ((show Γ(W.unop.left, ⊤) from x.down) *
          (show Γ(W.unop.left, ⊤) from W.unop.hom.appTop r)))
    (hμY : ∀ r (W : Y.Etaleᵒᵖ) (x : Y.etaleAdditiveSheaf.obj.obj W),
      (μY r).hom.app W x =
        ULift.up ((show Γ(W.unop.left, ⊤) from x.down) *
          (show Γ(W.unop.left, ⊤) from W.unop.hom.appTop r)))
    (n : ℕ) :
    ∃ a : Sheaf.H X.etaleAdditiveSheaf n ≃+
        (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homology n,
    ∃ a' : Sheaf.H Y.etaleAdditiveSheaf n ≃+
        (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).homology n,
      (∀ r x, a (Sheaf.H.map (μX r) n x) = r • a x) ∧
      (∀ r x, a' (Sheaf.H.map (μY r) n x) = r • a' x) ∧
      ∀ x,
        ∃ z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n,
        ∃ z' : (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).cycles n,
          (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homologyπ n z =
            a x ∧
          (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).homologyπ n z' =
            a' (Sheaf.H.map
              (((Etale.upperStarLowerStarAdjunction _ g).homEquiv _ _).symm
                (Scheme.etaleAdditiveSheafToLowerStar g)) n
              (Etale.cohomologyMap g X.etaleAdditiveSheaf n x)) ∧
          ∀ y : Fin (n + 1) → ι,
            cechCoordinate Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf) n y
                ((cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).iCycles n z') =
              (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf).presheaf.map
                (homOfLE (hinter n y)).op
                ((SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app
                  (op (⨅ l, U (y l)))
                  (cechCoordinate X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf) n y
                    ((cechOver X.toSpecΓ U
                      (SheafOfModules.unit X.ringCatSheaf)).iCycles n z))) := by sorry

end AlgebraicGeometry.Scheme.Modules
