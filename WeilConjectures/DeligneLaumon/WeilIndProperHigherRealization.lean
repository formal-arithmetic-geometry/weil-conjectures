/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.WeilGeometricFiberProperties
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.DeligneLaumon.ConstructibleTruncations
import WeilConjectures.DeligneLaumon.WeilIndProperHigherRealizationExists
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Realization of proper higher image on represented Weil ind-sheaves

Source: SGA 4, XVII, proper-image comparison; Bhatt--Scholze 6.8.14--6.8.15;
Barrett, arXiv:2005.10859, Theorem 1.1; Kashiwara--Schapira, §15.3.
(blueprint: lem-zl-ind-proper-higher-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Every representation of the higher proper ind-image has the prescribed
constructible cohomology as its underlying object. This is a proper-only comparison:
there is no open extension or composite compactification in the statement.
Source: SGA 4, XVII, proper image; Bhatt--Scholze 6.8.14--6.8.15; Barrett,
arXiv:2005.10859, Theorem 1.1; Kashiwara--Schapira, Categories and Sheaves, §15.3
(blueprint: lem-zl-ind-proper-higher-realization).

Proof: over a finite coefficient field identify the bounded derived category of the
ordinary constructible heart with the constructible derived category by Barrett's
realization theorem. The exact Yoneda embedding into its ind-category is fully
faithful on bounded derived categories. The normalized inverse-image adjunction
therefore identifies higher ind right image with the cohomology of proper derived
image. Proper finiteness ensures that this cohomology lies in the constructible
heart. On finite affine target charts these identifications respect restriction,
since they are fixed by the adjunction unit. The finite Cech resolution glues them
without absolute separatedness. Forgetting the Weil structure preserves injectives:
its left adjoint is the exact direct sum of the Frobenius iterates. Thus it computes
the same higher images. The integral proper-image realization has, at each positive
reduction, exactly the proper compact-support functor for the identity-open
compactification. Its normalized Roos comparison identifies this realization with
the integral value. Rationalization and finite-stage inclusion commute with the
standard cohomology functors and the proper adjunction mates. Hence this comparison
is the stated one for every normalized coefficient action. Full faithfulness of
the Weil embedding makes the result independent of the chosen representative H.
This applies also to n=0, the identity proper map, zero sheaves and empty schemes. -/
theorem zlIndWeilProperHigher_realization
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left]
    (S : SfCompactSupportCoefficientAction l D.k (zlRealizationPrimeUnit D l hl) Ω
      (.ofIsProper (zlFiberMap D p₀)))
    (n : ℕ) (G : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (H : sfCommonStageWeilSheaf D l hl Y₀ Ω)
    (e : (zlWeilIndEmbedding D l hl Ω Y₀).obj H ≅
      ((zlIndWeilPush D l hl Ω p₀).rightDerived n).obj
        ((zlWeilIndEmbedding D l hl Ω X₀).obj G)) :
    Nonempty (H.obj.carrier ≅
      (constructibleTruncationCohomology
        (sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl) (n : ℤ)).obj
          (S.system.functor.obj G.obj.carrier)) := by
  obtain ⟨H₀, ⟨e₀, h₀⟩⟩ := zlIndWeilProperHigher_realization_exists
    D l hl Ω p₀ S n G
  obtain ⟨e₀⟩ := e₀
  obtain ⟨hfull, hfaith⟩ := zlWeilIndEmbedding_full_faithful D l hl Ω Y₀
  let E := zlWeilIndEmbedding D l hl Ω Y₀
  let _ : E.Full := hfull
  let _ : E.Faithful := hfaith
  obtain ⟨hcarrier⟩ := h₀
  let i := E.preimageIso (e ≪≫ e₀.symm)
  let ih : H.obj.carrier ≅ H₀.obj.carrier :=
    asIso ((Endofunctor.IsoAlgebra.forget _).map i.hom.hom)
  exact ⟨ih ≪≫ hcarrier⟩

end WeilConjectures
