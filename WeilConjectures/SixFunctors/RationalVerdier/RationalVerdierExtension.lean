/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionInvertibility
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierComparisonNaturality
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierComparisonEvaluation
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierComparisonBiduality

/-! # Canonical rational comparison for one finite coefficient extension

Source: blueprint thm-coef-rational-verdier, proof
(blueprint: lem-coef-rational-verdier-extension). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The localized integral u and beta give normalized coefficient comparisons.
Source: thm-coef-rational-verdier, proof step 6; current blueprint proof,
paragraph 3 (blueprint: lem-coef-rational-verdier-extension).

Proof: apply integral finite coefficient extension to the given coherent
presentations wE and wL. The ordinary tensor presentations of A and B compute
the same derived tensor and internal Hom as the presentations supplied there:
their representative normalizations identify the adjunction counits and hence
the evaluation-defined beta. Thus u and beta are invertible for these
presentations as well. On the unchanged rational objects take their images
under integral-to-rational localization as the comparison components. The
object and pure-tensor formulas of A, B and scalar extension identify their
endpoints. Integral naturality of beta, multiplied by the coefficient, proves
naturality on pure tensors, hence by additivity on all maps. The localized
integral inverses give inverse natural transformations. The omega map is the
localization of u. Conjugate the ordinary tensor scalar comparison by the
normalized completion maps of A and B; representative uniqueness identifies
this with the specified completed scalar tensor comparison. Localize the
integral evaluation and delta squares and use the normalization equations in
A and B. These are precisely the last two clauses of ExtensionProperties.
Identity embeddings and zero objects require the same formulas.
The naturality hypotheses hA and hB are needed for the biduality clause: a
SignedSymmetry is pinned only on literal K-flat pairs, while delta uses the swap at
(RHom(K, omega), K), so without naturality A.bidual could be negated on all such K
and the delta square would fail. Natural swaps agreeing with the Koszul sign on
K-flat pairs are unique, since every derived object is isomorphic to a K-flat one;
the counit choices of A.ordinary and B.ordinary cancel between delta and beta. -/
theorem extension_exists
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : Datum D l hl X E wE) (B : Datum D l hl X L wL)
    (hA : ∀ (K M K' M' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X))
      (f : K ⟶ K') (g : M ⟶ M'),
      A.ordinary.tensor.map (Prod.mkHom f g) ≫ (A.symmetry.swap K' M').hom =
        (A.symmetry.swap K M).hom ≫ A.ordinary.tensor.map (Prod.mkHom g f))
    (hB : ∀ (K M K' M' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l L X))
      (f : K ⟶ K') (g : M ⟶ M'),
      B.ordinary.tensor.map (Prod.mkHom f g) ≫ (B.symmetry.swap K' M').hom =
        (B.symmetry.swap K M).hom ≫ B.ordinary.tensor.map (Prod.mkHom g f)) :
    ∃ e : Extension D l hl X E L i wE wL A B,
      ExtensionProperties D l hl X E L i wE wL A B e := by
  let T := integralScalar l X E L i
  let Q := sfRationalConstructibleLocalization l L X
  let R := scalar l X E L i
  let DE := IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves
  let DL := IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves
  obtain ⟨_, hu, hv⟩ := IntegralFiniteExtension.comparison_invertibility
    l E L i X D hl wE wL A.ordinary B.ordinary
  have := hu
  let u : T.obj wE.omega ⟶ wL.omega := ObjectProperty.homMk
    (IntegralFiniteExtension.u l E L i X D hl wE wL)
  have : IsIso u := (ObjectProperty.isIso_hom_iff u).mp hu
  have hR (K : sfRationalConstructibleCategory l E X) :
      R.obj K = Q.obj (T.obj K.obj) :=
    sfRationalScalarExtension_obj l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i K
  let omega := eqToIso (hR ⟨wE.omega⟩) ≪≫ Q.mapIso (asIso u)
  have huQ : HEq omega.hom (Q.map u) :=
    eqToHom_comp_heq (Q.map u) (hR ⟨wE.omega⟩)
  have hsource (K : sfRationalConstructibleCategory l E X) :
      R.obj (A.dual.obj (op K)) = Q.obj (T.obj (DE.obj (op K.obj))) := by
    rw [A.objects K]
    exact hR _
  have htarget (K : sfRationalConstructibleCategory l E X) :
      B.dual.obj (op (R.obj K)) = Q.obj (DL.obj (op (T.obj K.obj))) := by
    rw [hR K]
    exact B.objects _
  let beta (K : sfIntegralConstructibleCategory l E X) :
      T.obj (DE.obj (op K)) ⟶ DL.obj (op (T.obj K)) :=
    ObjectProperty.homMk
      (IntegralFiniteExtension.beta l E L i X D hl wE wL A.ordinary B.ordinary
        K.obj K.property.1)
  have hbeta (K : sfIntegralConstructibleCategory l E X) : IsIso (beta K) := by
    have hvK : IsIso (IntegralFiniteExtension.v l E L i X A.ordinary B.ordinary
        K.obj wE.omega.obj K.property.1 wE.omega.property.1) := hv K wE.omega
    apply (ObjectProperty.isIso_hom_iff (beta K)).mp
    change IsIso (IntegralFiniteExtension.beta l E L i X D hl wE wL
      A.ordinary B.ordinary K.obj K.property.1)
    unfold IntegralFiniteExtension.beta
    exact IsIso.comp_isIso' hvK
      ((IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)).mapIso
        (Iso.prod (Iso.refl _)
          (@asIso _ _ _ _ (IntegralFiniteExtension.u l E L i X D hl wE wL) hu))).isIso_hom
  let c (K : sfRationalConstructibleCategory l E X) :
      R.obj (A.dual.obj (op K)) ≅ B.dual.obj (op (R.obj K)) :=
    eqToIso (hsource K) ≪≫ Q.mapIso (@asIso _ _ _ _ (beta K.obj) (hbeta K.obj)) ≪≫
      (eqToIso (htarget K)).symm
  have hc (K : sfIntegralConstructibleCategory l E X) :
      HEq ((c ((sfRationalConstructibleLocalization l E X).obj K)).hom) (Q.map (beta K)) := by
    apply (conj_eqToHom_iff_heq _ _ (hsource ⟨K⟩) (htarget ⟨K⟩)).mp
    rfl
  have hn (K M : sfRationalConstructibleCategory l E X) (f : K ⟶ M) :
      (A.dual ⋙ R).map f.op ≫ (c K).hom =
        (c M).hom ≫ (R.op ⋙ B.dual).map f.op :=
    localizedBeta_naturality D l hl X E L i wE wL A B (fun K ↦ (c K).hom) hc K M f
  let e : Extension D l hl X E L i wE wL A B :=
    ⟨omega, NatIso.ofComponents (fun K ↦ c K.unop) (fun f ↦ hn _ _ f.unop)⟩
  have heval := normalizedExtension_evaluation D l hl X E L i wE wL A B e huQ hc
  exact ⟨e, huQ, hc, heval,
    evaluation_implies_biduality D l hl X E L i wE wL A B hA hB e heval⟩

end WeilConjectures.RationalVerdier
