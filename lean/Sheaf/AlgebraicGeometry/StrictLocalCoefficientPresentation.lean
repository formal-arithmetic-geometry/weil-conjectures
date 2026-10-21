/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.ZetaSeries
import Sheaf.AlgebraicGeometry.StrictLocalCoefficientChart
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale

/-!
# Coefficient field and an étale presentation of a strict localization

Source: Stacks Project, Tags 0F0U and 0F0X, coefficient-field construction and étale stages
(blueprint: lem-kun-strict-local-coefficient-presentation).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Choose a generic polynomial chart and its separable coefficient field, retaining the
étale presentation over the affine chart. This does not assert finite-type models over `L`.

Source: Stacks Project, Tag 0F0U, proof before the compatible-model footnote, and Tag 0F0X,
second paragraph (blueprint: lem-kun-strict-local-coefficient-presentation).

Proof: take the affine chart and compatible coefficient field from
`exists_strictLocal_coefficient_chart`. The affine-spectrum chart contains the point, and
its composite with the spectrum of the chosen structural ring map is the strict-local
structural map. Apply `smallStrictHenselization_indEtale_of_affine_chart` with the identity
identification of the strict-local spectrum. Unpack the ind-étale ring presentation to a
small filtered ring diagram with compatible maps from the chart ring and colimit vertex
the actual strict-local ring. Regard those structural maps as objects under the chart
ring and the transition maps as under-morphisms. The cocone has the same vertex and legs;
forgetting under-objects recovers the supplied colimit exactly. Its spectrum identification
is the identity, so the two scalar equations and the structural-map equation are retained.
The affine étale criterion gives étaleness of each stage.
-/
theorem exists_strictLocal_coefficient_presentation
    {K : Type u} [Field K] (Y : Scheme.{u}) [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    ∃ U : Y.Opens, s (IsLocalRing.closedPoint Ω) ∈ U ∧
      ∃ hU : IsAffineOpen U,
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsSepClosed L),
        Algebra.trdeg K L =
          @Algebra.trdeg K (Y.residueField (s (IsLocalRing.closedPoint Ω))) _ _
            (((Y ↘ Spec (.of K)).residueFieldAlgebraMap
              (s (IsLocalRing.closedPoint Ω))).toAlgebra) ∧
        ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
          (_ : Algebra R L) (_ : Algebra (FractionRing R) L)
          (_ : IsScalarTower R (FractionRing R) L)
          (_ : Algebra.IsAlgebraic (FractionRing R) L)
          (r : CommRingCat.of R ⟶ Γ(U.toScheme, ⊤))
          (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
          (E : I ⥤ Under Γ(U.toScheme, ⊤)) (c : Cocone E)
          (h : L →+* c.pt.right)
          (e : strictHenselizationScheme s ≅ Spec c.pt.right),
          Nonempty (IsColimit ((Under.forget _).mapCocone c)) ∧
          Nontrivial c.pt.right ∧
          e.hom ≫ Spec.map c.pt.hom ≫ (@Scheme.isoSpec U.toScheme hU).inv ≫ U.ι =
            strictHenselizationStructuralMap s ∧
          r ≫ c.pt.hom = CommRingCat.ofHom (algebraMap R L) ≫ CommRingCat.ofHom h ∧
          (ΓSpecIso (.of K)).inv ≫ (U.ι ≫ (Y ↘ Spec (.of K))).appTop ≫ c.pt.hom =
            CommRingCat.ofHom (algebraMap K L) ≫ CommRingCat.ofHom h ∧
          ∀ i : I, Etale (Spec.map (E.obj i).hom) := by
  classical
  obtain ⟨U, hU, hAff, L, hL, hKL, hSep, htr,
    R, hR, hDom, hRL, hFL, hTower, hAlg, r, a, h, hB, he, hr, hK⟩ :=
    exists_strictLocal_coefficient_chart (K := K) Y s
  let : IsAffine U.toScheme := hAff
  have hi : s (IsLocalRing.closedPoint Ω) ∈
      Set.range (U.toScheme.isoSpec.inv ≫ U.ι) := by
    refine ⟨U.toScheme.isoSpec.hom ⟨_, hU⟩, ?_⟩
    change U.ι ((U.toScheme.isoSpec.hom ≫ U.toScheme.isoSpec.inv) ⟨_, hU⟩) = _
    rw [Iso.hom_inv_id]
    rfl
  let : Algebra Γ(U.toScheme, ⊤) (strictHenselizationRing s) := a.hom.toAlgebra
  have hind : Algebra.IndEtale Γ(U.toScheme, ⊤) (strictHenselizationRing s) :=
    smallStrictHenselization_indEtale_of_affine_chart s Γ(U.toScheme, ⊤)
      (U.toScheme.isoSpec.inv ≫ U.ι) hi (Iso.refl _) a.hom (by simpa using he)
  have hh : a.hom.IndEtale := hind
  obtain ⟨I, hI, hFilt, D, t, b, hb, hStages⟩ :=
    (RingHom.IndEtale.iff_exists a).mp hh
  let := hI
  let := hFilt
  let E : I ⥤ Under Γ(U.toScheme, ⊤) :=
    { obj := fun i ↦ Under.mk (t.app i)
      map := fun {i j} f ↦ Under.homMk (D.map f) (by
        change t.app i ≫ D.map f = t.app j
        exact (t.naturality f).symm.trans (Category.id_comp _)) }
  let c : Cocone E :=
    { pt := Under.mk a
      ι := { app := fun i ↦ Under.homMk (b.app i) (hStages i).2
             naturality := fun i j f ↦ by
               apply Under.UnderMorphism.ext
               change D.map f ≫ b.app j = b.app i ≫ 𝟙 _
               exact b.naturality f } }
  refine ⟨U, hU, hAff, L, hL, hKL, hSep, htr,
    R, hR, hDom, hRL, hFL, hTower, hAlg, r, I, hI, hFilt, E, c, h, Iso.refl _,
    ⟨?_⟩, hB, ?_, hr, hK, ?_⟩
  · exact hb
  · change Spec.map a ≫ U.toScheme.isoSpec.inv ≫ U.ι = _
    exact he
  · intro i
    exact HasRingHomProperty.Spec_iff.mpr (hStages i).1

end AlgebraicGeometry.Scheme
