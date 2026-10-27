module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import Sheaf.TraceFormula.LciPointwiseCriterion

/-!
# Local complete intersection coordinate algebras on arbitrary affine opens

Source: Stacks Project, Morphisms, Tag 01UG (lemma-local-complete-intersection),
equivalence of (1) and (3), applied also to an affine open; Algebra, Tag 00SH
(lemma-lci-global), equivalence of (1) and (2).
(blueprint: lem-trf-lci-affine-open-locality)

## Main statement

* `lci_affine_open_locality` transfers the local complete intersection condition
  from an affine open cover to every affine open of a scheme over a field.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- If a scheme over a field has an affine open cover by local complete intersections,
then the coordinate algebra of every affine open is a finitely generated local complete
intersection over that field. Source: Stacks Project, Morphisms, Tag 01UG and Tag 01T2;
Algebra, Tag 00SH (blueprint: lem-trf-lci-affine-open-locality). The displayed theorem is the
canonical project statement for this node.

The cover is given by affine spectra `Spec (C i)` and their open immersions into `Z`.
The displayed commutative square records the `k`-algebra structure on every chart.
The conclusion uses the canonical `k`-algebra structure on `Γ(Z, W)` induced by
`s : Z ⟶ Spec k`; the existential finite-type witness is the finite-generation
clause required by `Algebra.IsLocalCompleteIntersection`. Empty covers and the zero
coordinate algebra are permitted by the conventions in the complete-intersection
definition.

Proof. The affine cover makes `s` locally of finite type. The pointwise criterion
(Tag 01UG) gives complete-intersection local rings on `Z`, and these local rings are
unchanged on an open subscheme. The affine-pair characterization of locally finite
type (Tag 01T2) gives finite generation of `Γ(Z, W)`. Applying the algebraic criterion
(Tag 00SH) to all prime localizations of this finitely generated algebra proves the
local complete-intersection condition. The empty-open case is covered by the
zero-ring convention.
-/
theorem lci_affine_open_locality (k : Type u) [Field k]
    (Z : Scheme.{u}) (s : Z ⟶ Spec (.of k))
    (hcover : ∃ (I : Type u) (C : I → CommRingCat.{u})
      (aC : ∀ i, Algebra k (C i))
      (ftC : ∀ i, Algebra.FiniteType k (C i))
      (φ : ∀ i, Spec (C i) ⟶ Z),
      (∀ i, IsOpenImmersion (φ i)) ∧
        (∀ i, φ i ≫ s =
          Spec.map (CommRingCat.ofHom
            (@algebraMap k (C i) _ _ (aC i)))) ∧
        (∀ z : Z, ∃ i, ∃ x : Spec (C i), φ i x = z) ∧
        (∀ i, @Algebra.IsLocalCompleteIntersection k (C i) _ _
          (aC i) (ftC i))) :
    ∀ (W : Z.Opens), IsAffineOpen W →
      ∃ ftW : @Algebra.FiniteType k (Γ(Z, W)) _ _
          (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ W le_top).hom.toAlgebra),
        @Algebra.IsLocalCompleteIntersection k (Γ(Z, W)) _ _
          (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ W le_top).hom.toAlgebra)
          ftW := by
  classical
  obtain ⟨I, C, aC, ftC, φ, hopen, hφ, hsurj, hlci⟩ := hcover
  let := aC
  let := ftC
  let := hopen
  let cover : Z.OpenCover :=
    Scheme.Cover.mkOfCovers I (fun i ↦ Spec (C i)) φ hsurj hopen
  have : LocallyOfFiniteType s := by
    apply (IsZariskiLocalAtSource.iff_of_openCover cover).mpr
    intro i
    change LocallyOfFiniteType (φ i ≫ s)
    rw [hφ i]
    exact HasRingHomProperty.Spec_iff.mpr (by
      change (algebraMap k (C i)).FiniteType
      exact RingHom.finiteType_algebraMap.mpr (ftC i))
  have hpoints := (lci_pointwise_criterion.{u, u} k Z s).1.mp
    ⟨I, C, aC, ftC, φ, hopen, hφ, hsurj, hlci⟩
  intro W hW
  let : Algebra k Γ(Z, W) :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ W le_top).hom.toAlgebra)
  have : Algebra.FiniteType k Γ(Z, W) := by
    apply RingHom.finiteType_algebraMap.mp
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ W le_top).hom).FiniteType
    exact (s.finiteType_appLE (isAffineOpen_top _) hW le_top).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  refine ⟨inferInstance, ?_⟩
  apply ((lci_pointwise_criterion.{u, u} k Z s).2.2 (Γ(Z, W)) inferInstance
    inferInstance inferInstance).mpr
  intro p hp
  let q : PrimeSpectrum Γ(Z, W) := ⟨p, hp⟩
  have hx : hW.fromSpec q ∈ W := by
    exact (congrArg (fun T : Set Z ↦ hW.fromSpec q ∈ T)
      hW.range_fromSpec).mp ⟨q, rfl⟩
  let x := hW.fromSpec q
  let : Algebra k (Z.presheaf.stalk x) :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ ⊤ le_top ≫
      Z.presheaf.germ ⊤ x trivial).hom.toAlgebra)
  let : Algebra Γ(Z, W) (Z.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨x, hx⟩
  have : IsScalarTower k Γ(Z, W) (Z.presheaf.stalk x) := by
    apply IsScalarTower.of_algebraMap_eq'
    have hcomp : s.appLE ⊤ W le_top ≫ Z.presheaf.germ W x hx =
        s.appLE ⊤ ⊤ le_top ≫ Z.presheaf.germ ⊤ x trivial := by
      rw [← s.appLE_map le_top (homOfLE le_top).op, Category.assoc,
        Z.presheaf.germ_res]
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ ⊤ le_top ≫
      Z.presheaf.germ ⊤ x trivial).hom) =
        (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ W le_top) ≫
          Z.presheaf.germ W x hx).hom
    exact congrArg CommRingCat.Hom.hom
      ((Category.assoc _ _ _).trans
        (congrArg (fun f ↦ (Scheme.ΓSpecIso (.of k)).inv ≫ f) hcomp)).symm
  have : IsLocalization.AtPrime (Z.presheaf.stalk x) p :=
    hW.isLocalization_stalk' q hx
  obtain ⟨R, hR, aR, localR, noethR, regR, eftR, rs, hrs, ⟨e⟩⟩ := hpoints x
  refine ⟨R, hR, aR, localR, noethR, regR, eftR, rs, hrs, ?_⟩
  exact ⟨e.trans ((IsLocalization.algEquiv p.primeCompl
    (Z.presheaf.stalk x) (Localization.AtPrime p)).restrictScalars k)⟩

end AlgebraicGeometry
