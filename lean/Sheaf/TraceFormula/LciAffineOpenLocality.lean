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
  sorry

end AlgebraicGeometry
