module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Translation by a point of a field groupoid

Source: Stacks Project, Tag 04LS, Lemma `lemma-groupoid-on-field-move-point`
(blueprint: lem-sfb-field-groupoid-point-translation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A point whose two residue maps are invertible gives a translation automorphism.
Source: Stacks Project, Tag 04LS, statement and explicit morphisms in its proof
(blueprint: lem-sfb-field-groupoid-point-translation).

Proof plan:
1. Let `j` be the canonical residue-field point of `r`. Compose `j` with the spectra
   of the inverses of the two residue maps to obtain `u` and `v`. The residue-point
   naturality and field-point parametrization give their images, `u ≫ s = 𝟙 _`,
   `v ≫ t = 𝟙 _`, and an automorphism `θ` with `u ≫ t = θ.hom` and `v = θ.inv ≫ u`.
   These are the inputs lem-weil-pbc-morphism-from-spec-field and
   lem-weil-pbc-residue-field-point-naturality, together with Spec functoriality.
2. Use the fibre-product universal property to define the forward map by the pair
   `(t ≫ u, 𝟙 R)` and the backward map by `(t ≫ v ≫ i, 𝟙 R)`, followed by `c`.
   The source section and the inverse-source and target-section identities make
   these pairs composable. Precomposition gives both displayed test-point formulas.
3. Set `q = t ≫ v`. The target law and `v = θ.inv ≫ u` show that the forward map
   after the backward map is `c(q, c(iq, id))`. Associativity, the inverse law,
   and the left unit law reduce this to the identity.
4. Set `p = t ≫ u`. The other composite is `c(ip, c(p, id))`, which reduces to
   the identity using associativity, the other inverse law, and the left unit law.
   All compositions are composable by the source and target laws of the groupoid.
5. The target identity and right unit law give `e ≫ L.hom = u`. Thus the identity
   point maps to `r`. No step uses a finite-type hypothesis.

The two existential compatibility proofs merely type the fibre-product lifts;
they impose no additional hypothesis on the groupoid or the test morphisms. -/
theorem exists_fieldGroupoid_pointTranslation (k : Type u) [Field k] {R : Scheme.{u}}
    (s t : R ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ R)
    (i : R ⟶ R) (c : pullback s t ⟶ R) (hG : IsGroupoidScheme s t e i c)
    (r : R) (hs : IsIso (s.residueFieldMap r)) (ht : IsIso (t.residueFieldMap r)) :
    ∃ (u v : Spec (CommRingCat.of k) ⟶ R)
      (θ : Spec (CommRingCat.of k) ≅ Spec (CommRingCat.of k)) (L : R ≅ R),
      (∀ z : Spec (CommRingCat.of k), u z = r) ∧
      (∀ z : Spec (CommRingCat.of k), v z = r) ∧
      u ≫ s = 𝟙 (Spec (CommRingCat.of k)) ∧
      v ≫ t = 𝟙 (Spec (CommRingCat.of k)) ∧
      u ≫ t = θ.hom ∧ v = θ.inv ≫ u ∧
      (∀ (T : Scheme.{u}) (x : T ⟶ R),
        ∃ h : (x ≫ t ≫ u) ≫ s = x ≫ t,
          x ≫ L.hom = pullback.lift (x ≫ t ≫ u) x h ≫ c) ∧
      (∀ (T : Scheme.{u}) (y : T ⟶ R),
        ∃ h : (y ≫ t ≫ v ≫ i) ≫ s = y ≫ t,
          y ≫ L.inv = pullback.lift (y ≫ t ≫ v ≫ i) y h ≫ c) ∧
      e ≫ L.hom = u := by
  sorry

end AlgebraicGeometry
