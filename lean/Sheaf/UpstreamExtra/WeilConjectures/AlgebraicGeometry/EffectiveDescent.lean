module

public import WeilConjectures.AlgebraicGeometry.EffectiveDescent
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.FieldTheory.CommonExtensionFields
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.AffineLocal
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Gluing
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Group
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Neighbourhood
public import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineNeighbourhood
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-! Declarations of ours that lived in the upstream file `WeilConjectures.AlgebraicGeometry.EffectiveDescent` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!
# Effective descent for schemes

Let `p : X ⟶ Y` be a morphism of schemes. This file collects the descent statements for schemes
over `X` equipped with a descent datum relative to `p` (in the transport form
`CategoryTheory.Over.DescentDatum`) that are needed to descend the Jacobian of a curve from a
finite separable extension of the base field.

## Main statements

- `CategoryTheory.Over.DescentDatum.isEffective_of_isFinite`: along a surjective finite locally
  free morphism, descent data on schemes in which every finite set of points lies in an affine open
  (for instance projective schemes over a field) are effective (blueprint
  `thm-pd-effective-descent`).
- `CategoryTheory.Over.DescentDatum.isEffective_of_isClosedImmersion`: along a surjective finite
  locally free morphism with affine source `X`, descent data on projective schemes over `X` are
  effective (blueprint `thm-pd-effective-descent`).
- `CategoryTheory.Over.DescentDatum.existsUnique_hom_of_isPullback`: compatible morphisms descend
  (blueprint `lem-pd-morphisms-descend`).
- `CategoryTheory.Over.DescentDatum.existsUnique_grpObj_of_isPullback`: compatible group scheme
  structures descend, uniquely (blueprint `lem-pd-group-scheme-descent`).
- `CategoryTheory.Over.DescentDatum.exists_commGrpObj_of_isPullback`: compatible commutative group
  scheme structures descend (blueprint `lem-pd-group-scheme-descent`).
- `AlgebraicGeometry.locallyOfFiniteType_quasiCompact_smooth_isProper_connectedSpace_of_isPullback`:
  finite type, smoothness, properness and connectedness descend along a field extension (blueprint
  `thm-pd-fpqc-local-properties`).
- `AlgebraicGeometry.isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback`:
  properness, smoothness of relative dimension `n` and geometric integrality descend along a field
  extension (blueprint `thm-pd-fpqc-local-properties`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y}

end CategoryTheory.Over.DescentDatum

namespace AlgebraicGeometry

private theorem integral_of_flat_surjective {A B : Scheme.{u}} (f : A ⟶ B)
    [Flat f] [Surjective f] [IsIntegral A] : IsIntegral B := by
  have : IrreducibleSpace B := f.surjective.irreducibleSpace f.continuous
  have (b : B) : _root_.IsReduced (B.presheaf.stalk b) := by
    obtain ⟨a, rfl⟩ := f.surjective b
    let φ := (f.stalkMap a).hom
    let := φ.toAlgebra
    have : IsLocalHom (algebraMap (B.presheaf.stalk (f a)) (A.presheaf.stalk a)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap a).hom)
    have : Module.Flat (B.presheaf.stalk (f a)) (A.presheaf.stalk a) := Flat.stalkMap f a
    have : Module.FaithfullyFlat (B.presheaf.stalk (f a)) (A.presheaf.stalk a) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact isReduced_of_injective φ (FaithfulSMul.algebraMap_injective
      (B.presheaf.stalk (f a)) (A.presheaf.stalk a))
  have : IsReduced B := isReduced_of_isReduced_stalk B
  exact isIntegral_of_irreducibleSpace_of_isReduced B

private theorem geometricallyIntegral_of_field_pullback {k K : Type u}
    [Field k] [Field K] [Algebra k K] {Z Z' : Scheme.{u}} (z : Z ⟶ Spec (.of k))
    (z' : Z' ⟶ Spec (.of K)) (q : Z' ⟶ Z)
    (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [GeometricallyIntegral z'] : GeometricallyIntegral z := by
  rw [GeometricallyIntegral.eq_geometrically]
  rw [geometrically_iff_of_commRing]
  intro L _ _ A a b hs
  obtain ⟨M, hM, hMk, i, j, _, _⟩ := Field.exists_common_extension k K L
  let im := Spec.map (CommRingCat.ofHom i.toRingHom)
  let jm := Spec.map (CommRingCat.ofHom j.toRingHom)
  let pk := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let pl := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hij : im ≫ pk = jm ≫ pl := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (i.commutes x).trans (j.commutes x).symm
  let W := pullback z' im
  let w₁ : W ⟶ Z' := pullback.fst z' im
  let w₂ : W ⟶ Spec (.of M) := pullback.snd z' im
  have hw : IsPullback w₁ w₂ z' im := .of_hasPullback z' im
  have hi : IsIntegral W := GeometricallyIntegral.geometrically_isIntegral
    im w₁ w₂ hw
  have ht : IsPullback (w₁ ≫ q) w₂ z (jm ≫ pl) := by
    rw [← hij]
    exact hw.paste_horiz h
  let r : W ⟶ A := hs.lift (w₁ ≫ q) (w₂ ≫ jm) (by
    simpa only [Category.assoc] using ht.w)
  have hra : r ≫ a = w₁ ≫ q := by simp [r]
  have hrb : r ≫ b = w₂ ≫ jm := by simp [r]
  have hr : IsPullback r w₂ b jm := by
    apply IsPullback.of_right (h₁₂ := a) (v₁₃ := z) (h₂₂ := pl)
    · simpa only [hra] using ht
    · exact hrb
    · exact hs
  have : Flat jm := by
    dsimp [jm]
    infer_instance
  have : Surjective jm := by
    dsimp [jm]
    infer_instance
  have : Flat r := MorphismProperty.of_isPullback hr.flip inferInstance
  have : Surjective r := MorphismProperty.of_isPullback hr.flip inferInstance
  exact integral_of_flat_surjective r

end AlgebraicGeometry
