/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Sheaf.TraceFormula.LocalDimensionFormula
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.TraceFormula.ReducedSchemeImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField

/-!
# The normalized graph of an invariant pencil

Source: de Jong, Families of curves and alterations (1997), Lemma 5.2 proof,
printed p. 613; Stacks Project, Tags 01R8, 0CNG, 01WD and 0BXR.
(blueprint: lem-sfb-invariant-pencil-graph-model)

The two helpers name the scalar inclusion and the generic map [1:t_1:...:t_r].
The theorem retains the canonical scheme image, normalization and generic-stalk pullbacks.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The scalar inclusion into the function field, obtained from the structure morphism
and the germ of global sections. Source: Stacks Project, Definition 01RW; de Jong (1997),
Lemma 5.2 proof, p. 613. (blueprint: lem-sfb-invariant-pencil-graph-model) -/
def invariantPencilFieldConstants {k : Type u} [Field k] {N : Scheme.{u}}
    [IsIntegral N] (f : N ⟶ Spec (.of k)) : k →+* N.functionField :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (N.fromSpecFunctionField ≫ f).appTop ≫
    (Scheme.ΓSpecIso N.functionField).hom).hom

/-- The generic map [1:t_1:...:t_r], constructed in the zeroth standard chart of the
canonical projective space. The nonzero homogeneous indices are the successors in `Fin`;
`Fin.cases 0 t` assigns them exactly the given rational functions.
Source: de Jong (1997), Lemma 5.2 proof, p. 613; Stacks Project, Tag 01NG.
(blueprint: lem-sfb-invariant-pencil-graph-model) -/
def invariantPencilGenericMap {k : Type u} [Field k] {N : Scheme.{u}}
    [IsIntegral N] (f : N ⟶ Spec (.of k)) {r : ℕ} (t : Fin r → N.functionField) :
    Spec N.functionField ⟶ ℙ(ULift.{u} (Fin (r + 1)); Spec (.of k)) :=
  AffineSpace.homOfVector (N.fromSpecFunctionField ≫ f)
      (fun j : {j : ULift.{u} (Fin (r + 1)) // j ≠ ⟨0⟩} ↦
        (Scheme.ΓSpecIso N.functionField).inv (Fin.cases 0 t j.1.down)) ≫
    (ProjectiveSpace.standardOpenIso (ULift.{u} (Fin (r + 1))) (Spec (.of k)) ⟨0⟩).inv ≫
    (ProjectiveSpace.standardOpen (ULift.{u} (Fin (r + 1))) (Spec (.of k)) ⟨0⟩).ι

/-- Invariant algebraically independent rational functions have an equivariant normalized
projective graph. `rho` is the left field action; the inverse before `Spec.map` makes
its induced scheme action a left action. No action is required to be faithful.
The map `etaV` specifies the rational map by its actual value on `Spec k(N)`.
The maps `p`, `a`, `b` are constrained to be the actual image/normalization projections.
The isomorphisms `eZ` and `eX` are the actual generic-stalk pullbacks. The map `beta`
is the pullback by `b`, transported through `eX`; its generic-point equation specifies
polynomial evaluation at the original tuple, and its range is exactly k(t_1,...,t_r).

Source: de Jong (1997), Lemma 5.2 proof, printed p. 613; Stacks Project,
Tags 01RV, 01R8, 056B, 0CNG, 01WD, 0BXR and 01RW.
(blueprint: lem-sfb-invariant-pencil-graph-model)

Proof:
1. Represent the finitely many germs t_i on a neighbourhood of the generic point and
intersect all its H-translates. This is an invariant dense open V. The affine chart
construction gives v, and equality of invariant germs gives equivariance by
lem-sc-integral-scheme-stalks-in-function-field,
lem-weil-pbc-morphism-into-affine-scheme and
lem-weil-pbc-projective-space-standard-charts.
2. N is Noetherian by lem-weil-pbc-finite-type-over-noetherian, and V is quasi-compact
by lem-weil-pbc-noetherian-open-subscheme-noetherian. The graph is an immersion since
projective space is separated (lem-weil-pbc-projective-space-proj-separated and
lem-weil-pbc-closed-immersion-base-change). Its morphism j is quasi-compact.
3. By lem-trf-reduced-scheme-image the schematic image Z is the reduced irreducible
closure of the graph, hence integral. By lemma-nagata-scheme-image-partial-section its
projection p is an isomorphism over V. The graph is p inverse V and is dense in Z,
so p identifies the generic stalks, namely the function fields (def-sc-function-field).
4. Every diagonal automorphism preserves the kernel ideal of j. The affine kernel
characterization of lem-weil-pbc-scheme-image-qc-kernel restricts these automorphisms
to Z. A closed immersion is a monomorphism, so the restrictions obey the group laws.
5. Embed N in finite projective space. Base change its embedding, apply lem-chow-segre
and lem-weil-pbc-closed-immersion-comp to embed Z in finite projective space. Thus Z
is proper and finite type by lem-kun-projective-implies-proper and def-weil-proper-morphism.
6. Apply lem-sfb-equivariant-normal-projective-model to p and V. Normalization is finite,
surjective and birational and lifts the action. It is normal, projective, geometrically
integral and finite type; a has the asserted properties and is an isomorphism over V.
7. Apply lem-sfb-projective-fibre-product-closed-model with one factor to obtain
H-projectivity and properness of b. On the zeroth chart its generic coordinate map is
polynomial evaluation at t. Algebraic independence makes this map injective, so b
sends the generic point to the generic point and is dominant, by
lem-weil-pbc-spec-field-point-residue-field. By lem-sc-integral-function-field-affine-fraction
its function-field map is precisely the inclusion k(t_1,...,t_r) into E, identified
using def-sfb-dominant-function-field-map. For r = 0 the chart ring and this subfield are k.
-/
theorem exists_invariant_pencil_graph_model
    (k : Type u) [Field k] (N : Scheme.{u}) [IsIntegral N]
    (f : N ⟶ Spec (.of k)) [IsHProjective f] [GeometricallyIntegral f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hN : ∀ x : N, IsDomain (N.presheaf.stalk x) ∧
      IsIntegrallyClosed (N.presheaf.stalk x))
    (H : Type v) [Group H] [Finite H] (rho : H →* (k ≃+* k)) (act : H →* Aut N)
    (hact : ∀ h : H, (act h).hom ≫ f =
      f ≫ Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom))
    (r : ℕ) (t : Fin r → N.functionField)
    (ht : @AlgebraicIndependent (Fin r) k N.functionField t _ _
      (invariantPencilFieldConstants f).toAlgebra)
    (hfixed : ∀ (h : H) (i : Fin r),
      @algebraMap N.functionField N.functionField _ _
        ((act h).hom.dominantFunctionFieldAlgebra) (t i) = t i) :
    ∃ (actP : H →* Aut ℙ(ULift.{u} (Fin (r + 1)); Spec (.of k))),
      (∀ h : H, (actP h).hom = ProjectiveSpace.map (ULift.{u} (Fin (r + 1)))
        (Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom))) ∧
    ∃ (V : N.Opens), Dense (V : Set N) ∧
      (∀ h : H, (act h).hom ⁻¹ᵁ V = V) ∧
    ∃ (actV : H →* Aut V.toScheme)
      (v : V.toScheme ⟶ ℙ(ULift.{u} (Fin (r + 1)); Spec (.of k)))
      (etaV : Spec N.functionField ⟶ V.toScheme),
      (∀ h : H, (actV h).hom ≫ V.ι = V.ι ≫ (act h).hom) ∧
      (∀ h : H, (actV h).hom ≫ v = v ≫ (actP h).hom) ∧
      v ≫ ℙ(ULift.{u} (Fin (r + 1)); Spec (.of k)) ↘ Spec (.of k) = V.ι ≫ f ∧
      etaV ≫ V.ι = N.fromSpecFunctionField ∧
      etaV ≫ v = invariantPencilGenericMap f t ∧
      v ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin (r + 1)))
        (Spec (.of k)) ⟨0⟩ = ⊤ ∧
    ∃ (j : V.toScheme ⟶
        pullback f (ℙ(ULift.{u} (Fin (r + 1)); Spec (.of k)) ↘ Spec (.of k))),
      j ≫ pullback.fst _ _ = V.ι ∧ j ≫ pullback.snd _ _ = v ∧
    ∃ (_ : IsIntegral j.image) (p : j.image ⟶ N),
      p = j.imageι ≫ pullback.fst _ _ ∧ IsIso (p ∣_ V) ∧
    ∃ (hp : p (genericPoint j.image) = genericPoint N)
      (eZ : N.functionField ≅ j.image.functionField),
      eZ.hom = p.functionFieldMap hp ∧
    ∃ (actZ : H →* Aut j.image) (actX : H →* Aut j.image.normalization)
      (a : j.image.normalization ⟶ N)
      (b : j.image.normalization ⟶ ℙ(ULift.{u} (Fin (r + 1)); Spec (.of k))),
      a = j.image.fromNormalization ≫ p ∧
      b = j.image.fromNormalization ≫ j.imageι ≫ pullback.snd _ _ ∧
      (∀ x : j.image.normalization, IsDomain (j.image.normalization.presheaf.stalk x) ∧
        IsIntegrallyClosed (j.image.normalization.presheaf.stalk x)) ∧
      IsHProjective (a ≫ f) ∧ GeometricallyIntegral (a ≫ f) ∧
      LocallyOfFiniteType (a ≫ f) ∧ QuasiCompact (a ≫ f) ∧
      (∀ h : H, (actZ h).hom ≫ p = p ≫ (act h).hom) ∧
      (∀ h : H, (actZ h).hom ≫ j.imageι ≫ pullback.snd _ _ =
        j.imageι ≫ pullback.snd _ _ ≫ (actP h).hom) ∧
      (∀ h : H, (actX h).hom ≫ j.image.fromNormalization =
        j.image.fromNormalization ≫ (actZ h).hom) ∧
      (∀ h : H, (actX h).hom ≫ (a ≫ f) =
        (a ≫ f) ≫ Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom)) ∧
      (∀ h : H, (actX h).hom ≫ a = a ≫ (act h).hom) ∧
      (∀ h : H, (actX h).hom ≫ b = b ≫ (actP h).hom) ∧
      IsHProjective a ∧ IsHProjective b ∧ IsProper a ∧ Surjective a ∧ IsIso (a ∣_ V) ∧
      IsDominant b ∧ IsProper b ∧
    ∃ (_ : IsIntegral j.image.normalization)
      (_ : IsIntegral ℙ(ULift.{u} (Fin (r + 1)); Spec (.of k)))
      (ha : a (genericPoint j.image.normalization) = genericPoint N)
      (hb : b (genericPoint j.image.normalization) =
        genericPoint ℙ(ULift.{u} (Fin (r + 1)); Spec (.of k)))
      (eX : N.functionField ≅ j.image.normalization.functionField)
      (beta : ℙ(ULift.{u} (Fin (r + 1)); Spec (.of k)).functionField →+* N.functionField),
      eX.hom = a.functionFieldMap ha ∧
      CommRingCat.ofHom beta = b.functionFieldMap hb ≫ eX.inv ∧
      Spec.map (CommRingCat.ofHom beta) ≫
          ℙ(ULift.{u} (Fin (r + 1)); Spec (.of k)).fromSpecFunctionField =
        invariantPencilGenericMap f t ∧
      Set.range beta =
        ((@IntermediateField.adjoin k _ N.functionField _
          (invariantPencilFieldConstants f).toAlgebra (Set.range t)) : Set N.functionField) := by
  sorry

end AlgebraicGeometry
