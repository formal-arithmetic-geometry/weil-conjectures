module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.Flat.Basic

/-! # Local structure of quasi-compact flat monomorphisms

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, VIII 2.1.12, 2.1.14 and 2.2.12,
printed pp. 88--91; Stacks Project, Tags 04VU, 00HR, 03DP and 00HD
(blueprint: lem-per-flat-monomorphism-local-structure).

The isomorphisms are asserted for the actual stalk maps and fibre structure maps.
Geometric regularity is expressed by the stated stronger description of each field-extended
fibre as either empty or canonically the spectrum of the extension field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A quasi-compact flat morphism with invertible diagonal is injective, identifies local
rings, has empty or canonical residue-field fibres, is regular, and preserves Noetherianity
and reducedness. All conclusions hold after arbitrary base change.

Source: ILO, Travaux de Gabber, VIII 2.1.12, 2.1.14 and 2.2.12, printed pp. 88--91;
Stacks Project, Tags 04VU, 00HR, 03DP and 00HD
(blueprint: lem-per-flat-monomorphism-local-structure).

Proof plan (the eight steps of the DAG node):
1. An invertible diagonal gives cancellation, hence monicity. The pullback universal
   property gives monicity after base change. Flatness and quasi-compactness are preserved
   by base change (lem-weil-pbc-flat-morphism-base-change,
   lem-pc-quasi-compact-base-change).
2. A monomorphism into the spectrum of a field is empty or its structure map is invertible
   (lem-sfb-monomorphism-into-field-coproduct, singleton case). The fibre homeomorphism
   identifies its points with the inverse image of the base point, proving injectivity and
   the nonemptiness criterion. Base change of this structure-map isomorphism identifies
   every nonempty field-extended fibre with the spectrum of that field, which is regular.
3. Choose affine neighbourhoods V = Spec B and U = Spec A with V mapping into U, using
   lem-weil-pbc-affine-opens-basis and lem-weil-pbc-morphism-factors-through-open-subscheme.
   Cancellation and lem-weil-pbc-open-immersion-monomorphism make V to U monic. Thus A to B
   is epic by def-weil-affine-spectrum and flat by lem-weil-pbc-flat-morphism-affine-criterion.
4. The local ring maps are the localized ring maps, by
   lem-weil-pbc-affine-open-stalk-localization and lem-weil-pbc-spec-map-stalk-localization.
   They remain epic: maps agreeing on localized A agree on B and hence on its fractions.
   Flat local maps are faithfully flat (lem-pc-local-flat-faithful-flat-reflects-surjective).
   Apply lem-sfb-faithfully-flat-ring-epimorphism-isomorphism to the actual stalk maps.
5. The two inclusions B to B tensor_A B agree because A to B is epic. Hence b tensor c
   equals 1 tensor bc. For any ideal J of B this identifies B tensor_A (B/J) with B/J,
   with inverse c-bar mapping to 1 tensor c-bar. Use the tensor pushout and module tensor
   universal properties (lem-weil-pbc-algebra-tensor-pushout-universal-property,
   def-weil-pbc-module-tensor-product).
6. Put I equal to the contraction of J. Tensor the sequence I to A to B/J with flat B
   (lem-weil-pbc-flat-tensor-exact). Under step 5 and B tensor_A A = B, its kernel is J
   and its image is IB. Therefore every ideal J is the extension of its contraction.
7. A finite Noetherian affine cover of the base has quasi-compact inverse images, each
   finitely covered by affine V = Spec B. Step 6 extends finite generators of contracted
   ideals to generators in B, so every B is Noetherian. These finitely many affines cover
   the source, exactly the finite-affine-cover definition of Noetherianity.
8. If the base is reduced, its stalks are reduced (def-pc-reduced-scheme); step 4 transfers
   reducedness to the source stalks. The argument applied to every pullback proves all
   base-change clauses, and identity base change gives the original morphism's clauses.
-/
theorem flat_monomorphism_local_structure
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [Flat f]
    (_hdiag : IsIso (pullback.diagonal f)) :
    Function.Injective f ∧
    (∀ y : Y, IsIso (f.stalkMap y)) ∧
    (∀ x : X,
      (IsEmpty (f.fiber x) ∨ IsIso (f.fiberToSpecResidueField x)) ∧
      (Nonempty (f.fiber x) ↔ x ∈ Set.range f)) ∧
    (∀ (x : X) (K : Type u) [Field K] (ι : X.residueField x →+* K),
      IsEmpty (pullback (f.fiberToSpecResidueField x)
        (Spec.map (CommRingCat.ofHom ι)) : Scheme.{u}) ∨
      IsIso (pullback.snd (f.fiberToSpecResidueField x) (Spec.map (CommRingCat.ofHom ι)))) ∧
    (IsNoetherian X → IsNoetherian Y) ∧
    (IsReduced X → IsReduced Y) ∧
    (∀ (T : Scheme.{u}) (g : T ⟶ X),
      Flat (pullback.snd f g) ∧
      Function.Injective (pullback.snd f g) ∧
      (∀ z : (pullback f g : Scheme.{u}), IsIso ((pullback.snd f g).stalkMap z)) ∧
      (∀ t : T,
        (IsEmpty ((pullback.snd f g).fiber t) ∨
          IsIso ((pullback.snd f g).fiberToSpecResidueField t)) ∧
        (Nonempty ((pullback.snd f g).fiber t) ↔ t ∈ Set.range (pullback.snd f g))) ∧
      (∀ (t : T) (K : Type u) [Field K] (ι : T.residueField t →+* K),
        IsEmpty (pullback ((pullback.snd f g).fiberToSpecResidueField t)
          (Spec.map (CommRingCat.ofHom ι)) : Scheme.{u}) ∨
        IsIso (pullback.snd ((pullback.snd f g).fiberToSpecResidueField t)
          (Spec.map (CommRingCat.ofHom ι)))) ∧
      (IsNoetherian T → IsNoetherian (pullback f g)) ∧
      (IsReduced T → IsReduced (pullback f g))) := by
  sorry

end AlgebraicGeometry
