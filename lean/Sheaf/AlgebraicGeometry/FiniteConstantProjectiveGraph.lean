/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-! # Finite constants and projective graph embeddings

Source: Stacks Project, Morphisms, Tags 0C4Q, 0B3I, 087S, 01WE, 01WF and 01W8;
Constructions, Tags 01NF and 01O3
(blueprint: lem-sfb-finite-constant-projective-graph).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A projective scheme over a finite extension of constants has one projective embedding
whose graph over any separated target remains a closed embedding after every base change.
The two equations for `j` specify the graph under the projective-space pullback square;
the two equations for `j'` specify its induced base change. The final isomorphism realizes
the ambient space as the projective bundle of the ordered free module of rank `N + 1`.

Source: Stacks Project, Morphisms, Tags 0C4Q, 0B3I, 087S, 01WE, 01WF, 01W8 and 01WC;
Constructions, Tags 01NF and 01O3
(blueprint: lem-sfb-finite-constant-projective-graph).

Proof plan:
1. The constants map Spec F -> Spec k is finite: F is a finite k-module, and the
   restrictions to the whole affine base and the empty open are finite
   (def-weil-affine-spectrum, def-weil-finite-integral-morphism). The trivial invertible
   module on the one-point affine Spec k is ample, using its section 1 in tensor degree 1
   (def-weil-pbc-ample-invertible-module).
2. Apply lem-trf-finite-projective-bundle and
   lem-trf-projective-bundle-to-h-projective to this constants map. No separability is used.
3. Compose with the projective structure map of R using lem-trf-h-projective-composition.
   Unpack def-kun-projective to choose N and i, replacing a finite coordinate type by
   the ordered N+1 coordinates. Empty coordinates imply empty R, which embeds in P^0.
4. The graph R -> R times_k S is closed, by
   lem-weil-pbc-fibre-product-change-of-base-closed-immersion applied to c, id_S and
   the separated structure map of S; identify R times_S S with R by its projections
   (def-pc-fibre-product, def-weil-closed-immersion).
5. Base change i to S and compose with that graph
   (lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-closed-immersion-comp).
   The projective-space cartesian square
   (lemma-nagata-projective-space-base-change-pullback) identifies the ambient product
   with projective space over S. Its projections give precisely the equations for j.
6. For any t : S' -> S, base change this closed immersion. The same cartesian-square
   theorem identifies the ambient space with projective N-space over S'. Fibre-product
   projections identify the source with R times_S S' and give the equations for j'.
   The closed immersion is preserved under arbitrary base change, so the projection is
   H-projective (def-kun-projective); no condition on t is required.
7. Use lem-trf-free-projective-bundle-base-change-space for the ambient isomorphism theta.
   Compose j' with theta inverse. Its structure map is the second pullback projection.
   The free module of rank N+1 is quasi-coherent and finite type (pqf-def-coherent),
   giving def-trf-projective-bundle-morphism and properness by lem-trf-projective-bundle-proper.
   All steps permit empty R and S', and require no quasi-projectivity or ample sheaf on S. -/
theorem exists_finiteConstant_projectiveGraph
    (k F : Type u) [Field k] [Field F] [Algebra k F] [Module.Finite k F]
    (R S : Scheme.{u}) [R.Over (Spec (.of F))] [S.Over (Spec (.of k))]
    [IsHProjective (R ↘ Spec (.of F))] [IsSeparated (S ↘ Spec (.of k))]
    (c : R ⟶ S)
    (hc : c ≫ S ↘ Spec (.of k) =
      (R ↘ Spec (.of F)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k F))) :
    ∃ (N : ℕ) (i : R ⟶ ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of k))),
      IsClosedImmersion i ∧
      i ≫ ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of k)) ↘ Spec (.of k) =
        (R ↘ Spec (.of F)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k F)) ∧
      ∃ j : R ⟶ ProjectiveSpace (ULift.{u} (Fin (N + 1))) S,
        IsClosedImmersion j ∧
        j ≫ ProjectiveSpace (ULift.{u} (Fin (N + 1))) S ↘ S = c ∧
        j ≫ ProjectiveSpace.map (ULift.{u} (Fin (N + 1))) (S ↘ Spec (.of k)) = i ∧
        ∀ (S' : Scheme.{u}) (t : S' ⟶ S),
          ∃ j' : pullback c t ⟶ ProjectiveSpace (ULift.{u} (Fin (N + 1))) S',
            IsClosedImmersion j' ∧
            j' ≫ ProjectiveSpace (ULift.{u} (Fin (N + 1))) S' ↘ S' = pullback.snd c t ∧
            j' ≫ ProjectiveSpace.map (ULift.{u} (Fin (N + 1))) t = pullback.fst c t ≫ j ∧
            IsProper (pullback.snd c t) ∧ IsHProjective (pullback.snd c t) ∧
            IsProjectiveBundle (pullback.snd c t) ∧
            ∃ θ : RelativeProjectiveSpace.scheme S' N ≅
                ProjectiveSpace (ULift.{u} (Fin (N + 1))) S',
              θ.hom ≫ ProjectiveSpace (ULift.{u} (Fin (N + 1))) S' ↘ S' =
                RelativeProjectiveSpace.π S' N ∧
              IsClosedImmersion (j' ≫ θ.inv) ∧
              (j' ≫ θ.inv) ≫ RelativeProjectiveSpace.π S' N = pullback.snd c t := by
  sorry

end AlgebraicGeometry
