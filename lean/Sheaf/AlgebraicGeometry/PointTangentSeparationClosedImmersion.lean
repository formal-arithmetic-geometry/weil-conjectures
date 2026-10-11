/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeTangentSpace
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Sections separating points and tangent vectors give a closed immersion

Source: Stacks Project, varieties.tex, Tag 0E8S, Lemma 33.23.1; coherent.tex,
Tag 02O5, Proposition 30.19.1
(blueprint: lem-sc-point-tangent-separation-closed-immersion).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- A generating subspace separating closed points and tangent vectors is finite-dimensional.
Every basis defines a closed immersion whose pullback of `O(1)` is `L`; for the full
section space this is the complete linear system, and `L` is very ample.
The coordinate space for a basis of `V` identifies with `P(V^dual)`.

Source: Stacks Project, varieties.tex, Tag 0E8S, Lemma 33.23.1; coherent.tex,
Tag 02O5, Proposition 30.19.1
(blueprint: lem-sc-point-tangent-separation-closed-immersion).

Proof:
1. Proper coherent cohomology makes `H^0(X,L)` finite-dimensional, hence also `V`.
2. Condition (0) makes the basis generate `L`. The projective-space construction gives
   the coordinate morphism and the identification of its pullback of `O(1)` with `L`.
3. The coordinate morphism is proper because its composite to `Spec k` is proper and
   projective space is separated (Tag 01W6).
4. Point separation gives injectivity on closed points. A nonempty closed fibre has a
   closed point (Tag 005E). A nonclosed point has infinitely many closed specializations
   (Tag 0478), contradicting injectivity. Thus each closed fibre is empty or a singleton.
5. Projective space is locally Noetherian. Tag 02OH gives a finite neighbourhood of
   every closed target point. Their union is all the target: a nonempty closed complement
   would contain a closed point. Hence the coordinate morphism is finite.
6. Its structure-map cokernel is finite type with closed support, so surjectivity can be
   checked at closed target points. At an empty fibre the target stalk of the pushforward
   is zero. For a singleton fibre `{x}`, properness identifies that stalk with `O_X,x`;
   the stalk map is finite and both residue fields are `k` by the Nullstellensatz.
7. Tangent separation makes the differential injective; rational tangent/cotangent
   duality (Tag 0B2E) makes the map on maximal ideals modulo squares surjective.
8. The finite local cotangent criterion (Tag 0E8M) makes the stalk map surjective.
   On affine opens the finite morphism is therefore induced by a surjective ring map,
   giving a closed immersion.
9. For `V = top` the morphism is the complete linear system. Its closed-immersion and
   pullback properties imply `IsVeryAmple f L`.
-/
theorem point_tangent_separation_closed_immersion
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
    (L : X.Modules) [L.IsInvertible]
    (V : Submodule k ((ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj (L.val.obj (Opposite.op ⊤))))
    (hgen : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ s : V, x ∈ Scheme.Modules.nonvanishingLocus L s.val)
    (hpoint : ∀ x y : X, IsClosed ({x} : Set X) → IsClosed ({y} : Set X) → x ≠ y →
      ∃ s : V, x ∉ Scheme.Modules.nonvanishingLocus L s.val ∧
        y ∈ Scheme.Modules.nonvanishingLocus L s.val)
    (htangent : ∀ x : X, IsClosed ({x} : Set X) →
      ∀ θ : schemeTangentSpace k X f x, θ ≠ 0 →
        ∃ s : V, x ∉ Scheme.Modules.nonvanishingLocus L s.val ∧
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction θ.val)).unit.app
            L).val.app (Opposite.op ⊤) s.val ≠ 0) :
    FiniteDimensional k V ∧
    (∀ (I : Type u) [Finite I] (b : Module.Basis I k V),
      ∃ s : I → L.sections,
        (∀ i, (s i).val (Opposite.op ⊤) = (b i).val) ∧
        ∃ hs : Epi (L.freeHomEquiv.symm s),
          IsClosedImmersion (ProjectiveSpace.homOfGeneratingSections I f L s hs) ∧
          Nonempty (ProjectiveSpace.twistRestrict
            (ProjectiveSpace.homOfGeneratingSections I f L s hs) 1 ≅ L)) ∧
    (V = ⊤ → IsVeryAmple f L) := by
  sorry

end AlgebraicGeometry
