/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Mayer--Vietoris gluing of the canonical flat base-change comparison

Source: Stacks Project, Cohomology of Schemes, Lemma 30.5.2 (Tag 02KH),
the Mayer--Vietoris alternative in the quasi-separated paragraph
(blueprint: lem-pc-flat-cohomology-gluing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Flat base-change comparisons glue along a two-open cover when the comparisons
on the two opens and their intersection are bijective in every degree.

Source: Stacks Project, Lemma 30.5.2 (Tag 02KH), Mayer--Vietoris alternative.
(blueprint: lem-pc-flat-cohomology-gluing)

Proof: The inverse images of U and V cover X_S; inverse image preserves their
intersection. Form the Mayer--Vietoris sequences for M on X and its pullback on
X_S. Tensor the former sequence with S; flatness preserves exactness, and tensor
commutes with the binary direct sums. The canonical comparisons H.baseChange give
a map between the two exact sequences. Compatibility with restrictions follows
from functoriality of pullback and its adjunction unit. Compatibility with the
connecting maps follows by applying the exact inverse-image functor to the Ext
classes defining the boundaries, or by a common injective Cech resolution.
The canonical iterated-pullback isomorphisms identify the three outside comparisons
with those in the hypotheses. In positive degree apply the five lemma to the
five terms ending and starting at the adjacent intersection cohomology groups.
In degree zero use the initial left-exact segment starting with zero. Thus the
comparison on X is bijective in all degrees.

No affineness of U intersect V is asserted. In the eventual qcqs induction that
intersection is only compact and separated, and is handled by the separated-case
lemma. The gluing lemma itself needs neither compactness nor separatedness. -/
theorem H.baseChange_bijective_of_openCover
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (hU : ∀ q : ℕ, Function.Bijective
      (H.baseChange (S := S) (U.ι ≫ f) ((pullback U.ι).obj M) q))
    (hV : ∀ q : ℕ, Function.Bijective
      (H.baseChange (S := S) (V.ι ≫ f) ((pullback V.ι).obj M) q))
    (hUV : ∀ q : ℕ, Function.Bijective
      (H.baseChange (S := S) ((U ⊓ V).ι ≫ f) ((pullback (U ⊓ V).ι).obj M) q))
    (q : ℕ) : Function.Bijective (H.baseChange (S := S) f M q) := by sorry

end AlgebraicGeometry.Scheme.Modules
