/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.AlgebraicGeometry.EtaleComparison
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability

/-!
# Clopen partitions refining coverings of w-contractible affine schemes

Source: blueprint, sec-proetale-coefficients, sk-thm-pe-weakly-contractible-basis,
node det-pe-wcb-clopen-partition; Stacks Project, Tag 098F, implication (1) to (2)
(blueprint: det-pe-wcb-clopen-partition).
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A covering of a w-contractible affine object of the small pro-étale site admits a
finite partition into clopen open subschemes, each mapping over the affine target to a
selected covering member. The partition has no pieces when the target is empty.

Source: blueprint node det-pe-wcb-clopen-partition; Stacks Project, Tag 098F,
implication (1) to (2) (blueprint: det-pe-wcb-clopen-partition).

Proof:
1. For the empty target take the empty partition. Otherwise sk-def-pe-site and
   def-weil-pbc-proetale-covering give finitely many affine opens in covering members
   whose images cover the affine target. The base change along the identity of the
   target identifies these with affine opens in the original members. All covering
   arrows are weakly étale; the original index set need not be finite.
2. Form their disjoint union, using lem-weil-pbc-scheme-coproduct-family. Its components
   are clopen and disjoint. It is affine by lem-weil-pbc-affine-morphism-permanence,
   clause (4), and its map to the target is surjective since the component images cover.
3. The inclusions of the affine opens are étale by lem-weil-pbc-open-immersion-etale,
   hence weakly étale by det-pe-morphisms-etale-comparison, clause (1). Composition and
   Zariski source locality from sk-lem-pe-weakly-etale-stability make the disjoint-union
   map weakly étale. Clause (4) of det-pe-morphisms-etale-comparison gives flatness of
   its ring map and multiplication. Surjectivity and
   lem-weil-pbc-flat-surjective-spectrum-faithfully-flat give faithful flatness.
4. Apply det-pe-wcb-split-cover to obtain a section of this faithfully flat weakly
   étale affine map, using w-contractibility of the target ring.
5. Pull the clopen components back along this section. Their inverse images are clopen,
   disjoint and cover the target. Restrict the section to each inverse image and then
   compose with the inclusion into its chosen covering member. The section equation
   says that the resulting map is over the target. Discard empty pieces and reindex
   the remaining finite family by `Fin m`.
-/
theorem proetale_wContractible_clopen_partition
    (X : Scheme.{u}) (D : Type u) [CommRing D] [IsWContractibleRing D]
    (f : Spec (.of D) ⟶ X) [WeaklyEtale f]
    (I : Type v) (V : I → X.ProEt) (a : ∀ i : I, V i ⟶ ProEt.mk f)
    (hcover : Presieve.ofArrows V a ∈ ProEt.precoverage X (ProEt.mk f)) :
    ∃ (m : ℕ) (W : Fin m → (Spec (.of D)).Opens),
      (∀ k : Fin m, IsClosed (W k : Set (Spec (.of D)))) ∧
      (∀ k : Fin m, (W k : Set (Spec (.of D))).Nonempty) ∧
      Pairwise (fun j k : Fin m ↦ Disjoint (W j) (W k)) ∧
      iSup W = ⊤ ∧
      ∃ (i : Fin m → I) (g : ∀ k : Fin m, (W k).toScheme ⟶ (V (i k)).left),
        ∀ k : Fin m, g k ≫ (a (i k)).left = (W k).ι := by
  sorry

end AlgebraicGeometry.Scheme
