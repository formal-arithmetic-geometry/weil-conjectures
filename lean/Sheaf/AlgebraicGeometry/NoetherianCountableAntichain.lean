module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.Set.Countable
import Mathlib.AlgebraicGeometry.Properties

/-!
# Countable specialization antichains in Noetherian schemes

Source: Stacks Project, Properties, Tags 0G2F and 0G2R
(blueprint: lem-sfb-noetherian-countable-antichain).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every subset of a Noetherian scheme contains an at most countable subset with
its closure and with no specialization between distinct elements.

Source: Stacks Project, Properties, Tags 0G2F (lemma-countable-dense-subset) and
0G2R (lemma-maximal-points) (blueprint: lem-sfb-noetherian-countable-antichain).

Proof plan:
1. Put `Z_x = closure {x}`. Let `Q` consist of points `x` admitting a countable
   `C_x ⊆ E ∩ Z_x` with closure `Z_x`, and choose one witness for each `x ∈ Q`.
   Singletons give `E ⊆ Q`, and the witnesses give `Q ⊆ closure E`.
2. For countable `A ⊆ Q`, the union `C` of the witnesses `C_x`, for `x ∈ A`, is
   countable, is contained in `E`, and has the same closure as `A`: each `x ∈ A`
   lies in `closure C_x`, and each `C_x` lies in `Z_x ⊆ closure A`.
3. By `lem-sc-noetherian-closed-subset-finite-components`, decompose `closure A`
   into finitely many irreducible components `Z_i`. They are closed in `U`, so
   `lem-weil-pbc-scheme-sober` supplies generic points. The complement in
   `closure A` of all the other components is a nonempty open subset contained
   in `Z_i`. Irreducibility makes it meet every nonempty open of `Z_i`; density
   of `C` in `closure A` then shows `C ∩ Z_i` is dense in `Z_i`. Thus the generic
   point of each `Z_i` belongs to `Q`. Components use
   `def-weil-irreducible-components`.
4. Let `M` be the points of `Q` having no proper generalization in `Q`.
   By `lem-sfb-subset-maximal-generalization`, every point of `Q` specializes
   from one in `M`. If `M` were infinite, choose a countably infinite `A ⊆ M`.
   Steps 2 and 3 put all generic points of the finitely many components of
   `closure A` in `Q`. Every point of `A` lies in a component, hence specializes
   from its generic point, and maximality forces equality. This would make
   `A` finite, a contradiction. Thus `M` is finite.
5. The union of `C_m` for `m ∈ M` is countable, lies in `E`, and its closure
   contains every `Z_m`, hence contains `Q` and `E`. Call this union `C`; then
   `closure C = closure E`.
6. Take `D` to be the points of `C` having no proper generalization in `C`.
   It is countable and contained in `E`. By
   `lem-sfb-subset-maximal-generalization`, every point of `C` specializes from
   a point of `D`, so `closure D = closure C`. If `v,w ∈ D` and `w ∈ closure {v}`,
   maximality of `w` gives `v = w`. Empty unions and finite sets are allowed
   throughout, including when `E` is empty.
-/
theorem exists_countable_subset_closure_eq_no_specializations
    (U : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian U]
    [CompactSpace U] (E : Set U) :
    ∃ D : Set U, D ⊆ E ∧ D.Countable ∧ closure D = closure E ∧
      ∀ (v : U), v ∈ D → ∀ (w : U), w ∈ D → w ∈ closure ({v} : Set U) → v = w := by
  sorry

end AlgebraicGeometry.Scheme
