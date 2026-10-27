module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.Connected.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-! # Connected components of finite-type schemes over fields

Source: Stacks Project, More on Morphisms, Tag 057K,
`lemma-local-local-structure-finite-type`, the Noetherian/open-component paragraph,
without the smoothness assumption (blueprint: lem-trf-finite-type-component-open-qc).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The connected component of a point of a finite-type scheme over a field is an open,
quasi-compact subscheme, connected (in particular nonempty), and of finite type over the field.
Source: Stacks Project, Tag 057K, `lemma-local-local-structure-finite-type`, paragraph
beginning "Let T be the connected component"; Tags 01T6, 01OZ, 04MF, 04ME, 04ZA,
01T5 and 01T3 (blueprint: lem-trf-finite-type-component-open-qc).

Proof:
1. The field is Noetherian: any ideal containing a nonzero element contains its inverse
   times that element, hence contains 1. Thus Spec k is locally Noetherian and quasi-compact.
   Apply `lem-weil-pbc-finite-type-over-noetherian` to make C Noetherian, then
   `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` to obtain ACC on opens.
2. `lem-sfb-noetherian-connected-components-open` makes the component open, and
   `lem-sfb-noetherian-space-compact-subsets` makes its underlying subset quasi-compact.
3. Give the component its open subscheme structure. Its topology is the subspace topology;
   the component is connected and contains c, hence is nonempty, as required by
   `def-weil-connected-scheme`.
4. For each affine open V of C, the inverse image under the inclusion j is the intersection
   of the component with V. By `lem-sfb-noetherian-space-compact-subsets` this subset is
   quasi-compact. The subspace topologies agree, so j is quasi-compact by the affine-preimage
   criterion of `def-weil-finite-type-morphism`.
5. By `lem-weil-pbc-qc-open-immersion-finite-type`, j is of finite type. Compose it with
   the given finite-type structure map using `lem-sfb-finite-type-composition-base-change`
   (clause 1) to obtain finite type of the component over k. -/
theorem finiteType_connectedComponent_open_quasiCompact
    {k : Type u} [Field k] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))] [QuasiCompact (C ↘ Spec (.of k))] (c : C) :
    ∃ U : C.Opens, (U : Set C) = connectedComponent c ∧ IsCompact (U : Set C) ∧
      ConnectedSpace U.toScheme ∧
      LocallyOfFiniteType (U.ι ≫ (C ↘ Spec (.of k))) ∧
      QuasiCompact (U.ι ≫ (C ↘ Spec (.of k))) := by
  have : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (.of k))
  have : CompactSpace C :=
    QuasiCompact.compactSpace_of_compactSpace (C ↘ Spec (.of k))
  have : IsNoetherian C := ⟨⟩
  let U : C.Opens :=
    ⟨connectedComponent c, TopologicalSpace.NoetherianSpace.isOpen_connectedComponent c⟩
  refine ⟨U, rfl, TopologicalSpace.NoetherianSpace.isCompact _, ?_,
    inferInstance, inferInstance⟩
  exact isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := c))

end AlgebraicGeometry
