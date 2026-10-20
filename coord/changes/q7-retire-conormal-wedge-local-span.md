# AlgebraicGeometry.conormal_wedge_mem_span_locally

## Reason

The human-authorized retirement list, coord/retire-items.tsv, names
Sheaf.AlgebraicGeometry.ConormalWedgeLocalSpan and its upstream twin.
The assigned module already compiles and has zero holes. The actual repair retires
its duplicate implementation and migrates its sole direct consumer to the official
library theorem. No upstream file is changed.

The upstream theorem uses exteriorPower and wedge; the local theorem uses
exteriorSheaf and exteriorSheafSection. The existing, proved theorem
exteriorSheafPresheaf_eq_exteriorPower identifies their presheaves. Pair each
presheaf with its pure-wedge maps in a dependent pair: their first components are
equal and their second components are heterogeneously equal by reflexivity.
A predicate on such pairs expresses the entire sheafified restriction-and-span
conclusion. Equality of the pairs therefore transports that conclusion directly,
including every dependent type. This argument is generic in the sheaf M.
The concrete compatibility helper applies it to the pullback of the ideal sheaf,
with the generator type given explicitly to avoid unfolding tensorPullback during
inference. Profiling also found unnecessary reductions of the pullback and
sheafification constructions. Inside a section containing only the two new helpers,
local irreducibility keeps tensorPullback, tensorPullbackObj, sheafification and
exteriorSheafRestriction behind their APIs. The section ends before all existing
helpers, so these local attributes affect no existing declaration or importer.
Both new helpers are private and proved.

## Old

In Sheaf.AlgebraicGeometry.ConormalWedgeLocalSpan:

```lean
theorem conormal_wedge_mem_span_locally
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (n : ℕ)
    (V : Y.affineOpens) (W : Z.Opens) (hW : W ≤ i ⁻¹ᵁ V.1)
    (a : Fin n → ((Scheme.Modules.tensorPullback i).obj i.ker.toModules).val.obj (op W))
    (x : Z) (hx : x ∈ W) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let E := Scheme.Modules.exteriorSheaf N n
    let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
      i.ker.toModules
    ∃ (W' : Z.Opens) (hW' : W' ≤ W), x ∈ W' ∧
      E.val.map (homOfLE hW').op (Scheme.Modules.exteriorSheafSection N n W a) ∈
        Submodule.span (Z.presheaf.obj (op W'))
          (Set.range (fun b : Fin n → i.ker.toModules.val.obj (op V.1) ↦
            Scheme.Modules.exteriorSheafSection N n W'
              (fun j ↦ N.val.map (homOfLE (hW'.trans hW)).op
                (η.val.app (op V.1) (b j)))))
```

## New

The local module is withdrawn through deleted.txt. Its node points to the existing
upstream theorem in WeilConjectures.AlgebraicGeometry.ConormalWedgeLocalSpan:

```lean
theorem conormal_wedge_mem_span_locally
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (n : ℕ)
    (V : Y.affineOpens) (W : Z.Opens) (hW : W ≤ i ⁻¹ᵁ V.1)
    (a : Fin n → ((Scheme.Modules.tensorPullback i).obj i.ker.toModules).val.obj (op W))
    (x : Z) (hx : x ∈ W) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let E := Scheme.Modules.exteriorPower N n
    let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
      i.ker.toModules
    ∃ (W' : Z.Opens) (hW' : W' ≤ W), x ∈ W' ∧
      E.val.map (homOfLE hW').op (wedge (M := N) (r := n) (U := W) a) ∈
        Submodule.span (Z.presheaf.obj (op W'))
          (Set.range (fun b : Fin n → i.ker.toModules.val.obj (op V.1) ↦
            wedge (M := N) (r := n) (U := W')
              (fun j ↦ N.val.map (homOfLE (hW'.trans hW)).op
                (η.val.app (op V.1) (b j)))))
```

The sole direct consumer, Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates,
replaces the private proof import by the upstream module and adds the private
ExteriorSheafPresheafComparison import. A private, fully proved generic transport helper and a concrete compatibility
helper recover the old span conclusion. The existing local_wedge_agreement_of_ideal_generators
helper calls this compatibility helper. Every other existing proof and every
existing signature, visibility, definition, docstring and public import is retained.
The parent's node records the comparison transport; its statement is unchanged.

## Users

Computed with tools/downstream.py Sheaf.AlgebraicGeometry.ConormalWedgeLocalSpan
--uses conormal_wedge_mem_span_locally. Three modules are downstream; only one
imports the retired module or uses its theorem. Current claim files contain no
claim for these three modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates | unclaimed | Replace the private proof import, add a proved private comparison helper, and update its one call; public theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.SelfTorCompatibleAffineMaps | unclaimed | Transitive consumer; public interface of its dependency is unchanged; no edit required. |
| Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates | unclaimed | Transitive consumer; public interface of its dependency is unchanged; no edit required. |

The item itself is assigned to Q7. Its private exterior_section_map and
exterior_section_smul helpers are implementation details not visible to consumers;
the consumer already has its own restriction helper. No source-library declaration
is removed or altered. All DAG parents retain the mathematical span dependency;
only its Lean attachment moves upstream. No quarantined parent cites this item.

The adapted direct consumer compiles with no warnings through lcompile.py (22.0 s).
Its sole public theorem signature is byte-for-byte equal to the original.
The overlaid import closure has no Sheaf/upstream twin pair,
and no import of the withdrawn module. The transport requires neither n > 0 nor
a nonzero section ring: the presheaf equality and identical pure-wedge maps include
empty tuples, empty opens, and zero modules. No target statement or target definition changes, and
the Picard-duality unit route is preserved. No new nodes or holes are introduced.
The full delivery axiom probe also completed (20.7 s, SHEAF-PROBED 1), with
no axiom or direct-sorry findings. The delivery tool performs the packet checks.

## Status

landed 20261020T221314-L-4171097 2026-10-20 (merge of deliver/Q7/Sheaf.AlgebraicGeometry.ConormalWedgeLocalSpan)
