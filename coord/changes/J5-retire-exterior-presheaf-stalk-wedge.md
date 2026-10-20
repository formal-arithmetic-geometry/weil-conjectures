# AlgebraicGeometry.Scheme.Modules.exteriorPresheaf_stalk_wedge

## Reason

Retire the duplicate Sheaf module under the human's 2026-10-20 retirement instruction,
recorded in coord/changes/retire-sheaf-twins-20261020.md and coord/retire-items.tsv.
Both the old theorem and its upstream twin are fully proved. Their sectionwise
exterior presheaves have identical section modules but differently constructed
restriction maps. Merely swapping the import would therefore be ill-typed.

The only direct consumer is ExteriorSheafStalkComparison (unclaimed). Its private
helper proves equality of the two restriction maps by the old restriction's
uniqueness on pure wedges. The identity section maps then form a presheaf-module
morphism from the upstream exterior presheaf to the retained one. Its additive
stalk map is linear over the commutative stalk ring, by representing a scalar
and a vector on a common neighborhood and applying the germ scalar formula.
Composing it with the upstream alternating map recovers exactly the old formula.
This adaptation changes no public signature, definition or public import in the
consumer, and adds no hole. To prevent expensive unfolding, the existing private
exteriorGermMap and the new private stalk-map construction are irreducible and
unexposed, with their wedge and germ formulas proved by unfolding once. The
original exteriorGermMap data body is unchanged. The transported alternating
map is also a private irreducible construction with an explicit germ formula.
Both the comparison and its unchanged immediate consumer
ExteriorTensorStalkKernelSpan compile in the sandbox overlay (46.8 and 11.8 s).
The final comparison uses explicit equalities on wedge generators in
exteriorGermMap_res, avoiding an expensive quotient rewrite; it compiles in
22.8 seconds. No upstream file or target is changed.

## Old

Defined in Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafStalkWedge:

```lean
theorem exteriorPresheaf_stalk_wedge {X : Scheme.{v}} (M : X.Modules)
    (n : ℕ) (x : X) :
    ∃ b : (M.presheaf.stalk x) [⋀^Fin n]→ₗ[X.presheaf.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{v}) (exteriorSheafPresheaf M n).presheaf x),
      ∀ (U : X.Opens) (hx : x ∈ U) (a : Fin n → M.val.obj (op U)),
        b (fun i ↦ M.presheaf.germ U x hx (a i)) =
          TopCat.Presheaf.germ (exteriorSheafPresheaf M n).presheaf U x hx
            (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a)
```

## New

Use the existing theorem in
WeilConjectures.AlgebraicGeometry.Modules.ExteriorPresheafStalkWedge:

```lean
theorem exteriorPresheaf_stalk_wedge {X : Scheme.{v}} (M : X.Modules)
    (n : ℕ) (x : X) :
    ∃ b : (M.presheaf.stalk x) [⋀^Fin n]→ₗ[X.presheaf.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{v})
          (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).presheaf x),
      ∀ (U : X.Opens) (hx : x ∈ U) (a : Fin n → M.val.obj (op U)),
        b (fun i ↦ M.presheaf.germ U x hx (a i)) =
          TopCat.Presheaf.germ
            (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).presheaf U x hx
            (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a)
```

The old module is deleted. The retained consumer converts between the presheaves
with the identity-on-sections morphism, so its exteriorSheaf statement has its
original meaning. The node attachment points to the upstream theorem and records
the conversion. The consumer node records the same proof route.

## Users

The downstream scan found the following fourteen modules. Only
ExteriorSheafStalkComparison imports the retired module or uses the theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Unchanged: uses the retained exterior-sheaf comparison interface; no direct wedge-theorem use. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel | unclaimed | Unchanged: uses the retained exterior-sheaf comparison interface; no direct wedge-theorem use. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Unchanged: uses the retained exterior-sheaf comparison interface; no direct wedge-theorem use. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Unchanged: uses the retained exterior-sheaf comparison interface; no direct wedge-theorem use. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism | unclaimed | Unchanged: uses the retained exterior-sheaf comparison interface; no direct wedge-theorem use. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue | unclaimed | Unchanged: uses the retained exterior-sheaf comparison interface; no direct wedge-theorem use. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal | unclaimed | Unchanged: uses the retained exterior-sheaf comparison interface; no direct wedge-theorem use. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt | unclaimed | Unchanged: uses the retained exterior-sheaf comparison interface; no direct wedge-theorem use. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor | unclaimed | Unchanged: uses the retained exterior-sheaf comparison interface; no direct wedge-theorem use. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafStalkComparison | unclaimed | Adapted: import the upstream twin, compare restrictions, and transport the wedge map. Public signatures stay identical. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelLocallySpanned | unclaimed | Unchanged: uses the retained exterior-sheaf comparison interface; no direct wedge-theorem use. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelRelations | unclaimed | Unchanged: uses the retained exterior-sheaf comparison interface; no direct wedge-theorem use. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorTensorStalkKernelSpan | unclaimed | Unchanged: uses the retained exterior-sheaf comparison interface; no direct wedge-theorem use. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Unchanged: uses the retained exterior-sheaf comparison interface; no direct wedge-theorem use. |

## Status

landed 20261020T141311-L-2034208 2026-10-20 (merge of deliver/J5/Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafStalkWedge)
