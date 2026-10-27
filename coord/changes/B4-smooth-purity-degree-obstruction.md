# AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothPurityMap

## Reason

Certify the existing missing-smoothness dispute by a genuine cohomology argument.
This is a partial proof delivery, not a signature correction or completed trace repair.
The four original holes remain. No public upstream signature, attribute, public import,
or non-theorem body changes; no definition or instance body is filled in this packet.

The new public theorem lives under Sheaf and is proved without smoothTrace,
smoothPurityMap, or the disputed isIso_smoothPurityMap instance. The source module
consumes it in a proved private lemma placed before that instance is declared. Its
hypothetical inverse is formed from an explicit local invertibility assumption.

## Old

The existing disputed instance remains exactly:

```lean
instance isIso_smoothPurityMap : IsIso (smoothPurityMap ℓ f d) :=
  sorry
```

There was no private smoothPurityMap_not_isIso_of_open declaration and neither
Sheaf.SmoothPurity.OpenDimensionObstruction nor Sheaf.SmoothPurity.PointUnitNonzero module.

## New

The same instance and its body remain verbatim. Add two private proof imports,
a diagnostic comment, and this private theorem to the source module:

```lean
omit [SmoothOfRelativeDimension d f.left] in
/-- A concrete obstruction to the missing smoothness hypothesis: on an open immersion
with positive proposed relative dimension and nonzero coefficient unit, no trace can
have an invertible adjoint. This is proved before the disputed instance is available;
the inverse below is formed only from the explicit hypothetical invertibility. -/
private theorem smoothPurityMap_not_isIso_of_open [IsOpenImmersion f.left]
    (hd : 0 < d)
    (hunit : ¬ CategoryTheory.Limits.IsZero
      (𝟙_ (Mod (Sheaf (ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))) :
    ¬ IsIso (smoothPurityMap ℓ f d) := by
  intro h
  exact hunit (isZero_unit_of_open_positive_purity ℓ f d hd
    ((ObjectProperty.ι _).mapIso
      (@asIso _ _ _ _ (smoothPurityMap ℓ f d) h).symm))

```

The imported new public theorem says that a positive-dimensional purity-shaped
isomorphism on an open immersion forces the source regular coefficient module to
be zero. Its proof identifies the left side with the degree-zero unit, rewrites
the shifted Tate single in degree -2d, and applies zeroth cohomology. The natural
condition d>0 is essential; empty sources are explicitly allowed. No assumption
about nonvanishing of the Tate module, or any construction of normalized trace,
is smuggled into the statement.

Also add this proved formal Step 4 helper; it establishes invertibility from
the explicitly supplied normalized comparison and trace formula without
choosing either one. The preceding geometric construction remains unresolved.

```lean
omit [SmoothOfRelativeDimension d f.left] in
/-- The formal last step of the normalized trace construction. Once the geometric
comparison is an isomorphism and the chosen trace is its counit transpose, the actual
purity map is that comparison and is invertible. No comparison is chosen here. -/
private theorem isIso_smoothPurityMap_of_trace_formula
    (e : boundedConstructibleTateTwist ℓ X d (2 * d) ≅
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map e.hom ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ f).counit.app (𝟙_ _)) :
    IsIso (smoothPurityMap ℓ f d) := by
  have h : smoothPurityMap ℓ f d = e.hom := by
    change (boundedConstructibleUpperShriekAdjunction _ ℓ f).homEquiv _ _
      (smoothTrace ℓ f d) = e.hom
    rw [htrace, ← (boundedConstructibleUpperShriekAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ f).homEquiv_counit _ _ e.hom]
    exact ((boundedConstructibleUpperShriekAdjunction _ ℓ f).homEquiv _ _).apply_symm_apply _
  rw [h]
  infer_instance

```

The native unit nonvanishing is also proved in the new PointUnitNonzero module.
It uses the existing isEquivalence_upperStarFromPointMod declaration, whose
proof remains sorry, and the actual coefficient ring evaluated at a singleton.
The source privately combines it with the obstruction in this concrete example,
before the disputed instance exists:

```lean
section PointObstruction

omit [Fact (ringChar k).Prime] in
private theorem pointObstruction_locallyOfFiniteType :
    LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))

omit [Fact (ringChar k).Prime] in
private theorem pointObstruction_quasiCompact :
    QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))

omit [Fact (ringChar k).Prime] in
private theorem pointObstruction_isSeparated :
    IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))

attribute [local instance] pointObstruction_locallyOfFiniteType
  pointObstruction_quasiCompact pointObstruction_isSeparated

omit [SmoothOfRelativeDimension d f.left] in
/-- At a separably closed point, the identity map with proposed dimension one is a
counterexample to the elaborated, unconditionally quantified purity instance. This
proof is before that instance and uses only the nonvanishing of the native unit. -/
private theorem smoothPurityMap_point_dimension_one_not_isIso [IsSepClosed k] :
    ¬ IsIso (smoothPurityMap ℓ (𝟙 (Over.mk (𝟙 (Spec (.of k))))) 1) := by
  exact smoothPurityMap_not_isIso_of_open ℓ _ 1 (by decide)
    (not_isZero_unit_on_separablyClosed_point ℓ k)

end PointObstruction
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SmoothPurity.Defs | B4 | Private consumer and diagnostic comment; public interface unchanged. |
| Sheaf.SmoothPurity.OpenDimensionObstruction | new, B4 | Proved public obstruction, with its own DAG node. |
| Sheaf.SmoothPurity.PointUnitNonzero | new, B4 | Proved native point-unit nonvanishing, with its own DAG node. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Direct importer, no interface change to consume. |
| TargetsCheck | unclaimed | Direct importer, no interface change to consume. |
| WeilConjectures | unclaimed | Direct importer, no interface change to consume. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Direct importer; smoothPurityMap signature unchanged. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Direct importer; smoothPurityIso signature unchanged. |

The direct downstream scan found the five existing importers listed above. None
requires adaptation: there are no changed signatures, public imports, instances,
attributes, or reducibility settings. The new modules' direct consumer is
the item itself, compiled together with it. No other group's module is edited. The private point identity-property lemmas
are registered as instances only locally inside PointObstruction; their
registration does not survive that section or affect importers.
The unit route and all existing node proof dependencies stay in place. The
isIso node records the completed formal adjunction assembly as a partial proof
step; its statement and proof route are unchanged.

## Status

landed 20261027T012810-L-2332547 2026-10-27 (merge of deliver/B4/WeilConjectures.SmoothPurity.Defs)
