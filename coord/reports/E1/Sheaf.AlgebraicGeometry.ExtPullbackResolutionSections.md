## What changed

Completed the proof of AlgebraicGeometry.extPullback_resolution_sections without changing
its signature, definitions, or original public import. The proof imports two new modules
only for its proof: ExtPullbackHomComplex and ConstantSheafPullbackTranspose.

The Hom-complex map homPullbackMap is constructed degreewise; additivity and differential
compatibility are proved. The main theorem proves the square with complexSectionsIso by
fromSingleMk_surjective, evaluation naturality, and constantSheaf_pullback_transpose.
Applying the homology functor and expanding extSectionsIso combines this square with
extPullback_homComplex by associativity. The final proof has no sorry.

Also proved constantSheaf_pullback_transpose: left-adjoint uniqueness transposes the
constant-sheaf comparison, unit naturality handles the supplied morphism, and right-adjoint
uniqueness transports between global and terminal sections. Its two generic private helpers
are proved. No data are selected from an unproved existence theorem.

The unchanged sandbox copy of SheafHExtResolutionSectionsIso from the previous attempt was
removed from the delivery. Its original compiled dependency is now present. The delivery
contains no adaptations of other existing modules and no interface changes.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.extPullback_resolution_sections
(lem-weil-pbc-ext-pullback-resolution-sections).

Proved the new theorem AlgebraicGeometry.constantSheaf_pullback_transpose
(lem-weil-pbc-constant-sheaf-pullback-transpose), and constructed
AlgebraicGeometry.SheafPullbackResolution.homPullbackMap without any sorry.

One new hole remains, in its own new module:
AlgebraicGeometry.SheafPullbackResolution.extPullback_homComplex
(lem-weil-pbc-ext-pullback-hom-complex).
Its entire proof is `by sorry`; its docstring includes its source and proof in words.
It is the first step of the argument before evaluation: no section unit, sections comparison,
or evaluated resolution map occurs in its conclusion. The original theorem is proved by
combining this step with a separately proved chain-map square, so this is a decomposition,
not a full sorry-free proof. Holes closed: 1 original. Holes added: 1. Net: 0.

The remaining comparison uses exact inverse image, a homotopy of augmentations, and the
chosen injective target resolution; it does not assume the pulled-back resolution injective.
Degree zero, zero sheaves, empty schemes, and arbitrary supplied lifts compatible up to
homotopy are included. The transpose theorem holds for arbitrary coefficient groups; no
edge case is excluded. The definitions construct their actual maps.

## No longer needed

No original import removed and no original module pruned. The parent now needs the
Ext/Hom-complex comparison, the proved transpose, and the existing sections comparison.
Its former dependencies lem-weil-pbc-ext-via-injective-resolution,
lem-weil-pbc-kinjective-hom-derived, prop-weil-pbc-inverse-image-exact, and
def-weil-pbc-cohomology-pullback remain needed below the Ext/Hom-complex node; they are
not claimed globally pruned. No node realizing the unit statement or its steps is bypassed.
The unchanged extra sandbox copy of SheafHExtResolutionSectionsIso was removed; its original
public import is still required.

## Where the brief, the DAG or earlier work was wrong

The previous attempt left the final theorem sorry after constructing its chain-map square.
This repair completes the homology calculation, makes the evaluation-naturality helper
private, and proves the previously holed adjunction transpose as well. The stale report
claiming a missing compiled dependency and a complete proposed proof was corrected.
The compiled dependency is available in the current snapshot.

The existing searches found extMk_hom, mapExactFunctor_hom, rightDerived_app_eq, and
rightDerived_map_eq, but no direct cross-scheme Hom-complex formula. A new LeanFinder query
again found these component lemmas. Loogle's short Adjunction.leftAdjointUniq query did not
resolve; direct Mathlib/source searches located Adjunction.Unique, the defining
upperStarConstantSheafIso, constantSheafΓAdj, and lowerStarCompGlobalSectionsIso.
Their signatures and definitions supply a complete proof of the transpose. The original
node plan is followed through the two resolution-level steps, with the unit route preserved.

## New nodes

lem-weil-pbc-ext-pullback-hom-complex is stated in
lean/Sheaf/AlgebraicGeometry/ExtPullbackHomComplex.lean. It isolates the Ext computation on
unevaluated Hom complexes, with its explicit additive chain map. Its comparison theorem is
the single remaining sorry. Source: Stacks 06XR and the functoriality equations 01F9/01FA.

lem-weil-pbc-constant-sheaf-pullback-transpose is proved in
lean/Sheaf/AlgebraicGeometry/ConstantSheafPullbackTranspose.lean. It supplies the
constant-sheaf/global-sections adjunction calculation in the parent's second step; its DAG
proof now records the completed uniqueness/naturality calculation and has no proof holes.

No change records are necessary: no existing statement, definition, or public import changed.

## Second reading by E1

1. Statement preservation: compared `ExtPullbackResolutionSections.lean` with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports and proof terms were added.

2. Compilation and proof integrity: compiled all three delivered modules with `lcompile.py`; compilation succeeds. The target theorem and transpose theorem contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The sole remaining `sorry` is the named, documented split theorem `SheafPullbackResolution.extPullback_homComplex`, with its matching DAG node.

3. New statements: checked `constantSheaf_pullback_transpose` and `extPullback_homComplex` against their docstrings and source references. The former is the adjunction transpose needed by the evaluation square and is proved fully; the latter isolates exactly the unevaluated Hom-complex comparison and is strictly simpler than the target. Neither duplicates an existing library declaration; `homPullbackMap` is a concrete definition with no hollow data.

4. Pruning and route: proof-only imports are plain `import`; the public import of the original item is unchanged. The proof follows the unit route through the Hom-complex comparison, evaluation square, and homology map. Existing dependencies remain needed for the split comparison, so no additional pruning is justified.

5. DAG and unit agreement: updated node proof/dependency metadata matches the declarations and proof route, and the new split node records its source, blueprint, and complete natural-language proof. The unit route and realized steps remain intact.

Changed during second reading: added this review section only; no Lean statements or proofs were altered.
