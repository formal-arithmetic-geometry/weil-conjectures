## What changed

Closed `AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_comparison` by
specializing the existing `higherDirectImageRawTransition_toHom`, rewriting the
canonical transition using `higherDirectImageOverMap_coefficient`, and applying
free-sheaf section evaluation naturality. Added proof-only imports of
`Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom` and
`Sheaf.AlgebraicGeometry.HigherDirectImageOverMapCoefficient`. The private proved
`evaluation_postcomp` is the evaluated component of `freeSheafSections_naturality`.

Shared the original restricted single complexes and fixed coefficient composite in
`Sheaf.AlgebraicGeometry.HigherDirectImageRawOverComplex` and
`Sheaf.AlgebraicGeometry.HigherDirectImageRawOverCoefficient`. The three existing
raw-over constructions now refer to these actual data, which contain no new choices.
Added the public import supporting these definitions. Every existing type signature,
visibility and docstring stays unchanged; the raw pullback wrapper is now marked `implicit_reducible`.
The data are definitionally identical to
the original constructions, and the unit's route is unchanged. The restriction proof
now unfolds the raw-over definition and applies the existing triangle restriction
proof directly; this removes an expensive redundant typed coefficient expansion.

Repair H10: the shared complex and coefficient are now semireducible definitions
with proved `higherDirectImageRawOverComplex_eq` and
`higherDirectImageRawOverCoefficient_heq` equations. These equations transport the
existing coefficient composition theorem without expensive kernel unfolding.
The raw pullback wrapper is an `implicit_reducible` definition, so the unchanged identity proof
can unfold
it at its existing transparency level. The composition proof uses local
irreducibility for the shared data and combines the transported coefficient identity
with the existing raw triangle composition theorem.

All five final delivered modules compiled in import order: complex 6.4 s,
coefficient 35.5 s, coefficient-map lemma 17.5 s, main module 13.6 s, and
composition formula 5.3 s. The unchanged limit is 60 seconds per file.

All six direct importers and both additional users compile against the final
changed dependencies. The composition formula is the delivered adaptation;
the other seven files are the verbatim repository originals:

| Module suffix | Seconds |
|---|---:|
| HigherDirectImageRawAffineClassVanishing | 13.6 |
| HigherDirectImageRawAffineImageRep | 24.9 |
| HigherDirectImageRawPullbackCompositionFormula | 4.8 |
| HigherDirectImageRawPullbackIdentity | 51.3 |
| HigherDirectImageRawPullbackComposition | 4.3 |
| HigherDirectImageRawDiagram | 25.3 |
| HigherDirectImageColimitComparisonEpi | 20.8 |
| HigherDirectImageLocalClassVanishing | 51.7 |

Updated the comparison node's proof route and added the three helper nodes.
The definition change is recorded in
`coord/changes/higherDirectImageRawOverPullback-share-data.md`. The downstream
`HigherDirectImageRawPullbackCompositionFormula` requires a proof adaptation
to the shared objects, described below; its statement and visibility are unchanged.

## Proved and sorry left

Closed the original module's only hole:
`AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_comparison`
(node `sbc-lem-higher-image-raw-over-comparison`). No `sorry` remains in the item.
The already proved restriction and conjunction declarations remain proved.
The repair additionally proves `higherDirectImageRawOverComplex_eq`,
`higherDirectImageRawOverCoefficient_heq` and the private
`restrictedCoefficient_comp`; the existing function composition theorem stays proved.
No additional hole is introduced by the repair.

Added one hole:
`AlgebraicGeometry.Etale.higherDirectImageOverMap_coefficient`
(node `sbc-lem-higher-image-over-map-coefficient`). This is a decomposition: one
upper hole is closed and one strictly smaller hole is added, for net zero textual
holes. The remaining theorem compares sheaf morphisms constructed by homology and
functoriality; it has no test object, raw class, raw comparison, or evaluation map.
Its docstring and node give the full functoriality and associativity proof. The shared
complex and coefficient definitions contain actual data and no holes.

The imported existing theorem
`AlgebraicGeometry.Etale.higherDirectImageRawTransition_toHom`
(node `sbc-lem-higher-image-raw-transition-to-hom`) retains its pre-existing hole.
This delivery uses it as the stage-3 brief instructs; it does not claim to close the
underlying derived-adjunction calculation. The remaining coefficient identity is
valid for all integer degrees, identity arrows and zero coefficient sheaves, since
it uses only functoriality and associativity and imposes no new hypothesis.

## No longer needed

No existing imports or globally needed modules are removed. Every original public
import supports the unchanged statements and constructions. The unused provisional
private `comparison_app` helper was removed; expansion of the comparison is now a
single definitional `change`. The unsuccessful alternative coefficient-naturality
route and all diagnostic modules remain only in scratchpad and are not delivered.

The comparison node no longer directly uses any of its four old proof dependencies:
`prop-weil-pbc-derived-inverse-image-adjunction`,
`sbc-lem-higher-image-raw-triangle-restriction`,
`def-sbc-module-higher-image-transitions`, or
`lem-weil-pbc-inverse-image-composition`. The existing general comparison
encapsulates the derived-adjunction argument; the coefficient identity and its
concrete coefficient construction encapsulate the transition and inverse-image
composition definitions. These are not claimed globally pruned.
The triangle module stays needed for the restriction proof. No modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The original comparison node did not cite the existing pre-evaluation raw triangle
comparison. The saved attempt could not finish because it repeatedly expanded the
restricted single complexes and coefficient composite during kernel checking.
Sharing those same data with explicit types fixes the expensive definitions and
makes the full comparison compile within the 60-second limit. No time limit was
raised, no proof file was split to evade the limit, and no statement was weakened.

The previous returned delivery did not make the composition and identity modules
compile within the limit. Its adaptation description also did not describe its code.
The repair changes the shared-data transparency and provides proved equations;
the report and change record below describe the final adaptation. The stale second
reading of the earlier files is removed; the independent reader must repeat it
against these actual files.

The coefficient-map identity is elementary mathematically, but attempts to elaborate
its complete functoriality proof still reached the file timeout. It remains a named
proper subproblem, with its proof in words and source. No mathematical error was found.

## New nodes

`def-sbc-higher-image-raw-over-complex`, in
`Sheaf.AlgebraicGeometry.HigherDirectImageRawOverComplex`, shares the actual
single complex `(B^*G)[0]` using the existing Mathlib single functor.

`def-sbc-higher-image-raw-over-coefficient`, in
`Sheaf.AlgebraicGeometry.HigherDirectImageRawOverCoefficient`, shares the original
single-functor comparison followed by the original inverse-image composition map.

`sbc-lem-higher-image-over-map-coefficient`, in
`Sheaf.AlgebraicGeometry.HigherDirectImageOverMapCoefficient`, isolates the mapped
coefficient-composite identity. Its full proof uses the unchanged definitions,
`Functor.map_comp`, and associativity. All three nodes are sourced from the fixed
constructions in Stacks Tags 03Q8 and 09Z1; all three kinds of search are recorded.

Change record: `coord/changes/higherDirectImageRawOverPullback-share-data.md`.

## Forced adaptations

`Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula`
(current holder: unclaimed). The original module compiled against the published
baseline in 40.1 seconds. Against the final changed dependencies, the original fails in
4.5 seconds at
line 60 with `Type mismatch: After simplification, term h`. Its expanded complexes
and coefficients do not match the shared data in the expected pullbacks; Lean also
reports unexposed `equivShrink`. This is a compiler error, not a timeout.
Only the forced composition proof is adapted;
`HigherDirectImageRawPullbackIdentity` is unchanged and compiles in 49.7 seconds.
The unchanged `HigherDirectImageRawAffineImageRep` also compiles in 25.6 seconds;
the wrapper's implicit reducibility permits its existing local irreducibility attribute.

The adaptation adds `set_option backward.isDefEq.respectTransparency true` and
local irreducibility for the shared complex and coefficient. A proved private
`restrictedCoefficient_comp` transports the original coefficient composition identity
by congruence, using `higherDirectImageRawOverComplex_eq` and
`higherDirectImageRawOverCoefficient_heq`. After `funext z` and `change`, the public
proof applies `congrArg` to that identity, reverses the resulting equality and
composes it with `higherDirectImageRawTrianglePullback_comp`. The expanded
complex/coefficient lets, `dsimp`, `rw [hc]` and final `simpa` are replaced by this
proof. Existing signatures, visibility, imports and docstrings are unchanged.


## Second reading by P3

1. Interface and meaning: PASS. Independently diffed all five delivered modules
   against the repository. All seven existing declaration signatures, visibility
   and docstrings are byte-for-byte unchanged. The three raw-over definition
   bodies and the pullback transparency attribute change exactly as the change
   record declares. The shared complex is the original single-functor object;
   the shared coefficient is the original two-map composite. Their equations
   are proved by reflexivity. Hence no hypothesis or conclusion changes and
   no target using these constructions changes its mathematical meaning.
   The only other existing module edited is the composition formula; its
   theorem statement is unchanged. Its original compiles against the published
   baseline (48.7 seconds), but fails with the documented type mismatch at
   line 60 against the delivered dependencies (10.4 seconds). The adapted proof
   changes only what transports this representation and compiles (6.5 seconds).

2. Proof and axioms: PASS. Compiled the five actual delivered modules in import
   order: complex 9.7 seconds, coefficient 46.5, coefficient-map lemma 22.0,
   main module 18.0, composition formula 6.5. No compiler error or warning.
   A scratch module prints axioms of every public delivered declaration,
   including the shared definitions and their equations. Only propext,
   Classical.choice and Quot.sound occur, with sorryAx precisely in the
   coefficient-map lemma, comparison and conjunction. The comparison and
   conjunction depend on the documented coefficient hole and the existing
   raw-transition hole; the restriction and composition theorems have no
   sorryAx. Delivery's probe additionally checks every private constant.
   Text inspection finds only the one whole-proof sorry in the named public
   coefficient-map theorem, and no forbidden declaration or holed definition.
   All seven unchanged consumers compile against the final delivery overlay:
   affine-class vanishing 34.5 seconds, affine-image representation 41.1,
   pullback identity 50.4, pullback composition 8.1, raw diagram 45.1,
   colimit comparison 32.3, local class vanishing 51.7. Identity and local
   vanishing initially timed out during concurrent checks; the final separate
   checks use the same sources and unchanged 60-second limit.

3. Split statements: PASS. The coefficient-map equality is a proper subproblem:
   it identifies a sheaf morphism using only two functor map-comp laws and
   associativity, and contains no raw class, test object, evaluation or raw
   comparison. Expanded higherDirectImageOverMap and higherDirectImageTransition
   by reading their definitions; their factors are exactly those described in
   the docstring. Identity arrows, zero coefficients and all integer degrees
   do not change this formal calculation. No arbitrary witness is chosen.
   Repeated Loogle, Lean Finder and repository searches with different queries.
   Functor.map_comp is an existing constituent; the identity proof and private
   abelian coefficient laws confirm the route but are not this statement.
   No exact duplicate was found. Added these searches to its new node.
   Attempts to close the coefficient lemma by direct functoriality, simp and
   a factored equality term reached the existing 60-second compile limit;
   none is delivered. The complete proof in words and matching node remain.

4. Route, imports and pruning: PASS after the report correction below.
   The proof specializes the existing pre-evaluation raw transition, rewrites
   its homology map by the coefficient identity, and applies the component
   of the existing freeSheafSections_naturality. This is the direct route from
   existing declarations, not a restatement of the item. Public imports supply
   statements or exposed construction bodies; both newly added proof-only
   imports are plain imports. The composition adaptation retains its original
   proof imports. The unit sk-lem-failure-field and its realized fields are
   untouched: these generic cohomology tools change no unit-level step.
   No import or module is globally pruned. The comparison node no longer
   directly uses all four old proof dependencies, now completely listed under
   No longer needed. This is one hole closed and one smaller hole added,
   a decomposition with net zero textual holes, not an independent completed
   comparison theorem.

5. Nodes and records: PASS. Compared both existing node diffs; only proof,
   proof_deps and proof_origin change. Every uses-list union equals the new
   proof_deps, and the recorded route matches the actual Lean applications.
   The three new nodes have the item's chapter and unit, source, construction
   or complete proof, search records, worker creation and Lean records.
   Their mathematical statements match the Lean signatures. The change record
   contains the original and final definitions, their users and the exact
   forced composition adaptation. It introduces no arbitrary data or hidden
   assumptions.

Second-reading changes: completed No longer needed with the omitted old
transition-definition and inverse-image-composition dependencies; added the
independent searches to sbc-lem-higher-image-over-map-coefficient; recorded
this independent reading and actual compile/axiom checks. No delivered Lean
proof or definition needed rewriting. No further hole was closed or added.

## Forced adaptations

### Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula
Original against changed dependencies failed:
```
at Λ].mapDerivedCategoryPlusSingleFunctor 0).hom.app ((B.hom)^*[ModuleCat Λ].obj G) ≫
        (DerivedCategory.Plus.singleFunctor (Sheaf A.left.smallEtaleTopology (ModuleCat Λ)) 0).map
          ((upperStarComp (ModuleCat Λ) (Over.Hom.left f) B.hom A.hom ⋯).inv.app G))
      U
      (higherDirectImageRawTrianglePullback Λ (Over.Hom.left g) (C.hom ≫ k) (B.hom ≫ k) ⋯ q
        ((DerivedCategory.Plus.singleFunctor (Sheaf C.left.smallEtaleTopology (ModuleCat Λ)) 0).obj
          ((C.hom)^*[ModuleCat Λ].obj G))
        ((DerivedCategory.Plus.singleFunctor (Sheaf B.left.smallEtaleTopology (ModuleCat Λ)) 0).obj
          ((B.hom)^*[ModuleCat Λ].obj G))
        (((Over.Hom.left g)^*[ModuleCat Λ].mapDerivedCategoryPlusSingleFunctor 0).hom.app
            ((C.hom)^*[ModuleCat Λ].obj G) ≫
          (DerivedCategory.Plus.singleFunctor (Sheaf B.left.smallEtaleTopology (ModuleCat Λ)) 0).map
            ((upperStarComp (ModuleCat Λ) (Over.Hom.left g) C.hom B.hom ⋯).inv.app G))
        U z))
but is expected to have type
  @Eq (↑((higherDirectImageRawOverPresheaf Λ k G q A).obj (op U)))
    (higherDirectImageRawTrianglePullback Λ (Over.Hom.left f ≫ Over.Hom.left g) (C.hom ≫ k) (A.hom ≫ k) ⋯ q
      (higherDirectImageRawOverComplex Λ G C) (higherDirectImageRawOverComplex Λ G A)
      (higherDirectImageRawOverCoefficient Λ G (f ≫ g)) U z)
    (higherDirectImageRawTrianglePullback Λ (Over.Hom.left f) (B.hom ≫ k) (A.hom ≫ k) ⋯ q
      (higherDirectImageRawOverComplex Λ G B) (higherDirectImageRawOverComplex Λ G A)
      (higherDirectImageRawOverCoefficient Λ G f) U
      (higherDirectImageRawTrianglePullback Λ (Over.Hom.left g) (C.hom ≫ k) (B.hom ≫ k) ⋯ q
        (higherDirectImageRawOverComplex Λ G C) (higherDirectImageRawOverComplex Λ G B)
        (higherDirectImageRawOverCoefficient Λ G g) U z))

Note: The following definitions were not unfolded because their definition is not exposed:
  equivShrink ↦ 36

(with the modules compiled into /tmp/forced-adaptation-c4kiqf73/.lbuild) [6.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
