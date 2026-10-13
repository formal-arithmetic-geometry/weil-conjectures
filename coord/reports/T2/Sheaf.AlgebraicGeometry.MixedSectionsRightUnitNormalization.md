## What changed

Proved `AlgebraicGeometry.mixedSections_right_unit_normalization` in
`Sheaf.AlgebraicGeometry.MixedSectionsRightUnitNormalization`, without changing its
signature, visibility, imports, definitions, or existing docstring. The proof follows
all three steps of the existing node plan, so no node update is necessary.

Two proved private helpers carry the calculations. `mixed_unit` extracts the chosen
Leray comparison's unit equation. Its underived comparison equals `Iso.refl` by the
pointwise identity clause of `exists_mixedGlobalSectionsDirectImageIso`; the two
homotopy comparison factors then cancel. `scalar_factor` applies
`Functor.mapDerivedCategoryNatIso_fach` and `Functor.mapDerivedCategoryCompIso_fach`.
Restriction-of-scalars comparison maps induce identity maps on the homotopy category;
postcomposition by the invertible factor maps proves the inverse-factor equation.
The main proof cancels the mapped direct-image inverse/hom pair, applies `mixed_unit`
for the composite map, moves the global-sections unit by naturality, applies
`scalar_factor`, and finishes by the definitional identity of the underived sections.
No K-injectivity assumption or derived-unit cancellation is used.

Validation: the module compiles through `lcompile.py` with no errors or warnings.
Searches used local `rg`, Loogle for derived factors, Lean Finder for localization
composition compatibility, and the prescribed grep service. The generic factor
identities in the source library supply the short route; no new intermediate
statement is needed.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.mixedSections_right_unit_normalization`
(node `lem-sc-mixed-sections-right-unit-normalization`).
No holes added. No `sorry` remains in the delivered module. Both private helpers
are proved completely. Existing imported declarations retain their own dependencies;
this delivery does not claim to close the whole target import closure.

## No longer needed

None. All three existing public imports supply objects appearing in the unchanged
statement. No proof import was added, no module was pruned, and both existing proof
nodes (`def-pc-global-hom-pullback-comparison` and
`lem-sc-mixed-global-sections-direct-image-iso`) remain used. The normalized
direct-image composition isomorphism is used only through its inverse law;
its derived-unit compatibility theorem is not needed here, as the existing plan says.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing plan fits the statement.
Some rewrites require `erw` because the statement mixes definitionally equal
preadditive instances and global-sections functor presentations. This affects
elaboration only, not the theorem or its hypotheses. Identity maps, zero complexes,
and empty schemes require no separate assumptions; all calculations are functorial
and the proof keeps the sheaf and module localization universes independent.

## Second reading by T2

1. **Interface: pass.** Read the full repository/sandbox diff and checked the
   existing theorem's signature byte for byte. Its hypotheses, conclusion,
   visibility, preceding options, imports, and docstring are unchanged. No
   definition or existing declaration was altered; no change record is needed.
2. **Proof: pass.** Compiled the delivered module with `lcompile.py`, without
   errors or warnings. Compiled a scratch copy with `#print axioms` for
   `scalar_factor`, `mixed_unit`, and
   `AlgebraicGeometry.mixedSections_right_unit_normalization`: each uses only
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Scanned for holes and forbidden declarations/options: none. The helpers
   prove genuine component calculations. Cancellation is only by isomorphisms,
   never by a potentially noninvertible derived unit. The comparison choices
   are existing normalized constructions characterized by unit equations;
   this delivery constructs no data from arbitrary existence witnesses.
3. **Split statements: pass, none.** No new open statement, module, or node was
   added. Read both helper calculations and the defining comparison equations.
   The equations work for identity maps, zero complexes, and empty schemes
   without additional assumptions. Independent local searches for scalar
   factors, mixed units, and derived-comparison compatibility in `lean/` and
   the upstream library confirmed the generic `mapDerivedCategoryNatIso_fach`
   and `mapDerivedCategoryCompIso_fach` lemmas used here; no shorter existing
   specialized result was found.
4. **Route and pruning: pass.** The main proof follows all three existing node
   steps. All three public imports provide declarations used in the unchanged
   statement; none is merely a proof import. Both old proof dependencies are
   used, so `No longer needed` is complete. Read
   `dag/units/sk-thm-picard-duality.json`: its `realized` fields are untouched,
   and this component proof bypasses no realized unit statement or step.
5. **DAG: pass.** Read the item's node and dependency declarations. Its `proof`,
   `proof_deps`, and `proof_origin` describe the actual cancellation, mixed
   unit equation, and naturality/scalar-factor calculation. No node update is
   necessary. The normalized direct-image comparison occurs in the signature
   and is canceled by its inverse law; its separate mate theorem is not used.

Second reading changed only this report by adding the independent review record.
The Lean proof required no repair. One original hole is closed, zero are added,
zero statements are split off, and no module is pruned.
