## What changed

Corrected the false arbitrary-identification interface of
`AlgebraicGeometry.formalFunctions_degreeZero_compatibility` to choose its two
identifications jointly and prove that the stalk equivalence has exactly the
canonical augmentation as its underlying linear map, as recorded in
`coord/changes/formalFunctions_degreeZero_compatibility.md`.
The parent now constructs the stalk equivalence from the actual stalk map of the
zeroth derived direct-image augmentation, proves bijectivity using left exactness,
and combines this with the fibre-system augmentation compatibility obligation.
No data is selected from an unproved mere-existence statement.

Added `Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroAugmentationCompatibility`
for the remaining fibre-system and germ equation, with the fixed augmentation
map in its statement. This removes the stalk-equivalence existence part from the
remaining obligation and pins the map to the one used by theta.
The dictionary's exact signature and visibility are unchanged; its forced proof
adaptation extracts the corrected joint witnesses and discards the additional canonical-map
equality.
Existing DAG proof records now describe the actual Lean reductions.

## Proved and sorry left

No proof of the original false arbitrary-a,b statement is claimed. Its correction
is an interface repair. The replacement
`AlgebraicGeometry.formalFunctions_degreeZero_compatibility` has a complete Lean
reduction: the stalk-equivalence construction and bijectivity are proved, while
the fibre-system compatibility remains open. This is a decomposition, not a
completed mathematical proof or net sorry progress.

The hole at the corrected
`AlgebraicGeometry.formalFunctions_degreeZero_compatibility`
(node `lem-weil-pbc-formal-functions-degree-zero-compatibility`) is replaced by
one hole added in
`AlgebraicGeometry.formalFunctions_degreeZero_augmentation_compatibility`
(node `lem-weil-pbc-formal-functions-degree-zero-augmentation-compatibility`).
The latter is the delivery's only direct `sorry`, a whole named theorem proof
with source and full argument in its docstring. Holes closed: one syntactic upper
hole after correction; holes added: one. Net hole reduction: zero.
`AlgebraicGeometry.formalFunctions_degreeZero_dictionary` was already proved
syntactically, and its adapted proof still rests on the remaining obligation;
it is not a newly closed hole.

## No longer needed

From the compatibility module remove the direct imports of
`Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroStalkIso`,
`Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroSystemIso`,
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties`, and
`Sheaf.Paper.HigherDirectImagePresheaf`. The formerly plain import of
`Sheaf.AlgebraicGeometry.FormalFibreCohomology` now supplies the public signature.
The new augmentation compatibility module is a plain proof import.

Every old compatibility proof dependency is superseded in that parent's route:
`def-weil-pbc-formal-fibre-cohomology` (remains a statement dependency),
`lem-weil-pbc-module-cohomology-fmap-basic-properties`,
`lem-weil-pbc-higher-direct-image-presheaf`,
`lem-weil-pbc-formal-functions-degree-zero-stalk-iso`, and
`lem-weil-pbc-formal-functions-degree-zero-system-iso`.
The first three are still needed in the new obligation's definitions or proof
plan; the parent uses the generic Mathlib degree-zero augmentation isomorphism
instead of extracting arbitrary witnesses from the last two.

The dictionary now directly uses only
`lem-weil-pbc-formal-functions-degree-zero-compatibility` in its proof record.
Its old direct proof dependencies are no longer direct uses there:
`def-pc-module-pullback`, `def-weil-pbc-formal-fibre-cohomology`,
`def-weil-pbc-module-stalk`, `lem-weil-pbc-higher-direct-image-presheaf`,
`lem-weil-pbc-left-exact-injective-resolution-degree-zero`,
`lem-weil-pbc-module-cohomology-fmap-basic-properties`, and
`lem-weil-pbc-module-pullback-structure-sheaf`.
Definitions remain statement dependencies and the other tools are used below.
The dictionary's original imports are retained because this unheld adaptation
must change only forced proof lines. No whole-library module pruning is claimed.
`dag/units/sk-thm-p1.json` and all its realized nodes are unchanged.

## Where the brief, the DAG or earlier work was wrong

The old compatibility statement cannot hold for arbitrary identifications:
for f = id on Spec Q and t = 1, negate the canonical system identification b.
This is still an inverse-system isomorphism, but changes the output from 1 to -1;
IsFormalFunctionsTheta does not constrain b. The jointly chosen identifications
repair is justified, and does not change the dictionary statement or targets.

The first worker's corrected compatibility was exactly the dictionary statement
left as `sorry`. Applying it from the dictionary was not a real proof reduction.
The second reading replaces that with a proved construction of the canonical
stalk equivalence, plus the smaller fixed-augmentation obligation. The original
stalk and system existence statements end in True and do not characterize their
arbitrary witnesses; they cannot justify compatibility for those witnesses.

The first worker's dictionary DAG proof text still described three old steps,
while its proof_deps listed only compatibility. Its change record did not give
old and new signatures verbatim. The compatibility statement_change also omitted
old_proof_deps after changing the proof dependencies. These are corrected.
The baseline DAG itself omitted compatibility from the dictionary proof_deps,
although the original Lean proof applied it; baseline DAG statement citers are
therefore empty, and the new dictionary record adds the actual edge.

The cited Stacks TeX files are not materialized on this read-only machine. I read
[Tag 01E4](https://stacks.math.columbia.edu/tag/01E4),
[Tag 01FB](https://stacks.math.columbia.edu/tag/01FB), and
[Tag 02OD](https://stacks.math.columbia.edu/tag/02OD) from the primary source.
The remaining obligation uses the degree-zero augmentation constructions of
01E4 and 01FB; it does not apply 02OD's completion theorem without properness or
Noetherian hypotheses.

The landing return identified that the preceding compatibility conclusion was
word for word the dictionary statement. Repaired by strengthening compatibility
in place with `a.toLinearMap =` the canonical stalk augmentation. The construction
proves this equality by reflexivity. It is mathematically substantive: it pins a
to the augmentation, whereas the dictionary merely asserts some equivalence.
The dictionary now extracts the witnesses and forgets that extra equality. Its
signature, visibility, imports and docstring remain unchanged. Importing the
dictionary back into compatibility would instead create an import cycle.
No further nodes or holes are added by this repair. The previous second reading
was removed because it reviewed the returned version; a new independent second
reading is required for this repaired version.

## Forced adaptations

`Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroDictionary`: the original proof
applies `formalFunctions_degreeZero_compatibility f y a b`, which over-applies the
new existential-valued theorem (function expected / type mismatch). Replace the
three proof lines extracting a and b and applying the old arbitrary-input
formula with `obtain ⟨a, _, b, hb⟩ := formalFunctions_degreeZero_compatibility f y`
and `exact ⟨a, b, hb⟩`.
Every signature and visibility is byte-for-byte identical, and its imports and
docstring remain untouched. deliver3.py appends the counterfactual compiler
output after checking that the original compiles on the baseline, fails against
the changed interface, and the adaptation compiles against the delivered set.

## New nodes

`lem-weil-pbc-formal-functions-degree-zero-augmentation-compatibility`, in
`Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroAugmentationCompatibility`,
is the remaining fibre-system identification and germ equation for the fixed
canonical augmentation map. Unlike its parent, it neither chooses nor asserts a
stalk equivalence. Its docstring explains the component construction, transition
naturality, resolutionSectionClass augmentation identity and cancellation of
restriction to the whole fibre. Empty fibres and the zero section give zero on
both sides; for f = id on Spec Q with t = 1 the fixed augmentation and canonical
system comparison give 1, with no arbitrary rescaling quantified. Search through
Lean Finder, Loogle, LeanSearch and grep found only generic germ/augmentation
results. LeanSearch returned Internal Server Error and is recorded unavailable.
The generic augmentation isomorphism found by Loogle is used in the parent.

Change record: `coord/changes/formalFunctions_degreeZero_compatibility.md`.


## Second reading by S2

1. Compared each delivered module against the repository. Existing declaration signatures are unchanged except for the declared compatibility interface repair and the forced dictionary proof adaptation; no target statement or definition changed accidentally. Verdict: pass.
2. Compiled all three modules with `lcompile.py --all`; they compile without errors. The parent and dictionary have no `sorry`; the augmentation theorem has exactly its named `sorry`, with no forbidden declarations or hollow definitions. Verdict: pass.
3. Checked the corrected compatibility statement and the augmentation statement against edge cases (identity on `Spec ℚ`, zero section, empty fibres) and searched Mathlib and `lean/` for existing results. The arbitrary-isomorphism formulation is false; the fixed-augmentation formulation is the needed strictly smaller obligation and is not duplicated. Verdict: pass.
4. The parent proof constructs the canonical stalk equivalence by bijectivity of the degree-zero augmentation and uses the augmentation theorem; imports removed from the parent are listed in `## No longer needed`. The unit route and realized nodes remain unchanged. Verdict: pass.
5. DAG statements, proof steps, proof dependencies, and proof origins match the Lean declarations; the new augmentation node records its source, proof, searches, and split status. Verdict: pass.

Changed during second reading: added this review record only; no Lean proof or interface changes were needed after compilation.

## Forced adaptations

### Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroDictionary
Original against changed dependencies failed:
```
/tmp/forced-adaptation-ex8hh258/lean/Sheaf/AlgebraicGeometry/FormalFunctionsDegreeZeroDictionary.lean:76:15: error: Function expected at
  formalFunctions_degreeZero_compatibility f y
but this term has type
  ∃ a,
    ↑a =
        ModuleCat.Hom.hom
          ((Y.toRingedSpace.moduleStalkFunctor y).map
            ((RingedSpace.moduleDirectImage
                    (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f))).toRightDerivedZero.app
              (SheafOfModules.unit X.ringCatSheaf))) ∧
      ∃ b,
        ∀ (n : ℕ)
          (θ :
            ↑(formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0) →ₗ[↑(Y.presheaf.stalk y)]
              ↑(formalFibreCohomologyLocal f y (SheafOfModules.unit X.ringCatSheaf) 0 n)),
          IsFormalFunctionsTheta f y (SheafOfModules.unit X.ringCatSheaf) 0 n θ →
            ∀ (V : Y.Opens) (hy : y ∈ V) (hV : ⊤ ≤ formalFibreι f y n ⁻¹ᵁ f ⁻¹ᵁ V) (t : ↑Γ(X, f ⁻¹ᵁ V)),
              (ConcreteCategory.hom (b.hom.app (op n)))
                  (θ
                    (a
                      ((ConcreteCategory.hom
                          (TopCat.Presheaf.germ
                            ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val.presheaf V y
                            hy))
                        t))) =
                (ConcreteCategory.hom (Scheme.Hom.appLE (formalFibreι f y n) (f ⁻¹ᵁ V) ⊤ hV)) t

Note: Expected a function because this term is being applied to the argument
  a

(with the modules compiled into /tmp/forced-adaptation-ex8hh258/.lbuild) [2.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
