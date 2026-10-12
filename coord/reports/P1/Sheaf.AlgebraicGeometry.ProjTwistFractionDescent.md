## What changed

Replaced the sole sorry in `AlgebraicGeometry.Proj.twist_fraction_descent` by a
complete Lean composition. The target signature and original public imports are unchanged.
Three proof imports were added: `ProjTwistFiniteLocalizationData`,
`CoverModuleExact`, and `ProjTwistDegreeDetection`.

The target proof obtains finite compatible localization data, applies the existing,
proved `RingTheory.coverModuleExact` over A_(f) to A_f, and uses the local evaluation
maps' normalization to recover the section's pointwise values. It then rewrites those
values and applies degree detection using their subtype proofs. No intermediate module
is introduced merely to package the gluing application.

Three delivered modules compile in dependency order. No existing definition, statement,
visibility, instance, or target signature changed. No forced adaptations were needed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Proj.twist_fraction_descent`
(node `lem-sc-proj-twist-fraction-descent`).

Added exactly two holes, each a public theorem with its whole proof `:= by sorry`:

- `AlgebraicGeometry.Proj.twist_finiteLocalization_data`
  (`lem-sc-proj-twist-finite-localization-data`): extract finite compatible ordinary module
  fractions and their local evaluation maps from the section's local fraction witnesses.
- `AlgebraicGeometry.Proj.twist_degree_detection`
  (`lem-sc-proj-twist-degree-detection`): detect the degree of a fixed ordinary fraction
  from membership of its prime-localized values in the degree-k parts. It has no section
  parameter and no global gluing conclusion.

There are no sorries left in the item's module. This is
an explicit decomposition, not an unconditional proof: one existing hole closed and two
new holes added, net -1 before any independent closure pruning. The finite module gluing
step itself is proved from an existing proved theorem, rather than left as another hole.

Edge cases checked mathematically: nilpotent f has empty basic open and zero localizations;
the finite-data statement allows n=0 and top=bottom in the zero chart ring. Negative k
requires no nonnegative shift assumption: a sufficiently large power of positive-degree f
provides a denominator degree for zero, and any surviving nonzero component has numerator
degree k+r*b already nonnegative. For a standard polynomial grading with f a variable,
local chart elements are the usual degree-zero ratios and the conclusions recover the
ordinary Laurent fraction of the section. None of these tests requires A to be reduced,
noetherian, generated in degree one, or a domain.

## No longer needed

No imports or modules are pruned. The old proof_deps entries
`def-weil-pbc-proj-twisting-sheaf` and `def-sc-degree-zero-module-fractions` are no longer
proof steps of the composition, but remain necessary statement dependencies and their
public imports stay. The new proof route
uses finite module gluing and degree detection, and imports only the modules it uses.
No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof step described the entire global argument but named only the two
definitions. It did not supply a theorem for finite compatible chart-data extraction or
homogeneous-degree detection. The new nodes make those two remaining parts explicit.
The existing `CoverModuleExact` module already proves the partition-of-unity gluing step
and is reused. The original node's proof, proof_deps, and proof_origin now match the Lean
composition. The inherited unit has empty realized bindings; this delivery does not
change them or its route.

LeanSearch returned Internal Server Error for the required searches; these attempts are
recorded as unavailable. LeanFinder, Loogle, and source searches found the homogeneous
fraction constructors, homogeneous-core prime theorem, and affine-Spec local-fraction
lemmas, but no theorem directly supplying these Proj twist interfaces.

## New nodes

`lem-sc-proj-twist-finite-localization-data` records the remaining local geometric step.
Its conclusion is compatible local data on a finite cover, with normalized evaluation
maps; it does not assert a global fraction. Its proof in words refines local homogeneous
fractions, uses the affine chart and quasi-compactness, and detects equality on overlaps.

`lem-sc-proj-twist-degree-detection` records the remaining algebraic step for a fixed
ordinary fraction. Its proof in words decomposes a numerator into homogeneous components,
uses injectivity of homogeneous localization into ordinary prime localization and
homogeneous annihilator detection, then retains just the required component.

Both new nodes inherit the item's chapter, unit, and blueprint ancestry. Each has a
Lean record and three kinds of search. There are no change records because no existing
interface or statement was changed.

## Second reading by P1

1. Compared the existing module with the repository using a textual diff. The entire
   existing declaration signature, docstring, visibility, and both public imports are
   unchanged. Only three private proof imports and the proof body differ. The two other
   modules and their nodes are new; no definitions, instances, or change records appear.
2. Compiled all three modules in dependency order with lcompile.py. A scratch axiom probe
   reports only propext, Classical.choice, Quot.sound and sorryAx for the three twist
   declarations, and only the permitted three for coverModuleExact. The only delivered
   sorry occurrences are the two reported named public theorems. No forbidden declarations
   or hollow definitions occur. The composed proof uses local witnesses only in a theorem;
   no arbitrary witness is installed as data in a definition.
3. Read both split statements against their complete types and the source's chart and
   shift constructions. Finite compatible data omit global gluing; degree detection has
   a fixed fraction and no section or gluing conclusion. Both are true, strictly separate
   parts of the argument, and used by the composition. Checked the zero ring, nilpotent f,
   negative k, and a polynomial grading with f of degree greater than one. Independent
   LeanFinder, Loogle, and grep searches (recorded in searches.jsonl) found chart ideal
   descriptions and localized-module equality tests, but no direct theorem closing either
   interface. Neither split is merely the original descent conclusion renamed.
4. Read the composition from its conclusion down through coverModuleExact, including the
   module action and both equalities under each evaluation map. No shorter proved route
   was found. All added imports are needed and private; public imports serve signatures.
   The old proof dependencies are explicitly accounted for above. The unit's realized
   statement and step arrays are already empty; this decomposition changes no unit route.
5. Compared the existing node diff: only proof, proof_deps, and proof_origin changed.
   These name exactly finite data, coverModuleExact, and degree detection. Read both new
   nodes, their Lean signatures, sources, searches, ancestry and creation records; they
   match their modules. Their planned proof texts agree with the repaired docstrings.

Changed only the new split lemmas' natural-language proofs and matching node proof texts:
clarified how basic neighborhoods refine local witnesses, distinguished homogeneous
h_i in A from chart u_i in A_(f), and expanded the injectivity and f-saturated annihilator
argument in degree detection. Clarified the old proof dependencies in No longer needed.
No Lean statement or executable proof changed. This remains a decomposition: one original
hole closed, two holes added, net -1; neither split could be closed in a brief proof.
