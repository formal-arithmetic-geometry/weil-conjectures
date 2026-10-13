## What changed

Closed the original hole in `AlgebraicGeometry.exists_affine_hom_comparison_maps`
without changing its signature or its two public imports. The assembly chooses
the generator-normalized comparison and combines its two naturality equations
and rank-one invertibility. All additions are in four new modules.

Repaired the earlier sandbox's timeout: `affineHomComparisonFunctor` is now a
named definition with the proved equation `affineHomComparisonFunctor_eq`.
The assembly rewrites by this equation before applying the three component
lemmas. It avoids the earlier unrestricted `dsimp` and the expensive kernel
comparison of expanded functor-map expressions. No compiler limit was raised,
no existing library definition was changed, and no file was split to avoid a
limit. The four new modules already belonged to the mathematical decomposition
in the earlier sandbox.

Proved both naturality lemmas and rank-one invertibility rather than retaining
those three holes. Proved the supporting generator normalization, generator
functoriality, generator detection, and internal-Hom section composition API.
Generator detection uses the chart functor's left adjunction; adjoint linear
maps are detected by composing with the maps that send one to each element.
Rank-one invertibility uses the concrete module evaluation equivalence and the
proved upstream internal-Hom unit evaluation isomorphism.

Verification: all five delivered modules compile without warnings; the
construction module takes about 13 seconds, the property modules 5–10 seconds,
and the assembly about four seconds. The delivery tool also completed its
axiom probes. Its first preflight found missing metadata in the earlier
sandbox nodes, now repaired.

The comparison definition chooses only the unique map specified by the remaining
normalization theorem. Its statement determines that map up to equality; no
arbitrary existence witness or hollow data definition was introduced.

## Proved and sorry left

Original hole closed:

- `AlgebraicGeometry.exists_affine_hom_comparison_maps`
  (`lem-sc-k3-affine-hom-comparison-maps`).

The following new component statements have complete Lean proofs:

- `AlgebraicGeometry.affineHomComparison_chart_left`
  (`lem-sc-k4-affine-hom-comparison-left`).
- `AlgebraicGeometry.affineHomComparison_chart_right`
  (`lem-sc-k4-affine-hom-comparison-right`).
- `AlgebraicGeometry.affineHomComparison_chart_rankone`
  (`lem-sc-k4-affine-hom-comparison-rankone`).

Exactly one new hole remains:

- `AlgebraicGeometry.existsUnique_affineHom_generator_extension`
  in `Sheaf.AlgebraicGeometry.AffineHomComparisonGeneratorExtension`
  (`lem-sc-k4-affine-hom-generator-extension`). Its proof is exactly `by sorry`.
  Its docstring specifies the linear assignment into global internal-Hom
  sections, the adjunction construction, normalization, uniqueness, and
  transport along the chart isomorphism. It asserts neither naturality nor
  rank-one invertibility, which are proved separately.

This is a decomposition: one original hole closed and one lower hole added,
net zero against the original import-closure baseline. Compared with the
previous sandbox, three of the four proposed lower holes have been removed.
The resulting theorem still depends on the construction hole; no claim of
sorry-free axioms is made.

## No longer needed

No existing node or library module is pruned. The old direct proof dependencies
`def-pur-sheaf-hom` and `lem-weil-pbc-spec-module-tilde-sections` remain used
through the construction and property nodes; the new DAG replaces their direct
edges with the actual component edges. Both original public imports are
needed for the statement. Removed the redundant direct proof import of
`Sheaf.AlgebraicGeometry.AffineHomComparisonGeneratorExtension` from the item:
the three property modules expose its interface. Removed the redundant direct
public imports of InternalHom and Mathlib Tilde from the three new property
modules, since their public construction-module import provides them.

The experimental scratchpad module is not delivered. No general assertion that
Hom commutes with localization, finite-presentation hypothesis, or
quasi-coherence hypothesis on internal Hom is needed. The unit record has no
realized nodes for this item; its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous timeout was not a tool failure. A named functor equation fixes the
expensive unfolding and kernel comparison while preserving the explicit functor
in the original theorem's statement. The earlier generic naturality and rank-one
arguments can be specialized successfully with explicit sheaf-ring parameters;
their three remaining holes were unnecessary.

The original DAG named tilde and internal Hom but did not state the actual
comparison construction. The new construction node supplies precisely this
missing part. The mapping property in Stacks Tag 01I7 applies to an arbitrary
target sheaf, which matters because internal Hom need not be quasi-coherent.
Read Tags 01I7 and 01HV directly and the pinned Mathlib tilde adjunction and
upstream InternalHom, InternalHomUnit, InternalHomFree, AffineHom and
HomObjSections modules. Searches found the ingredients rather than an existing
normalized comparison theorem.

Checked zero rings, zero modules, and arbitrary non-finitely-presented source
modules: the remaining construction uses the unrestricted tilde adjunction,
and the completed proofs use adjunction detection and evaluation at one,
without nontriviality, finiteness, or coefficient restrictions. No false
statement or forced adaptation of an existing module was found.

## New nodes

`lem-sc-k4-affine-hom-generator-extension` isolates the unique comparison
normalized on all global generators. This is the only remaining hole.

`lem-sc-k4-affine-hom-comparison-left` records the proved contravariant
naturality equation, derived by precomposing with all generators.

`lem-sc-k4-affine-hom-comparison-right` records the proved covariant naturality
equation, derived by the same generator detection argument.

`lem-sc-k4-affine-hom-comparison-rankone` records the proved evaluation-at-one
argument showing that the normalized comparison is invertible for source A.

Updated the item's existing proof route and the new nodes' proof dependencies,
Lean signatures and actual search records. There is no change record: existing
statements, definitions and visibility are unchanged.


## Second reading by K4

1. Interface preservation: compared every delivered module with the repository.
   Only AffineHomComparisonMaps already exists; its theorem signature is byte
   for byte identical, and its original public imports and visibility remain.
   The other four modules are new. No definition, existing statement, target,
   or module held by another group is adapted. Verdict: pass.
2. Proof and axioms: compiled all five modules locally in import order with
   lcompile.py, without errors or warnings (about 7–17 seconds per component,
   4.5 seconds for the assembly). Inspected all definitions and proofs and
   scanned for forbidden declarations and attributes. Exactly one literal
   sorry occurs, in existsUnique_affineHom_generator_extension. Compiled scratch
   copies with #print axioms for every public declaration. Only propext,
   Classical.choice and Quot.sound occur, plus sorryAx for that construction,
   the chosen comparison, its normalization, the three properties and assembly.
   Generator detection and section composition are independently sorry-free.
   The chosen datum is specified uniquely up to equality by the remaining
   theorem, so it satisfies the permitted unique-existence rule. Verdict: pass
   as a decomposition, not a sorry-free proof or positive net hole reduction.
3. Split statement: read the generator-extension theorem, its full proof
   docstring and node against Stacks Tags 01I7 and 01HV. The arbitrary-target
   mapping property supplies the construction from the linear assignment
   h to T(h); the explicit rank-one identification gives the stated generators.
   Uniqueness also follows from the proved affineHomGenerator_ext. The theorem
   contains neither naturality nor rank-one invertibility and is strictly the
   construction part, not a renamed copy of the original conjunction. Checked
   zero ring, M=0, N=0, M=A, and arbitrary non-finitely-presented M: localization
   and the unrestricted adjunction need no extra hypotheses. Independent
   msearch searches used “extend linear map to global sections through
   associated module sheaf adjunction” (leanfinder), tilde.adjunction (loogle),
   and Hom/comparison variants (grep). Repository searches and direct reading
   of AffineHom and HomObjSections found ingredients, not this normalization
   theorem; AffineHom's existence lemma requires a quasi-coherent target.
   Closing the remaining hole requires formal scalar-linearity and chart
   transport calculations, beyond a short review repair. Verdict: pass.
4. Route and pruning: read each proof from the assembly down. Naturality uses
   normalization, generator functoriality and the proved section-composition
   formula; invertibility compares the map with module evaluation at one via
   the proved internal-Hom unit isomorphism. Each import supports a signature
   or an actual proof; InternalHomFree is correctly a plain proof import.
   No old dependency is abandoned: both remain used transitively, now stated
   explicitly under No longer needed. Read the unit's realized record: its
   statement and step arrays are empty, and this delivery alters neither the
   unit nor its route. Verdict: pass; no library modules pruned.
5. DAG agreement: inspected all five nodes, the actual Lean signatures and
   their proof steps. Every proof_deps set equals the union of step uses;
   the construction, adjunction, internal Hom and evaluation dependencies
   reflect the code. All four new nodes have the required source, origin,
   searches, creation, blueprint, chapter, unit and Lean records. The existing
   node changes only its proof, proof_deps and proof_origin after restoring
   its original Lean metadata. Verdict: pass.

Second-reading changes: restored the existing node's original verbatim Lean
signature metadata, removed one accidental blank line in the original module,
clarified the retained old dependencies in No longer needed, and added this
review. No mathematical proof or statement needed repair. Scratch axiom copies
were removed before delivery. One original hole is closed and one strictly
lower construction hole is added; the net is zero.
