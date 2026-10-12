## What changed

Replaced the sorry proof of
`AlgebraicGeometry.Scheme.Modules.exists_cechBaseChange_iso` with a complete Lean
assembly of degreewise isomorphisms into a chain map. The proof chooses the component
isomorphisms, applies their differential compatibility, constructs the chain map with
`CochainComplex.ofHom`, identifies its coordinate formula with `IsCechBaseChange`, and
uses `HomologicalComplex.Hom.isIso_of_components` to prove invertibility.

Added two proof-only imports and two separate modules:
`Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechTerms` and
`Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechDifferential`.
They inline the existing constructions in their signatures, so neither imports the
item module and no cycle is introduced. No existing signature or definition changes.
The inclusion parameter is supplied by the item's already proved
`baseChangeCover_intersection_le`; it is not an added hypothesis of the item.

Read Stacks Tags 02KH and 02KG online, the item's full DAG proof and dependencies,
the affine-section theorem and its proof, the Cech coordinate/differential API, and
the unit record `sk-thm-picard-rr` (its realized lists are empty). The source route is
kept: affine sections, finite products, restriction naturality, chain isomorphism.
Library searches found no direct replacement. LeanSearch returned HTTP 500 and is
recorded as unavailable, not as no match. LeanFinder and Mathlib grep ran; direct
repository searches also found no theorem with the required scalar coordinate formula.

All three modules compile locally without warnings using lcompile.py. The new
statements were checked on empty index families, empty intersections, degree zero,
the zero module and the zero algebra. The term theorem requires a finite index family
but not a covering; the differential theorem does not require finiteness, affineness,
quasi-coherence, flatness or invertibility. A tuple has k+1 entries, so affineness of
an intersection never requires affineness of the empty intersection of no opens.

## Proved and sorry left

The original module's one sorry is removed:
`AlgebraicGeometry.Scheme.Modules.exists_cechBaseChange_iso`
(node `lem-pc-flat-cech-base-change`) is proved from the two named smaller statements.
This is a reduction, not a claim that its transitive axiom closure is sorry-free.

Exactly two new public theorem sorries remain, each with a complete proof in words:

- `AlgebraicGeometry.Scheme.Modules.exists_cechBaseChange_term_isos`
  in FlatCohomologyCechTerms, node `lem-pc-flat-cech-base-change-terms`.
  This gives individual degree isomorphisms and coordinates, with no differential
  compatibility or chain map.
- `AlgebraicGeometry.Scheme.Modules.cechBaseChange_components_comm`
  in FlatCohomologyCechDifferential, node
  `lem-pc-flat-cech-base-change-differential`.
  This proves differential compatibility conditional on a family of canonical maps;
  it asserts neither existence nor invertibility of those maps.

## No longer needed

Removed the original proof-only import
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections` from the item: the assembly
does not invoke its declarations. No original public import was removed; they
support the existing definitions and signatures. No original node is declared
globally unnecessary: the new term node retains the affine-section route in its
proof plan, even though its unproved statement needs no import of that proof tool.
The main node no longer directly uses `lem-weil-pbc-separated-affine-open-intersection`,
`lem-weil-pbc-module-pullback-affine-sections`,
`lem-weil-pbc-conjugate-iso-unit-equation`, or
`def-pc-flat-cohomology-comparison` as proof dependencies: those are needed by the
new term or differential nodes and remain in the transitive route. None is falsely
reported as globally unnecessary. The final assembly uses the cochain-complex node
and the two new nodes only. No new module imports an unused proof module.

## Where the brief, the DAG or earlier work was wrong

The old DAG's second step called all of finite-product tensor comparison and
restriction/differential compatibility elementary. Although the mathematical
argument is valid, the current Lean APIs do not provide that whole step as a single
application. The split makes its two logically independent obligations explicit.
The existing affine-section theorem uses tensorPullback and tensors over the local
affine section ring; the term proof still needs unit-compatible transport to the
library pullback and the cartesian-ring tensor associativity calculation.

The generic affine-section result from the proper-base-change unit is retained as
a tool below the term node, as in the original DAG; it is not bypassed. Its module
was inspected, but is not imported by the main assembly merely to appear in the
import graph. No statement is believed false, and no statement correction is made.

A dependency-closure audit found an existing DAG cycle:
`lem-weil-pbc-sheaf-algebraic-structures-objects` ->
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component` ->
`lem-weil-pbc-sheaf-algebraic-structures-objects`.
The identical cycle is reached from the original item on the unchanged repository;
neither cycle node is changed here. All dependencies of the three delivered node
records exist. This inherited metadata issue is reported for the maintainer.

The delivery dry run returned OK: local and server compilation and preflight
passed except for the deliberately absent second-reading section, which belongs
to the second worker. Nothing was pushed.

## New nodes

`lem-pc-flat-cech-base-change-terms` records the canonical degree isomorphisms,
with the finite-product construction and affine-section transport in its proof.
Its module is `lean/Sheaf/AlgebraicGeometry/Cohomology/FlatCohomologyCechTerms.lean`.

`lem-pc-flat-cech-base-change-differential` records naturality with the differential
for arbitrary canonical component maps. Its proof expands the alternating
restriction sum, uses unit and structure-sheaf naturality, and closes by tensor
induction and coordinate injectivity. Its module is
`lean/Sheaf/AlgebraicGeometry/Cohomology/FlatCohomologyCechDifferential.lean`.

Both inherit the original chapter and unit. Their statements are strictly parts
of the original argument, have the source citation and blueprint ancestry, and
record three actual search kinds. The original node's proof and proof_deps now
match the Lean assembly. No change record is needed: existing public interfaces
are unchanged and the two imports added to the item are proof-only.

## Second reading by F2

1. Compared the complete item module with the read-only repository using `diff -u`.
   All existing declaration signatures, definitions and docstrings are byte for
   byte unchanged. Only the final theorem proof and proof-only imports differ.
   The two new modules introduce only their advertised theorems; no change record
   is necessary. Verdict: pass.
2. Independently compiled all three modules with `lcompile.py --all`: no errors or
   warnings. A scratch module printed axioms of all ten delivered declarations:
   the seven existing definitions/elementary declarations use only `propext`,
   `Classical.choice`, and `Quot.sound`; the main theorem and two new lemmas also
   use `sorryAx`, exactly as expected for this reduction. The only textual sorries
   are the whole proofs of the two reported public theorems. No forbidden
   declarations or hollow definitions occur. Verdict: pass as a partial proof,
   not a sorry-free transitive proof.
3. Read both new signatures and complete docstring arguments against Stacks
   02KH and 02KG. The term result asserts degreewise invertibility and the
   canonical formula only; the differential result assumes the formula and
   asserts compatibility only. Neither restates the chain-isomorphism theorem.
   The supplied inclusion hI is automatic, unique as a map of opens, and the main
   proof supplies it without adding a hypothesis. Checked mathematically the
   empty index family (all terms zero), singleton family, degree zero (two signed
   restrictions), empty tuple intersections, zero module, and zero algebra.
   Every tuple is nonempty. Finiteness is needed only for tensor commuting with
   products; no flatness is needed before taking cohomology. Verdict: true and
   appropriately split.
   Repeated searches with different wording using msearch LeanFinder and Loogle,
   and rg over Mathlib tensor products, upstream and lean/Sheaf. The search for
   section-module maps commuting with alternating faces found
   `AlgebraicTopology.AlternatingCofaceMapComplex.map`; this requires an existing
   cosimplicial morphism and does not supply the scalar-extension and geometric
   restriction calculation. `cechComplexFunctor_map_f_π` and
   `cechComplexFunctorIso_hom_naturality` concern a fixed cover and base ring.
   `cechδ_naturality` concerns connecting maps, not this differential.
   The affine-limit results returned for finite-product scalar extension do not
   state the needed section formula. No duplicate or immediate replacement was
   found. Neither remaining proof closes by a few-minute application of these
   APIs: geometric scalar transport and restriction calculations remain.
4. Read the assembly from its conclusion downward: `isIso_of_components`,
   `CochainComplex.ofHom`, differential compatibility, and degreewise isomorphisms.
   This uses the standard shortest assembly and preserves the original route
   through affine sections and finite products. Inspected every import: new
   modules import the API their signatures mention; the new item imports are
   proof-only. All four old proof dependencies absent from the new direct proof
   are listed under No longer needed, with their retained transitive roles.
   The unit sk-thm-picard-rr has empty realized statement and step lists, so this
   reduction bypasses no recorded unit realization. Verdict: pass.
5. Compared the old node JSON with the delivered record: only proof,
   proof_deps and proof_origin change. Their steps agree with the Lean assembly.
   Both new nodes name their actual module and declaration, state the exact
   coordinate assertions, have source/ancestry/search/creation records, and
   retain the item's chapter and unit. Every statement/proof dependency resolves
   to a repository or delivered node. Verdict: pass; the inherited cycle noted
   above is outside this delivery.

Second reading changed the report's pruning account: it now explicitly records
removal of the proof-only ModulePullbackAffineSections import, while distinguishing
that import removal from the retained affine-section dependency in the term
node's proof plan. No Lean proof, signature, definition, or DAG record needed
repair. Added this independent review and scratch axiom verification.
