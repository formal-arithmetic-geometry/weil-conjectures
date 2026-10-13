## What changed

Replaced the entire proof of `FormalGlueing.canonical_map_surjective` without changing
its signature or its public imports. The proof transports the actual prime and chart
components to canonical modules, recovers a unique value using the injectivity and
exactness in `RingTheory.formalGlueingComplexExact`, proves additivity and scalar
compatibility, and proves equality of the scalar-extension and localized components.
Tensor induction and the localization universal property finish the component equalities;
the given `hmap` and componentwise extensionality finish the categorical equality.

Added `Sheaf.RingTheory.FormalGlueingMorphismTuple` with the strictly smaller theorem
`FormalGlueing.canonical_tuple_compatible`. It asserts only that a morphism's value tuple
lies in the kernel of the displayed glueing differential. It has neither flatness nor
quotient hypotheses and asserts no preimage, linear lifting, functor or surjectivity.
Its remaining proof consists of transporting the compatibility equations and identifying
the iterated-localization overlaps with the product localization.

Added private, proved helpers `transport_prime`, `canonical_piece_eq`, `transport_chart`
and `components_ext` to the target module. All data in the proof is constructed explicitly
or selected from a uniquely characterized preimage. No definition, existing statement,
universe, visibility or target changed. Both delivered modules compile cleanly together
through `lcompile.py --all`, in about eight seconds combined.

## Proved and sorry left

Closed the original hole in `FormalGlueing.canonical_map_surjective`
(node `lem-weil-pbc-formal-glueing-morphism-lifting`): no sorry remains in the item's module.

Added one hole: `FormalGlueing.canonical_tuple_compatible`
(node `lem-weil-pbc-formal-glueing-morphism-tuple`), in the new module
`Sheaf.RingTheory.FormalGlueingMorphismTuple`. Its whole proof is `by sorry`, with source
and complete proof in words in its docstring and node.

This is a decomposition: one upper hole closed, one lower hole added, net zero.
The extraction of unique preimages from exactness, the linearity proof and the proof
that the lifted map recovers all morphism components are complete Lean proofs.
The new kernel statement is valid for arbitrary ring maps. For t=0 its differential
has only empty families and is zero; zero denominators and zero modules require no
cancellation. The parent still uses exactly its original flatness and quotient hypotheses
for preimage existence and uniqueness.

## No longer needed

Removed the direct proof import `Sheaf.Paper.FormalGlueingCanonicalMaps` from the item's
module. The old proof dependency `lem-weil-pbc-formal-glueing-canonical-maps` is no
longer used directly by the parent. Its comparison and swap facts remain planned dependencies of the new
compatible-tuple node; they are not mathematically pruned. The exact-complex proof import
remains and is used. Added only the proof import of the new tuple module.

No original node or module is globally pruned. All steps of the original argument remain:
the compatibility calculation is isolated, and exactness, linearity and recovery are
implemented in Lean. The unit's statement and its realized proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error or disputed statement was found. Canonical charts restricted from
R_f carry an R-action equal to the original localized R-action, but the module instances
are not definitionally equal. `canonical_piece_eq` proves the required equality using
`Module.ext'` and `algebraMap_smul`; the component transports use this equality explicitly.

LeanSearch returned Internal Server Error. LeanFinder, Loogle and source grep supplied
usable searches; none provided the whole lifting or tuple-compatibility statement.
The referenced local Stacks TeX is absent on this machine. Read the primary-source pages
[05EK](https://stacks.math.columbia.edu/tag/05EK),
[05EM](https://stacks.math.columbia.edu/tag/05EM) and
[05EL](https://stacks.math.columbia.edu/tag/05EL) directly instead. The new node records
these locations and the implicit compatibility argument written out by C4.

## New nodes

`lem-weil-pbc-formal-glueing-morphism-tuple`, recorded in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-formal-glueing-morphism-tuple.json`,
with Lean declaration `FormalGlueing.canonical_tuple_compatible` in
`lean/Sheaf/RingTheory/FormalGlueingMorphismTuple.lean`. It isolates the prime and overlap
kernel calculation of the original node's steps 2–3. Its statement has no existence
claim and is strictly part of the lifting argument. The parent node's proof,
proof dependencies and proof origin now describe the implemented reduction.
No change record is needed: there is no existing interface change or forced adaptation.

## Second reading by C4

1. **Interfaces: pass.** Compared the delivered lifting module with the repository using
   `diff -u`: its existing theorem signature, universes, docstring and public imports
   are byte for byte unchanged. The only Lean changes are four private proved helpers,
   the target proof and proof imports. There are no definition or statement adaptations.
   The new tuple module adds one theorem, with no existing declaration changed.
2. **Proof and axioms: pass as a decomposition.** Both modules compile together through
   `lcompile.py --all` without errors or warnings. Scratch copies with `#print axioms`
   checked all four helpers and both public theorems. Helpers use only `propext`,
   `Classical.choice`, `Quot.sound`; the public theorems additionally use `sorryAx`,
   as expected from the open compatible-tuple theorem and upstream open dependencies.
   There is precisely one syntactic `sorry` in this delivery, the named tuple theorem;
   there are no forbidden declarations or holed definitions. Transport witnesses are
   constructed by equality elimination. The only selected module element is the
   preimage proved unique by exactness and injectivity, so it is not arbitrary data.
3. **Split statement: pass.** Read the full signature, docstring and node against
   [Stacks 05EL](https://stacks.math.columbia.edu/tag/05EL) and
   [05EK](https://stacks.math.columbia.edu/tag/05EK). The theorem asserts only kernel
   membership, without preimage existence, flatness or quotient hypotheses, so it is
   strictly part of lifting rather than a renamed lifting theorem. The prime equation
   follows from morphism compatibility and comparison injectivity (also directly from
   the given alpha equivalence); the overlap equation follows from chart compatibility
   and clearing two denominators. Independently checked the common numerator
   `f_i^b f_j^a (f_j^b x - f_i^a y)` over `(f_i*f_j)^(a+b)` and that the annihilating
   product power contains both clearing powers. No cancellation in N is used.
   Checked t=0, t=1, f_i=0, f_i=1, i=j and M or N zero: empty families, zero
   localizations and identity localizations satisfy the same argument.
   Fresh LeanFinder search used commuting descent maps and the Cech differential;
   Loogle search `IsLocalizedModule.map, LinearMap.comp` returned map composition and
   naturality tools, not this statement. Source searches of both library roots found
   formal-glueing H0, canonical maps and other tuple results, but none with this
   morphism-induced kernel assertion. Completing the remaining transport and overlap
   formalization is substantial; no quick closure or shorter existing theorem was found.
4. **Route and pruning: pass.** Read the exact-complex statement and canonical-map
   declarations, and checked `dag/units/sk-thm-p1.json` including `realized`. The
   reduction keeps exactness, compatibility, unique recovery, linearity and component
   recovery; no unit statement or realized step is bypassed or changed. Public imports
   supply the signatures; the two parent proof imports supply the actual proof.
   The tuple's CoverModuleExact import is public because its unit-invertibility theorem
   occurs inside the displayed rho in the signature. The removed canonical-maps
   dependency is explicitly named above; it remains a planned tuple dependency, and
   no globally pruned module is claimed. This is one hole closed and one added, net zero.
5. **DAG: pass after metadata repair.** Only `proof`, `proof_deps`, `proof_origin`
   differ in the existing parent node, and they describe the Lean proof. The new node
   includes source, complete proof, searches, provenance, blueprint ancestry, chapter,
   unit and Lean record; its proof dependency set equals the union of the step uses.
   Replaced the new node's flattened `lean.statement` with the exact multiline Lean
   signature, as required by the brief. No mathematical statement changed.

Second-reading changes: repaired the new node's verbatim signature metadata, explicitly
named the old dependency no longer used directly, and appended this audit. No Lean proof
or statement needed repair. The reported count remains one original hole closed and one
strictly smaller hole split off, a decomposition rather than an axiom-free proof.
