## What changed

Proved `CategoryTheory.stacksGalois_functorToContAction_isEquivalence` with its
signature unchanged. The proof constructs Mathlib's `PreGaloisCategory`,
`FiberFunctor F`, and `GaloisCategory` instances from the Stacks hypothesis and
then uses Mathlib's equivalence theorem, tagged 0BN4. Exactness and conservativity
transfer through `FintypeCat.incl`; the existing Stacks axioms lemma supplies
preservation of epimorphisms. Finite group quotient shapes are shrunk to universe
zero before applying finite-colimit existence and preservation. `uSwitch` supplies
the fibre functor in the hom universe required by `GaloisCategory`, without
restricting any universe of the original theorem.

Added and proved `CategoryTheory.stacksGalois_mono_complement` in
`Sheaf.CategoryTheory.Galois.StacksMonoComplement`. Pullbacks along connected
components classify which components meet a mono. Their complementary coproduct
has an injective fibre map with complementary range. The Type binary coproduct
criterion and reflection of finite colimits give the required summand cofan.
The proof handles empty component families, the initial source, and an iso by
allowing an empty complementary coproduct.

The new module is imported only for the proof. Updated both DAG proofs to match
these Lean arguments. No existing statement, definition, public import, or target
signature was changed. The unit record `sk-prop-h2` has no realized statement or
proof step assigned to this node, and its Kummer route is unaffected.

## Proved and sorry left

Proved `CategoryTheory.stacksGalois_functorToContAction_isEquivalence`
(node `thm-galois-abstract-equivalence`): the item's only sorry is closed.
Also proved `CategoryTheory.stacksGalois_mono_complement`
(node `lem-galois-stacks-mono-complement`). No sorry remains in either delivered
module; none was split off.

The proofs use the existing public theorem
`CategoryTheory.stacksGaloisCategory_axioms` (node `lem-galois-axioms`), which still
contains sorry in the library and is not changed by this delivery. Thus this is
a complete stage-3 reduction to an existing stated dependency, not yet a proof
with only the three standard axioms throughout its transitive closure.

Both modules compile together locally without warnings. The delivery dry run
performs the final compilation and preflight checks.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.Galois.AutProfinite`,
`Sheaf.CategoryTheory.Galois.GaloisTransitive`, and
`Sheaf.CategoryTheory.Galois.StacksGaloisObjectExists`. The new route does not use
nodes `lem-galois-aut-profinite`, `lem-galois-action-continuous`,
`lem-galois-transitive`, or `lem-galois-object-exists` as Sheaf dependencies of
this theorem. Their associated custom topology, inverse-limit transitivity,
and Galois-object constructions are supplied internally by Mathlib's theorem
under the derived SGA1 hypotheses. They may still be needed by other targets;
this delivery only removes this theorem's edges to them. The definition node
`def-galois-category` and the axioms node `lem-galois-axioms` remain needed.
No imported module is unused in either delivered file.

## Where the brief, the DAG or earlier work was wrong

The original 12-step proof is not false. Its recorded Mathlib candidate correctly
identified the missing comparison with SGA1. That comparison now has a Lean
proof: the only substantial extra lemma, the summand axiom, is proved too.
The original declaration's docstring is preserved; the updated DAG records the
shorter implementation route.

LeanSearch was unavailable (Internal Server Error) on both queries; this is
recorded as unavailable, without an absence verdict. LeanFinder, Loogle,
Mathlib-source grep, and a DAG/blueprint search were used instead.

WANTED: `literature/stacks-project/pione.tex`, Definition 0BMY, Lemma 0BN0,
and Proposition 0BN4, for checking the written source argument against the
original text; the read-only checkout contains literature indexes only. The
new proof is recorded with `proof_origin.by = agent`, deriving the assertion
from the existing definitions and theorem signatures. No source was downloaded.

## New nodes

`lem-galois-stacks-mono-complement`:
`dag/nodes/sec-curve-estimates/lem-galois-stacks-mono-complement.json`, realized by
`lean/Sheaf/CategoryTheory/Galois/StacksMonoComplement.lean`, declaration
`CategoryTheory.stacksGalois_mono_complement`. This is the SGA1 summand axiom,
a strict part of the Stacks-to-Mathlib comparison, and is proved rather than
left sorry. It depends only on `def-galois-category` and `lem-galois-axioms`.
There are no change records because existing public interfaces are unchanged.


## Second reading by M2

1. **Interfaces: PASS.** Compared the entire existing module against the repository
   with `diff -u`. The sole existing theorem's signature is byte for byte unchanged,
   as are the existing docstring, namespace, universes, and public imports. Only its
   proof and private proof imports differ. The complementary-summand theorem is a
   new declaration in its own new module. No definition or target changed, and no
   change record is required.
2. **Proofs and axioms: PASS as a reduction to an open dependency.** Independently
   compiled both modules together with `lcompile.py --all`: no errors or warnings
   (2.4 s and 1.9 s). Read every proof, including the finite-group universe shrink,
   the `uSwitch` fibre functor, pullback identification, complementary ranges, and
   reflection of the binary colimit. No delivered file contains `sorry`, an axiom,
   `unsafe`, `opaque`, `implemented_by`, or `extern`. Scratch-copy `#print axioms`
   checks of both declarations returned exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The last is the acknowledged existing theorem
   `stacksGaloisCategory_axioms`, not a new admission in this delivery. Removed the
   scratch copies after checking.
3. **New statements: PASS.** There are zero split-off open statements. The proved
   complement theorem is strictly the summand-axiom part of the comparison, not
   a restatement of the equivalence. Its source, complete prose proof, and new node
   are present. Checked empty target decomposition, initial source, identity/iso,
   and a proper subset inclusion of finite sets: the selected components give the
   expected complements, including an empty complementary coproduct. Independently
   searched LeanFinder for reflection of a coproduct with complementary fibre
   images, Loogle for the summand axiom, and the library/Mathlib sources for summands
   and complements. Reflection lemmas assist the last step; the Mathlib summand
   field already assumes `PreGaloisCategory`, and its finite-set/action examples do
   not supply the comparison under the Stacks hypotheses. No duplicate or shorter
   complete replacement was found.
4. **Route and pruning: PASS.** The proof constructs precisely the hypotheses of
   Mathlib's proved 0BN4 instance; it uses the original functor in the conclusion
   and uses `uSwitch` only to witness existence of a fibre functor. Both remaining
   proof imports in the existing module are used. The new module's public import
   supplies its signature, and its two private imports supply the proof. Compared
   old and new dependency sets: `## No longer needed` lists all four removed nodes
   and all three removed imports. Read `dag/units/sk-prop-h2.json`: this node carries
   neither its realized statement nor any realized step; its Kummer route stays
   unchanged. No unit file was changed.
5. **DAG agreement: PASS.** The existing node differs only in `proof`, `proof_deps`,
   and `proof_origin`. Read both delivered nodes against the Lean proofs; in each,
   `proof_deps` is exactly the union of the steps' `uses`. The new node has its
   statement dependency, source, proof, agent origin, search records, creation
   record, blueprint parent, chapter/unit, and matching Lean declaration. Neither
   node claims to eliminate the existing axioms theorem's admission.

**Changes by the second reader:** appended this independent review and performed
fresh searches, compilation, and explicit axiom checks. No Lean or DAG repair was
needed; the mathematical implementation and delivered node files are unchanged.
