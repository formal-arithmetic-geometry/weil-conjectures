## What changed

Reduced `AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso` to two
independent parts of Stacks Tag 03RV. The forward part gives finite constant local
models and finite geometric stalks for the canonical representable sheaf. The converse
part descends finite constant local models to a finite étale representative. The original
module supplies the sheaf witness using the existing subcanonical small étale site,
extracts each local isomorphism, applies `Sheaf.isConstant_of_iso`, and combines local
constancy with the finite-stalk field. Its signatures and definitions are unchanged.

During this session the repository received the idempotent and finite étale lifting
reductions from another delivery. The sandbox was refreshed from that source, preserving
those landed proofs. They are not counted as new progress by this delivery.

Two new proof-only imports were added. Both new modules compile before the original
module; the complete sandbox compiles without warnings through lcompile.py. The two
existing DAG records for the conjunction theorem now describe the actual reduction.

## Proved and sorry left

Newly reduced: `AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso`
(nodes `lemma-weil-pbc-finite-locally-constant-etale-equivalence` and
`lem-galois-flc-representable`). Its proof has no local `sorry`.

The following declarations have `sorry` as their entire proof:

- `AlgebraicGeometry.Etale.bijective_cohomologyMap_one_constantSheaf_of_henselianRing`
  (`lemma-weil-pbc-h1-torsor-comparison`), unchanged in the original module.
- `AlgebraicGeometry.Scheme.finiteEtale_yoneda_local_trivializations`
  (`lem-weil-pbc-finite-etale-yoneda-local-trivializations`), new.
- `AlgebraicGeometry.Scheme.finiteLocallyConstant_sets_representable`
  (`lem-weil-pbc-finite-locally-constant-sets-representability`), new.

The existing idempotent lifting, finite étale equivalence and henselian-local corollary
remain proved from their existing dependencies. Neither new helper is the whole original
conjunction: the forward helper also specifies finite local values, and the converse
helper addresses effective descent independently. Empty schemes and empty finite fibres
are included. Local ranks may vary without a global finite bound.

## No longer needed

Removed unused imports from the original module:

- `Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable`
- `Sheaf.AlgebraicGeometry.FiniteEtaleDescent`
- `Sheaf.AlgebraicGeometry.GaloisCategories`
- `Sheaf.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`
- `Sheaf.Paper.FiniteEtaleEtaleLocalSplit`
- `WeilConjectures.CategoryTheory.Sites.Torsor`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.Mathlib.RingTheory.Henselian`

No mathematical node is declared obsolete. The local splitting, constant sheaf
representability and descent dependencies belong to the new intermediate nodes, rather
than to the combining proof. The small-site representable sheaf witness is obtained
from the already existing `subcanonical_smallEtaleTopology`, so the bespoke
`SmallEtaleRepresentablePresheafSheaf` lemma is not used by this reduction. The unresolved
H¹ node retains its route; this delivery makes no claim that its torsor dependencies
can be pruned.


Direct dependencies removed from `lem-galois-flc-representable.proof_deps`:

- `def-pc-fibre-product`
- `def-weil-pbc-constant-sheaf`
- `def-weil-pbc-etale-sheaf-of-sets`
- `def-weil-pbc-etale-site`
- `def-weil-pbc-finite-etale-category`
- `lem-galois-constant-sheaf-sets-representable`
- `lem-galois-descent`
- `lem-galois-yoneda-fully-faithful`
- `lem-weil-pbc-etale-composition-cancellation`
- `lem-weil-pbc-etale-covering-base-change`
- `lem-weil-pbc-etale-local-on-source`
- `lem-weil-pbc-etale-scheme-base-change`
- `lem-weil-pbc-finite-coproduct`
- `lem-weil-pbc-finite-etale-etale-local-split`
- `lem-weil-pbc-finite-local-on-target`
- `lem-weil-pbc-open-fibre-product`
- `lem-weil-pbc-scheme-coproduct-family`
- `lem-weil-pbc-small-etale-representable-presheaf-sheaf`

These are removed from the combining proof, not a claim that their mathematical
content is obsolete. Local splitting, constant-set representability, Yoneda and descent
remain in the intermediate nodes' plans; the other entries are definitions or the
base-change, coproduct and gluing constructions explained in their docstrings. The
canonical subcanonical-site instance replaces the bespoke sheaf-property lemma here.
The other updated node previously had an empty `proof_deps`, so removes no dependency.

## Where the brief, the DAG or earlier work was wrong

The initial brief snapshot had four sorries, but two reductions landed concurrently.
Against the refreshed source this delivery closes one of the two remaining sorries.

The apparent shortcuts `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence`
and `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent` both already import
this module: import_direction.py rejects importing them here. They cannot supply the
proof of their own upstream representability input.

`finite_stalk_of_finite_locally_constant_sets` in the existing
`Sheaf.AlgebraicGeometry.FiniteLocallyConstantStalk` has an `IsAlgClosed` binder, whereas
`Scheme.IsFiniteSheaf` quantifies over `IsSepClosed`. The new forward intermediate
explicitly includes the separably closed finite-stalk conclusion. Its docstring explains
the direct local argument; a later worker must account for this binder difference when
using the existing finite-stalk module.

LeanSearch returned an Internal Server Error. The unavailable search and the successful
LeanFinder, Loogle and source searches are recorded honestly in both new nodes.
The Stacks Tag 03RV statement and proof were read on the Stacks website. Its local .tex
copy is absent on this machine; no repository literature files were written.

## New nodes

`lem-weil-pbc-finite-etale-yoneda-local-trivializations`, in
`lean/Sheaf/AlgebraicGeometry/FiniteEtaleYonedaLocalTrivializations.lean`, supplies finite
local constant models and finite stalks for the canonical finite étale representable
sheaf. It follows the forward implication of Tag 03RV using local splitting. The new
public import of the Proetale complements supplies the existing subcanonical-site
instance required to state the canonical sheaf.

`lem-weil-pbc-finite-locally-constant-sets-representability`, in
`lean/Sheaf/AlgebraicGeometry/FiniteLocallyConstantSetsRepresentability.lean`, supplies the
converse descent argument of Tag 03RV: finite local models, Yoneda descent data, and
effective finite étale descent. Its hypotheses are the explicit local constancy and
finite-stalk data, so its statement does not import the original module or create a
cycle. No definition, statement signature or change record was needed.

## Second reading by G1

1. Compared the entire original module with the repository using `diff`, and checked
   every existing declaration with the delivery parser: all signatures and definitions
   are byte-for-byte unchanged. Only the representability conjunction's proof and
   proof-only imports differ. The other landed reductions are preserved. No change
   record is necessary. Verdict: pass.
2. Compiled all three modules with `lcompile.py --all`: no errors or warnings.
   Searched every delivered Lean file for forbidden declarations and all `sorry`s:
   exactly the three named theorems listed above remain open, with no hollow definition.
   Compiled scratch copies with `#print axioms` for every declaration. Only `propext`,
   `Classical.choice`, `Quot.sound` and `sorryAx` occur; the latter remains through the
   explicitly open intermediate theorems and existing dependencies. This is a checked
   reduction, not an axiom-free completion of representability. Verdict: pass.
3. Read both helper signatures, their full docstring proofs and their node records,
   and checked Stacks Tags 03RV and 04HN on the source website. The forward helper
   gives finite local values plus stalk finiteness; the converse helper is independently
   the descent implication, not a renamed copy of the whole conjunction. On a nonempty
   trivializing member, choose an algebraic closure of a residue field (in universe u)
   to see that its constant value is finite; resize that finite set for the scheme
   coproduct. Empty members can be removed, and the empty base has the empty representative.
   Empty fibres and disconnected bases with unbounded local ranks cause no exception.
   The localized site is the small etale site of the cover member, so the displayed
   local isomorphisms have the right domain. Independent LeanFinder search for a finite
   etale representable sheaf locally constant finite set, Loogle search for
   `CategoryTheory.Sheaf.IsConstant`, and `rg` searches of both library roots found no
   usable theorem closing either helper. The fibre-point finiteness Mathlib hit does
   not identify a sheaf stalk. Inspected ConstantSheafSetsRepresentable,
   FiniteEtaleDescent, FiniteLocallyConstantStalk and FiniteEtaleEtaleLocalSplit: each
   supplies only part of the argument and remains open. In particular the algebraically
   closed binder of the existing stalk theorem cannot directly discharge the new
   separably closed conclusion. No helper can be closed in a few minutes. Verdict: pass.
4. Read the combining proof top down: canonical Yoneda sheaf, local trivializations,
   `Sheaf.isConstant_of_iso`, then the independent descent result. Proof-only imports
   are plain imports. The new modules' public imports supply their signature notions
   and, in the forward module, the required subcanonical instance. Checked both unit
   records `sk-thm-p1` and `sk-prop-h2`: no node realized there is removed or bypassed;
   the finite-etale/descent route remains. Completed the report's exact list of every
   old direct proof dependency removed. These removals do not assert global obsolescence.
   Verdict: pass after the reporting repair.
5. Compared both existing node JSON files against the repository: only `proof`,
   `proof_deps` and `proof_origin` differ, and they name precisely the two lemmas used
   by the Lean reduction. Checked each new node's source, self-contained statement,
   statement dependencies, proof plan, search records, split status, creation record,
   blueprint parent, chapter/unit and verbatim Lean signature. The source plans match
   the docstring arguments, including the explicitly recorded separably-closed stalk
   issue. Verdict: pass.

Second reading changed only this report: supplied the missing exhaustive dependency
removal list and recorded the independent mathematical, signature, compilation and
axiom checks. No Lean proof, statement, definition or node was rewritten.
