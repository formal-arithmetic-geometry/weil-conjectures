## What changed

Proved `PrincipalWLocalization.WeakEtaleRefinement.properties` in
`lean/Sheaf/RingTheory/WeakEtaleRefinementProperties.lean`, keeping its signature and the
specified refinement construction unchanged. No other Lean module is changed.

The proof follows the three original stages: obtain the retained-point description; identify
local rings over the strict cover and apply the principal ind-Zariski criterion; prove spectrum
surjectivity and faithful flatness. A proved private helper converts the principal
ind-Zariski presentation to an ind-etale presentation using finite products of etale principal
localizations. No definition or data construction is changed.

Added the proof-only import `WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale` for its
already proved residue-field algebraicity and tensor-spectrum surjectivity helpers, together
with the public upstream stalk API it exposes. The second reading replaced the open stability
theorem application by Mathlib tensor base change, transported through `commRight`, and
removed its direct proof import. It also removed the redundant public
`Sheaf.RingTheory.IndPrincipalZariski` import; `WeakEtaleRefinement` already exposes it.
The existential upstream refinement theorem
is not applied: its ring is a different construction. Updated the item's proof docstring and
DAG proof, proof_deps, and proof_origin to describe the actual argument.

Validation: the complete module compiles with `lcompile.py` in approximately five seconds,
without warnings. No new public declaration or statement change; the only added declaration
is a fully proved private helper. The argument includes empty spectra and the zero ring:
all prime constructions occur after receiving a prime, and finite products permit size zero.

## Proved and sorry left

Closed the one original hole:
`PrincipalWLocalization.WeakEtaleRefinement.properties`
(node `thm-weil-pbc-weak-etale-refinement`).

Holes added: none. Holes left in delivered Lean files: none. Split-offs: none.
This is a proof from existing dependency declarations, including the still-unproved strict-cover,
retained-localization, and principal local-ring criterion declarations; those existing
modules remain subsequent stage-3 obligations. This delivery does not claim that the theorem's
whole transitive axiom closure is already free of sorry.

## No longer needed

Removed proof imports:

- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`.
- `Sheaf.RingTheory.WeaklyEtaleField`.
- `Sheaf.RingTheory.IndEtaleStability`.
- `WeilConjectures.RingTheory.ProEtale.HenselianLocalRing`.

The Mathlib faithful-flat imports are redundant for the ring-homomorphism criterion exposed by
`Mathlib.RingTheory.RingHom.FaithfullyFlat`. The strict-local theorem is used through the already
proved upstream `Algebra.WeaklyEtale.bijectiveOnStalks` exposed by the new upstream import,
so its direct import is redundant; its DAG node remains a logical dependency.

The direct public import `Sheaf.RingTheory.IndPrincipalZariski` was also removed as
redundant: the unchanged public import `Sheaf.RingTheory.WeakEtaleRefinement` itself
publicly imports it. Thus this removes no downstream API. Base change of weak etaleness
uses Mathlib's left tensor-product instance followed by `commRight`; the transport map is
etale because it is bijective, and Mathlib weak-etale composition finishes the transport.
Ind-etale base change, composition, and implication of weak etaleness use proved upstream
APIs. The stability node remains a logical dependency for those statements, as does the
strict-local node for the upstream stalk theorem.

Removed direct DAG dependencies:

- `lem-weil-pbc-weak-etale-field`: the full finitely-generated-subalgebra/ind-etaleness/reducedness
  statement, and its module `Sheaf.RingTheory.WeaklyEtaleField`, are unnecessary here. The
  already proved upstream residue-field helper supplies exactly the algebraicity needed;
  its field calculation is recorded by the existing node
  `lem-weil-pbc-weakly-etale-field-separable`.
- `lem-weil-pbc-faithfully-flat-base-change`: faithful flatness of `B → D₀` is unnecessary.
  Instead base-change the surjection `Spec(C/J) → Spec A`, using the existing generic node
  `lem-weil-pbc-surjective-base-change` and its affine upstream helper, then retain the diagonal
  prime pair. The flat-plus-surjective-spectrum criterion stays needed.

These removals describe this item's proof; other parents may still need those modules.
No unit statement or realized unit step is bypassed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The original DAG's final paragraph compressed the crucial covering
argument: faithful flatness of `B → D₀` alone does not ensure that its surjectivity survives
`D₀ → B′`. The proof explicitly uses closed-point surjectivity of the strict cover to get
surjectivity for `C/J`, base-changes that map, and retains each resulting diagonal prime pair.

The principal ind-Zariski predicate has no direct conversion API to ind-etaleness in its defining
module; the elementary conversion is proved privately here. The retained closed-point
homeomorphism uses the patch topology explicitly, so its use requires specifying that topology
locally when projecting the underlying equivalence. Neither issue needs a definition change.


## Second reading by G1

1. **Visible interface — pass.** Compared the sole delivered Lean module and node with
   the repository versions. The existing theorem signature is byte for byte unchanged;
   no definition, target statement, or declaration visibility changed. There are no
   adapted modules or new public declarations. The redundant public-import removal is
   documented in `coord/changes/WeakEtaleRefinementProperties-imports.md`, including
   all 29 transitive users and their current holders. Removing the redundant
   public import preserves its complete exposure through `WeakEtaleRefinement`.
2. **Proof and axioms — pass.** Compiled the full module with `lcompile.py`. A scratch
   copy with `#print axioms` shows exactly `propext`, `Classical.choice`, `Quot.sound`,
   and the permitted `sorryAx` from open dependencies for `properties`. The private
   `indEtale_of_principal` helper, upstream residue-field algebraicity helper, upstream
   stalk-bijectivity helper, and tensor-spectrum surjectivity helper each use only the
   three standard axioms. There are no holes or prohibited declarations in the delivered
   module, and no data is selected from an unproved mere-existence theorem. The
   equivalence and homeomorphism extracted from `Retained.properties` are used only
   inside this theorem proof to derive propositions.
3. **Split-offs and edge cases — pass.** None were added. The fully proved private
   helper handles the empty finite product. Reviewed the maps and retained diagonal
   pairs, the quotient argument, and maximal-ideal contraction. Empty spectra and the
   zero ring introduce no prime-existence assumption: every prime choice is under an
   existing prime or under the supplied surjectivity hypothesis. Searched with new
   leanfinder, loogle, and grep queries and `rg` across the library. No existing theorem
   about this specified refinement replaces the argument; the upstream existential
   refinement theorem constructs a different ring.
4. **Top-down proof and pruning — pass after repair.** Read the imported declarations,
   the source-library refinement proof, and the unit record
   `dag/units/sk-thm-properbasechange.json`. The proof retains the strict-cover,
   retained-localization, strict-local, local-ring criterion, and covering route.
   The two old direct DAG dependencies omitted from the new proof are both listed
   above. No realized unit statement or step is bypassed; no module is withdrawn.
   All remaining imports are needed either by the signature or by explicit proof APIs.
5. **DAG agreement — pass.** Checked the original and delivered node field by field:
   only `proof`, `proof_deps`, and `proof_origin` differ. Their steps describe the actual
   principal-stage conversion, maximal contraction, stalk identifications, and quotient
   tensor covering argument; the node's statement and Lean record are unchanged.
   Existing stability and strict-local nodes record mathematical dependencies supplied
   here by their proved Mathlib/upstream forms. There are no new nodes to audit.

Second-reading changes: replaced the sole application of the open stability theorem by
Mathlib weak-etale base change and transport through the tensor commutativity isomorphism;
removed `Sheaf.RingTheory.IndEtaleStability` and the redundant public
`Sheaf.RingTheory.IndPrincipalZariski` import; clarified the DAG proof and this report;
wrote `coord/changes/WeakEtaleRefinementProperties-imports.md` as required by preflight.
No other mathematical part of the first worker's proof needed repair. One original hole
is closed, zero holes are added, and zero statements are split off.
