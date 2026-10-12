## What changed

Replaced the sole sorry in `AlgebraicGeometry.exterior_dual_pairing_exists` by a complete
Lean reduction with its signature and existing docstring unchanged. The proof constructs
a morphism of exterior presheaves from local alternating functionals, proves restriction
compatibility, and applies the module sheafification adjunction. Evaluation of its unit
recovers exactly the original determinant formula.

Added three modules, one declaration each:

- `DeterminantDualPairingFunctional`: the remaining unique fixed-tuple local functional.
- `ExteriorSheafDualExt`: proved extensionality using local surjectivity of the exterior
  sheafification unit, pure-wedge spanning, naturality and separatedness of the structure sheaf.
- `DeterminantDualAlternatingFamily`: proved existence and uniqueness of the alternating family
  from the fixed-tuple functional. Additivity and scalar compatibility use determinant column
  identities; alternation uses vanishing of a determinant with equal columns.

The choices in the proofs come from unique-existence theorems; no definition chooses an
arbitrary witness. No existing definition, signature or visibility changes. All four modules
compile together without warnings with the authorized single-file compiler. No global build run.

## Proved and sorry left

Closed: `AlgebraicGeometry.exterior_dual_pairing_exists`
(node `lem-sc-exterior-dual-pairing-construction`). Its proof contains no sorry.

Added and proved: `AlgebraicGeometry.exteriorSheaf_dual_ext`
(node `lem-sc-exterior-sheaf-dual-ext`) and
`AlgebraicGeometry.exterior_dual_pairing_local`
(node `lem-sc-exterior-dual-pairing-local`). Their proofs contain no sorry.

Added and still sorry: `AlgebraicGeometry.exterior_dual_pairing_functional`
(node `lem-sc-exterior-dual-pairing-functional`). This fixes one open and one tuple;
it asks only for the unique internal functional with the determinant formula on all subopens.
It does not assert a global morphism, alternation in the tuple or restriction compatibility
between different opens. Those parts are now proved in Lean.

This is a decomposition: one original hole closed, one smaller hole added, net zero holes.
The main theorem and the local alternating-family theorem still depend on that hole.
The extensionality helper has no new theorem holes beyond the existing exterior-sheaf interface.

## No longer needed

Removed the redundant proof import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom` from the item:
it is already publicly imported by the retained `Modules.Dual` interface.
All original public imports remain necessary for the unchanged statement.
The old direct proof dependency `lem-sc-exterior-power-dual-pairing` is no longer
used directly by the item; it is retained under
`lem-sc-exterior-dual-pairing-functional`. No original mathematical dependency
is pruned transitively: the ring exterior-power pairing
and module sheafification interface remain needed in the remaining local functional's proof.
The item's direct DAG dependencies now name the local alternating-family and extensionality
nodes; the canonical ring pairing is below the fixed-tuple functional node.

Discarded the earlier sandbox-only `DeterminantDualPairingConstruction`,
`DeterminantDualPairingMorphism` and `DeterminantDualPairingFormula` modules.
They were never library dependencies and do not count as DAG pruning.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox's formula theorem claimed the determinant formula for an arbitrary
morphism: false, for instance the zero morphism over a nonzero ring in degree zero.
Its gluing theorem claimed any family of functionals glues, without multilinearity or
restriction compatibility: also false. Neither is retained or used. The earlier report
named a construction-data declaration absent from its files. The replacement report and
DAG now match the delivered Lean.

A formula only on wedges over the largest open does not determine an internal functional:
its components on every subopen matter. The remaining lemma therefore explicitly quantifies
over every subopen, and the proved extensionality lemma uses that exact hypothesis.

The original DAG's plan is retained: determinant functionals, their compatibility,
then exterior universal property and sheafification. The unit record's realized lists are
empty; no unit statement or prescribed unit step is bypassed.

The local checkout has no `literature/stacks-project` directory. Read the primary Stacks
pages for Tags 03CY and 0BRT directly, and Mathlib's exterior pairing source locally.
Tag 0BRT motivates determinant inversion; it does not explicitly spell out the general
sheaf determinant pairing. The expanded construction is identified as agent-written in
the new nodes, using the module sheafification interface of Tag 03CY and the explicit
Mathlib determinant pairing. LeanSearch returned an internal server error; this is recorded
as unavailable, with LeanFinder and source grep searches completed.

## New nodes

`lem-sc-exterior-dual-pairing-functional`: the one remaining obligation, unique extension
of the determinant functional for a fixed open and tuple. Its docstring and node give
all construction and uniqueness steps, including the open-site restriction of the
locally bijective sheafification unit. Empty opens, the zero ring and degree zero satisfy
the same argument; no freeness, rank or nonzero-ring assumption is needed.

`lem-sc-exterior-sheaf-dual-ext`: fully proved extensionality on all subopen wedges.
The implementation uses image sieves and separatedness directly, avoiding any new
open-restriction/sheafification comparison lemma.

`lem-sc-exterior-dual-pairing-local`: fully proved alternating-family packaging and
uniqueness, from the fixed-tuple lemma and the proved extensionality theorem.
The determinant argument treats all degrees, including zero, uniformly.

All three inherit `sec-picard-framework` and `sk-thm-picard-duality` from the item.
No change record is required: no existing interface or statement is changed.

## Second reading by N1

1. Compared the item with the repository using `diff` and checked the theorem
   signature byte for byte with a script: unchanged, including its docstring
   and public visibility. The other three delivered modules are new. No
   existing definition or target statement changes; no change record is needed.
   Verdict: pass.
2. Compiled all four modules in dependency order through `lcompile.py`, cleanly.
   The only textual sorry is the whole proof of the named functional theorem.
   No forbidden declarations or hollow definitions occur. A scratch copy with
   explicit imports and four `#print axioms` commands reports only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` for each declaration; the
   scratch copy was deleted. The main and local proofs depend on the new
   functional hole; extensionality's `sorryAx` comes from existing interfaces.
   Both choices in the new proofs are from unique-existence statements, which
   determine their data by equality. Verdict: pass as a decomposition, not a
   sorry-free proof of the item.
3. Read the one remaining obligation and its complete docstring argument.
   A fixed tuple yields linear functionals on every subopen; naturality is
   verified on spanning wedges and extension is unique into the restricted
   structure sheaf. This is strictly a part of the construction: alternation
   in the dual tuple, compatibility between opens, and the outer exterior
   universal property and sheafification are actually proved in the delivery.
   In degree zero the empty determinant is 1 and the functional is the
   structure-sheaf identification; on the empty open or over the zero ring
   everything evaluates to zero (where 1 = 0). Degree one is evaluation; equal
   columns give zero without characteristic assumptions. The Stacks pages
   [03CY](https://stacks.math.columbia.edu/tag/03CY) and
   [0BRT](https://stacks.math.columbia.edu/tag/0BRT) were independently read:
   the former supplies unique module-sheafification factorization, the latter
   motivates determinant inversion rather than stating this general pairing.
   Independent searches with the query about extending a natural functional
   across sheafification (LeanFinder), `exteriorPower.alternatingMapToDual`
   (Loogle), and sheafification/extensionality/determinant source searches
   (msearch grep and rg in both libraries and upstream) found ingredients but
   no duplicate sheaf theorem. Formalizing the remaining extension requires
   the restricted-over-site construction, rather than a short application of
   the ring pairing theorem, so it remains explicitly open. Verdict: pass.
4. Read the proof from the original target downward: fixed-tuple functionals
   give the alternating map; wedge extensionality proves restrictions commute;
   the exterior universal property gives a natural presheaf morphism; the
   sheafification adjunction gives the required morphism and formula. No
   shorter existing sheaf-level result was found. Every public import is used
   by the unchanged signatures; the new helper imports are proof-only.
   The redundant InternalHom import is removed. Checked all four original
   proof dependencies: three remain direct, and the ring pairing moves below
   the functional node (now explicitly listed above). The unit's realized
   statement and step lists are empty; its route is not bypassed. Verdict: pass.
5. Read all four nodes against the Lean and checked that each proof_deps list
   is the union of its steps' uses. Existing node changes are confined to the
   proof route and origin. New nodes have the required source, origin,
   searches, creation, blueprint, chapter, unit, and Lean records.
   Replaced the three new nodes' flattened `lean.statement` strings with the
   exact multiline signatures from their files. Verdict: pass.

Second-reading changes: exact new-node signature records and an explicit
account of the old ring-pairing dependency under No longer needed; appended
this independent review. No Lean proof or statement needed repair.
