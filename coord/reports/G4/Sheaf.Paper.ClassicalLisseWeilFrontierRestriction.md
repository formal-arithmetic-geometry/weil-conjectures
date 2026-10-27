## What changed

Replaced the whole proof of
`WeilConjectures.ZlFrontier.classical_lisse_weil_frontier_restriction` by a complete
Lean assembly of three proper argument steps. The proof obtains the frontier
independently of the Weil structure and applies the one-model restriction result to
every piece at its common degree. The no-Weil frontier clause uses the already-defined
`RestrictionModel.identification` directly, retaining its exact lattice and factorization.
The geometric Frobenius square is proved privately from `zlFrobenius_naturality` and
`constantExtensionFiber_return`; it is supplied to the restriction step explicitly.

Moved all existing auxiliary data, including `RestrictionConclusion`, verbatim into
`Sheaf.Paper.ClassicalLisseWeilFrontierData` and publicly reexported it from the item.
This breaks the import cycle between the assembly and its argument lemmas. It is not
splitting a slow compile. A textual comparison confirms that the entire data block is
identical and the original declaration signatures are unchanged. No source-library file
is modified, and the target statements are untouched.

The new proof modules are `Sheaf.Paper.ClassicalWeilRestrictionExistence`,
`Sheaf.Paper.ClassicalFrontierExistence` and `Sheaf.Paper.ClassicalSuccessiveRestrictions`.
Each contains one named public theorem with its whole remaining proof `:= by sorry`,
a source, a proof in words and a matching node. The extraction is recorded in
`coord/changes/G4-classical-frontier-restriction-data.md`. No other agent was started.

Validation: every delivered Lean module compiles individually through lcompile.py;
the complete assembly also compiles against the sandbox modules. No timeout was used
as a reason for splitting. The all-files compile checks the import order. The main
Frobenius helper required only a local transparency setting so the finite-field datum
can unfold at the rewrite; no global definition or reducibility attribute changed.

## Proved and sorry left

Closed the item's one textual hole:
`WeilConjectures.ZlFrontier.classical_lisse_weil_frontier_restriction`
(node `lem-zl-classical-lisse-weil-frontier-restriction`). Its assembly proof has no sorry.
The private helper `restriction_model_frobenius_square` is also fully proved.

Three holes added, each the entire proof of one separate public theorem:

- `WeilConjectures.ZlFrontier.classical_weil_restriction_exists`
  (`lem-zl-classical-weil-restriction-exists`): one finite-field model's classical Weil
  lift, finite coefficient representation and normalized sf local-operator compatibility,
  with the geometric Frobenius square already supplied. It constructs no frontier.
- `WeilConjectures.ZlFrontier.classical_frontier_exists`
  (`lem-zl-classical-frontier-exists`): the canonical geometric frontier subordinate to
  the supplied partition, with no Weil map or successive-restriction assertion.
- `WeilConjectures.ZlFrontier.classical_successive_restrictions`
  (`lem-zl-classical-successive-restrictions`): composition of normalized restrictions
  on the supplied lattices, with no frontier or Weil structure.

This is a decomposition of one hole into three strictly smaller argument steps, not
a net proof gain. Actual item holes: 1 before, 0 after; added helper holes: 3; net: -2.
All other delivered definitions are real constructions, and the data module has zero
holes. Previously existing holes in imported modules are unchanged.

## No longer needed

No mathematical module or declaration is withdrawn. The original two public imports
`Sheaf.Paper.ClassicalLisseWeilRestrictionMaps` and
`Sheaf.Paper.NormalizedFiniteRealizationFibre` move to the data module and remain public
reexports through it. They are still required by the unchanged interfaces.

The main theorem's proof_deps now lists the three assembly lemmas, the extracted data,
`def-zl-weil-ind-sheaf-category` and
`lem-zl-constant-extension-weil-heart-equivalence`. Its former direct proof dependencies
are now attached to the relevant smaller steps:
`def-pod-lisse-l-adic-sheaves`, `def-weil-algebraically-closed-coefficients`,
`def-weil-frobenius-detailed`, `def-weil-local-frobenius-trace`,
`def-weil-pbc-scheme-reduction`, `def-weil-weil-sheaf-complex`,
`lem-per-lisse-completed-system-comparison`,
`lem-trf-integral-pullback-comparison-realization`, `lem-tw-lisse-rational-realization`,
`lem-zl-classical-system-raw-lisse-realization`, and
`lem-zl-smooth-affine-frontier-stratification`.
They are not pruned from the overall argument or target closure. The main node's three
old tool_uses entries (lem-per, lem-tw and lem-trf) are removed there because those
comparisons are now used inside the split steps. No new approval is added.

The unit's existing route is retained: the finite-field frontier construction and
restriction of the original Weil structure are still the argument. No pruned modules.

## Where the brief, the DAG or earlier work was wrong

The current `smooth_affine_frontier_stratification` theorem does not state the
length-zero clause for an empty scheme: its proof replaces a length-zero filtration by
a one-step chain. The new frontier step handles the empty scheme directly, using the
isomorphism from its reduction to the empty scheme and no pieces.

That dependency also quantifies an arbitrary ambient Over isomorphism χ, whereas this
item pins `constantExtensionFiberIso`. It cannot be replaced merely by comparing its
projections: the theorem does not assert the needed projection equation. The frontier
step's proof in words explicitly corrects this by descending χ composed with the
inverse canonical isomorphism, its inverse and both equations to a further finite
extension, then composing the diagram's ambient maps with the descended automorphism.
This preserves the reduced closed chain, clopen covers and smooth dimensions and fixes
the geometric factorizations. Stacks 01ZM(2),(3) supplies exactly this finite data
argument. This glue is one reason the frontier step remains a separate hole.

The existential `classical_system_raw_lisse_realization` theorem chooses its realization
families. Its signature alone does not directly identify those families with the
uniformly supplied R, S, A, C here. The normalized-unit and fibre bridge assembly remains
part of the one-model restriction and successive-restriction steps. Their docstrings
state the actual needed argument, rather than silently instantiating an existential
family as arbitrary supplied data.

Edge cases checked at the statements: empty Y₀, rank-zero lattices, reduced=false and
reduced=true, m=1, a nonreduced ambient scheme, dimension-zero pieces, and a partition
permuted by Frobenius. None of the three smaller steps assumes Frobenius-stability of
the chosen partition or integral lattice. No statement was weakened or marked disputed.

## New nodes

`def-zl-classical-frontier-restriction-data` attaches the unchanged auxiliary data to
its new owning module. Its primary declaration is `RestrictionModel`; its lean record
also lists the remaining data declarations. This is an interface relocation only.

`lem-zl-classical-weil-restriction-exists` carries original proof steps 2--5 with the
Frobenius square already supplied by the proved helper. It excludes all frontier
construction and the uniform assembly across its pieces.

`lem-zl-classical-frontier-exists` carries original step 6's geometry, retaining the
support reduction, canonical geometric factorization, empty-chain and dimension-zero
requirements. It adds the precise canonical-comparison glue described above.

`lem-zl-classical-successive-restrictions` carries original step 1's normalized
composition equation on the supplied lattices.

All inherit the original chapter and unit. Mathlib and repository searches found the
categorical fully faithful lift but no duplicate of these normalized assembly steps.
The change record is `coord/changes/G4-classical-frontier-restriction-data.md`.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
