## What changed

Completed the unchanged theorem
`AlgebraicGeometry.Scheme.schemeTheoreticSupport` in
`lean/Sheaf/Paper/SchemeTheoreticSupport.lean`. Its ideal data is constructed explicitly:
the affine ideals are exactly the section-module annihilators, and their compatibility
is a named proved theorem. No data is chosen from an arbitrary existence statement.

Added `lean/Sheaf/AlgebraicGeometry/AnnihilatorAffineBasicOpen.lean`, with the proved public
statement `AlgebraicGeometry.Scheme.Modules.annihilator_affine_basicOpen`. Its private
algebra lemma proves annihilator localization for any multiplicative subset by multiplying
one denominator for each of finitely many generators. The duplicate scheme-specific private restriction helper has been replaced in place by
`isFiniteType_over_site`, a theorem for an arbitrary category with binary products and pullbacks,
a Grothendieck topology, a sheaf of rings and the stated slice-site and iterated-slice-site sheafification and
local-bijectivity assumptions. The scheme case is obtained by specializing these binders.
The helper's elaboration options remain local to that declaration.

The main proof uses Mathlib for the closed immersion, kernel identity, and quotient
pullback charts; sheaf locality and naturality prove the arbitrary-open criterion and
minimality. The existing affine finite-module support formula proves image equality.
The two DAG records follow the implemented proof. Existing signatures and public imports
are unchanged, and the unit's realized route is preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.schemeTheoreticSupport`
(node `lem-weil-pbc-scheme-theoretic-support`).

Also proved the new compatibility theorem
`AlgebraicGeometry.Scheme.Modules.annihilator_affine_basicOpen`
(node `lem-weil-pbc-annihilator-affine-basic-open`). The private helpers in both modules
are proved. There is no direct `sorry` left in either delivered module, and zero holes
were added or split off. This closes an original hole from existing named dependencies,
rather than moving it to a new unproved statement.

Existing dependencies still supply the affine section base-change theorem, the affine
finite-type criterion, and the finite-type support formula. Their unfinished proofs are
not claimed closed by this delivery.

Validation: both files compile in sandbox import order using `lcompile.py --all`, without
warnings. The general algebra proof permits an empty generating family and localizations
at zero, so the zero-module and zero-basic-open cases need no exceptions. The global
proof also covers the empty scheme by its pointwise affine-neighborhood argument.

## No longer needed

Removed `import Sheaf.RingTheory.AnnihilatorLocalizationAway` from the main module.
The module `Sheaf.RingTheory.AnnihilatorLocalizationAway` and its node
`lem-weil-pbc-annihilator-localization-finite` are not used by either delivered proof:
the required localization identity is proved directly and more generally in a private
helper of the new compatibility module. This is the substantive pruning.

Removed the direct main-module imports of
`Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange` and
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`, replacing them with
`Sheaf.AlgebraicGeometry.AnnihilatorAffineBasicOpen`. Those two original modules and their
nodes remain needed through the new module; they are relocated dependencies, not pruned
from this item's transitive closure. No additional module is claimed globally unreachable
from the five targets, since other routes may still import it.

## Where the brief, the DAG or earlier work was wrong

Repair of the returned delivery: the original private `isFiniteType_over` duplicated the
statement in `Sheaf.AlgebraicGeometry.FinitePushforwardCoherent`. That existing theorem is
private, so an ordinary import cannot use it. Following the return's permitted alternative,
this delivery generalizes the helper in place to `isFiniteType_over_site`; its explicit
binders no longer mention schemes, structure sheaves or open subsets. No existing library
module or interface is adapted, and no unfinished theorem is added.

The original plan was mathematically adequate. Its localization statement is specialized
to the canonical localization ring and module, while the proof needs the actual basic-open
section ring and restriction map. Mathlib's `IsBaseChange` / `IsLocalizedModule` interface
and the direct finite-generator denominator proof avoid those transport issues.

The compatibility step is the only additional public statement. Its proof is complete,
so it creates no new work item with a direct hole. Once affine compatibility is available,
the arbitrary-open annihilator criterion follows solely by semilinearity, naturality, and
sheaf separation; no separate unproved annihilator-sheaf construction is needed.

The Stacks TeX source was absent on this machine. The source texts actually read were
https://stacks.math.columbia.edu/tag/05JU and
https://stacks.math.columbia.edu/tag/07T8, together with the local DAG proof and Mathlib
sources. LeanSearch returned an internal-server error; that unavailable search is recorded
without a verdict. LeanFinder, Loogle, source searches, and the blueprint search ran.
No statement dispute or forced adaptation arose.

## New nodes

`lem-weil-pbc-annihilator-affine-basic-open`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-annihilator-affine-basic-open.json`, records
exactly the basic-open compatibility needed by the real `IdealSheafData` construction.
Its source is the last paragraph of Stacks 05JU and the localization specialization of
07T8. It is strictly a part of the original argument, and is proved from existing affine
base-change and affine finiteness declarations plus Mathlib localization tools. Its node
records the three kinds of search, source attribution, edge cases, and the complete
finite-generator argument. No change record is required: no existing interface changed.

## Second reading by H1

1. Compared both delivered Lean modules and the existing scheme-theoretic-support module
   with the repository versions. The target signature is unchanged byte for byte; the new
   compatibility theorem is recorded by its new node. Verdict: passed.
2. Compiled both modules with `lcompile.py --all`; there are no `sorry`, forbidden
   declarations, or added axioms in the delivered source. The compatibility statement is
   the precise basic-open annihilator identity and its proof covers zero modules and empty
   generating families. Verdict: passed.
3. Checked the new node, its source, proof dependencies, Lean declaration and report
   against the implementation, and searched Mathlib and the library for duplicates.
   Verdict: passed; no split-off holes were added.
4. The proof uses the existing affine finite-type, section base-change, closed-subscheme,
   and support declarations. The old localization import is removed and the remaining
   dependencies are retained through the new module. Verdict: passed; pruning is recorded
   above.
5. The unit route remains realized through the affine compatibility step and the
   scheme-theoretic-support node; the DAG proof and dependency lists follow the Lean proof.
   Verdict: passed.

I changed only proof bodies, proof-only imports, the existing node's proof metadata, and
added the compatibility module/node. I also added this second-reading record.
