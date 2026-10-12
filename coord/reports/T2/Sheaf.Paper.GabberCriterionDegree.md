## What changed

Replaced the sole sorry in `AlgebraicGeometry.Etale.gabberCriterion_degree` with a
complete Lean proof from two strictly smaller intermediate statements. The proof
inducts strongly on the degree simultaneously over all principal opens D(h),
constructs the ideal of restrictions killing a fixed class, proves h belongs to
its radical by testing prime ideals, obtains a power h^N in the ideal, and uses
injectivity of pullback along the isomorphism D(h^N h) = D(h). Finally D(1) is
isomorphic to Spec R and its pullback detects equality. All existing signatures
and public imports are unchanged.

The two new modules are `Sheaf.Paper.GabberPrincipalClassLocallyZero` and
`Sheaf.Paper.GabberPrincipalVanishingIdeal`. Their proof-only imports keep the
comparison, local Zariski vanishing, Mayer--Vietoris and restriction functoriality
available to the next workers. The item's proof imports only those two new
modules and Mathlib's ideal operations in addition to its existing public imports.
The target node now records the actual induction and radical argument.

All three modules compile together without warnings other than the two intended
sorry declarations. Edge cases checked in the argument: q=1 gives a vacuous
lower-degree hypothesis; h=0 gives an empty principal open and a vacuous prime
condition; N=0 still gives h^(N+1); a zero ring needs no prime and the radical
intersection proof remains valid; f=0 and g=-f do not require a nonempty open.

## Proved and sorry left

Proved, from the two new statements:
`AlgebraicGeometry.Etale.gabberCriterion_degree`
(node `lem-weil-pbc-gabber-criterion-degree`). No sorry remains in the item.

The delivery leaves exactly two public theorem proofs equal to `by sorry`:

- `AlgebraicGeometry.Etale.gabber_principal_class_locally_zero`, node
  `lem-weil-pbc-gabber-principal-class-locally-zero`: local comparison and
  positive-degree local triviality, for one fixed class on one principal open.
- `AlgebraicGeometry.Etale.gabber_principal_vanishing_ideal`, node
  `lem-weil-pbc-gabber-principal-vanishing-ideal`: ideal closure for one fixed
  class under lower-degree vanishing on all principal opens and the degree-one
  kernel hypothesis. It assumes no strict henselian hypothesis and does not
  assert that the class vanishes.

These statements are independent parts of the source argument. Neither asserts
fixed-degree vanishing or repackages the target theorem. Their combination,
strong induction, radical argument, and final injectivity are proved in Lean.

## No longer needed

Removed these five direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.EtaleMayerVietoris`
- `Sheaf.AlgebraicGeometry.ZariskiCohomologyLocallyZero`
- `Sheaf.Paper.StrictHenselianZariskiEtaleComparison`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The first three are retained in the appropriate new intermediate modules; they
are not pruned from the theorem's transitive proof route. The last two need no
direct import: the statement uses Ext cohomology and the existing public
TopologicalInvariance import already supplies inverse image and pullback.
No module is claimed unreachable from all targets. Of the old node's direct
`proof_deps`, the following nine no longer occur directly in the target proof:

- `lem-weil-pbc-gabber-strict-henselian-zariski-comparison`
- `lem-weil-pbc-principal-localization-open-immersion`
- `lem-weil-pbc-spec-domain-stalks-function-field`
- `lem-weil-pbc-zariski-cohomology-locally-zero`
- `def-weil-affine-spectrum`
- `def-weil-pbc-etale-cohomology`
- `def-weil-pbc-inverse-image`
- `def-sc-zariski-cohomology`
- `lem-weil-pbc-etale-mayer-vietoris`

Comparison, stalk localization and Zariski local vanishing move below the local
lemma; Mayer--Vietoris moves below the ideal lemma. Principal localization is
unneeded on this route: the local lemma can identify stalks of an open subscheme
directly with stalks of Spec R, without presenting D(h) as Spec R_h. The affine,
etale-cohomology and inverse-image definitions remain statement dependencies;
Zariski cohomology remains part of the comparison/local-vanishing route.
`def-weil-pbc-cohomology-pullback` is the sole retained old direct proof dependency.
This reduction keeps the unit's curve/PBC/Gabber route intact.

## Where the brief, the DAG or earlier work was wrong

The original node packages the entire simultaneous induction into one proof
step. Its existing dependencies do not directly supply the needed principal
restriction comparison, the naturality glue between Ext and derived cohomology,
or the ideal of vanishing restrictions. The delivery states the two substantive
steps in exactly the Ext-based interface used by the target and proves the rest.
In particular, preceding-degree vanishing only on Spec R would not suffice;
the induction hypothesis must include every D(a), as implemented here.

The initial source snapshot of `strictHenselian_zariski_etale_comparison`
quantified an arbitrary family `c` of cohomology maps and concluded each was an
isomorphism, without fixing c to the canonical comparison. This was a
statement-interface defect (arbitrary zero maps need not be isomorphisms).
The second reading found the landed repair in
`coord/changes/strictHenselian_zariski_etale_comparison.md`
(landing 20261012T063524-L-3161736): the corrected signature fixes the inclusion
functor and comparison using hi_inclusion, hfstar and hc. No application in this
delivery needs adaptation, since the new local-vanishing lemma remains open
and concerns the actual restriction maps. Its verbal proof uses the canonical
comparison of Stacks 09AX. The comparison still uses Scheme.{u+1} and H' whereas
this item uses Scheme.{u} and H; constructing the canonical data, resolving the
universe difference, and identifying the restriction maps are genuine remaining
work, not supplied by a direct application of the corrected declaration.

Stacks 0GY0 omits details when replacing R by R_h. Here no localization of the
kernel hypothesis is assumed: all classes and induction hypotheses are on D(h)
with R fixed, and degree-one addition uses hf and hg in the original ring.

The local Stacks TeX and unit _section.md copies are absent on this machine;
I read the recorded unit JSON and the source proof at
https://stacks.math.columbia.edu/tag/0GY0. The new nodes cite the corresponding
TeX label. The item's nearest blueprint ancestor is null according to
blueprint_refs.py; new nodes inherit that null and record the precise source
paragraph. Blueprint searches for Gabber, vanishing ideal and locally zero
found no existing blueprint realization of the new statements. DAG/library
searches found only the parent criterion and its unbundled inputs.

LeanSearch returned HTTP 500 for both new statements, recorded as unavailable.
LeanFinder and source grep ran successfully; they found unrelated cotangent
cohomology, ordinary ideal sheaves and the generic Mayer--Vietoris API, not the
statements needed here. No change to another module or declaration was made.

## New nodes

`lem-weil-pbc-gabber-principal-class-locally-zero` in
`dag/nodes/sec-proper-base-change/` records local vanishing on D(fh) near every
prime avoiding h, with comparison, local triviality, and restriction naturality
as its proof dependencies. Its own module has one public sorry theorem and a
complete proof in words.

`lem-weil-pbc-gabber-principal-vanishing-ideal` in the same directory records
ideal closure at the inductive step, with degree-one addition via the kernel
condition and higher-degree addition via Mayer--Vietoris. Its own module has one
public sorry theorem and a complete proof in words. Neither new node closes the
whole fixed-degree claim. No change record is required because existing
statements, definitions and public imports were preserved.


## Second reading by T2

1. **Unchanged interfaces — pass.** Read the diff against the repository's
   GabberCriterionDegree.lean. The existing theorem's entire signature is byte
   for byte identical; its docstring, universe and four public imports are also
   unchanged. Only its proof and private imports change. The other two modules
   are new; no existing definition, declaration, or target statement changes,
   so no change record is required.

2. **Lean proof and axioms — pass, conditional on the two listed splits.**
   Compiled all three files together through lcompile.py, in import order,
   without errors or unintended warnings. Independently compiled scratch copies
   with `#print axioms` for each of the three declarations: each lists only
   propext, Classical.choice, Quot.sound and sorryAx. The latter is expected:
   the two named split theorems remain open. The item has no sorry; the two new
   files have exactly one each, with no hollow definitions or prohibited
   declarations. The induction supplies every positive lower degree on every
   principal open. The prime-ideal contradiction establishes h in the radical;
   the resulting power gives D(h^(N+1)) = D(h), so isomorphism pullback
   injectivity proves the class zero. D(1) then detects equality on Spec R.

3. **Split statements — pass.** Read Stacks 0GY0, including the omitted
   localization details, and 09AX online. The local lemma is precisely the
   local-triviality part: hR is used only to compare cohomology on D(h) and its
   subopens; positive-degree local vanishing and the principal-open basis give
   f outside p. It asserts no global vanishing and needs no hfg. The ideal
   lemma uses no henselian hypothesis: closure under multiplication is further
   restriction, degree-one addition applies hfg to hf and hg in R, and higher
   addition uses Mayer--Vietoris with the q-1 hypothesis on D(hfg(f+g)). Nested
   inverse images must be transported by upperStarComp and the cohomological
   functoriality comparison; this genuine remaining formalization is explicitly
   acknowledged rather than assumed definitional. Checked q=1 (empty hprev),
   q=2 (only degree-one intersection needed), h=0, the zero ring, f=0,
   g=-f, and xi=0. No edge case contradicts either statement. Fresh LeanFinder
   searches used neighborhood/stalk and annihilation/open-cover wording; the
   results concerned structure-sheaf sections and ideal-sheaf constructions.
   A fresh Mathlib grep found generic Mayer--Vietoris APIs only. Repository
   searches and reading EtaleZariskiCohomology and Gabber's restriction-injectivity
   module found respectively quasi-coherent curve comparison and degree-zero
   sheaf injectivity, neither the required general-sheaf statement. The existing
   comparison and Mayer--Vietoris interfaces cannot close these splits in a
   few minutes: both need bridges to the Ext-based restriction maps. The
   arbitrary-c defect in the initial snapshot was subsequently repaired by the
   landed change record read above; neither version is applied in this delivery. Neither split restates the target.

4. **Top-down reduction and pruning — pass after report repair.** The real
   induction, prime/radical argument and two injectivity steps are in the item's
   proof. Mathlib supplies the radical intersection and power facts; the
   existing cohomologyMap_bijective supplies isomorphism injectivity. New lemmas
   are used for the two independent unresolved portions only. Imports needed
   solely for proofs are plain imports. Read sk-thm-p1.json, including all
   realized entries: this sub-unit change replaces no realized statement or
   step and retains comparison, local triviality and Mayer--Vietoris. Corrected
   the report to enumerate every removed old direct proof dependency and to
   distinguish the unused principal-localization presentation from dependencies
   retained below the new lemmas. No globally unreachable module is claimed.

5. **DAG agreement — pass after metadata repair.** Read all three node files
   against the Lean declarations and proof. Each proof_deps is exactly the union
   of the step uses; the target records strong induction, radical membership,
   basic-open equality, and final injectivity in the order written. New nodes
   match their Lean signatures, carry source places, complete verbal arguments,
   statement dependencies, three search kinds (the unavailable LeanSearch is
   reported), creation metadata, chapter/unit, and blueprint ancestry. The old
   node changes only proof, proof_deps and proof_origin. Marked its steps
   non-elementary because they invoke the two substantive splits or topological
   invariance; the arithmetic and lattice operations within them remain
   elementary. No existing statement or node statement changed.

Changes from this reading: corrected pruning documentation; corrected the
parent node's elementary flags; added the matching blueprint id to each new
module docstring; updated the comparison-interface discussion after reading its
landed change record. The Lean proof and all theorem signatures are retained.
