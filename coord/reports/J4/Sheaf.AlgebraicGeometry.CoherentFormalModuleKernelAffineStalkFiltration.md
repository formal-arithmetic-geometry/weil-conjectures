## What changed

Replaced the sorry in `AlgebraicGeometry.coherentFormalModule_kernel_affine_stalk_filtration`
by a compiling proof from two strictly intermediate statements, preserving its complete
signature, visibility, and docstring. The proof first obtains a common affine section
presentation, proves quasi-coherence of every stabilized level using the existing coherent,
kernel, and cokernel/image theorems, and specializes a generic localization theorem to the
intersection submodules. The choice of N and L precedes the stalk variables, as required.
Only ordinary proof imports were added to the item; its public imports are unchanged.

Added `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelAffineSectionQuotients` and
`Sheaf.AlgebraicGeometry.AffineIntersectionQuotientsStalk`, each with one sourced named theorem,
a complete proof in words, and its own node. Updated the item's proof, proof_deps, and
proof_origin to agree with the Lean reduction. No existing interface or target was changed.
All three files compile individually through lcompile.py; the import-ordered sandbox compile
also succeeds. No axiom, hollow definition, arbitrary data choice, or private sorry was added.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.coherentFormalModule_kernel_affine_stalk_filtration`
(node `lem-weil-pbc-formal-kernel-affine-stalk-filtration`). The item has no remaining sorry.
This is a decomposition, not a sorry-free mathematical proof: one upper hole is closed and
two lower holes are added (net -1 holes before any closure-dependent ledger calculation).

Every added hole is the whole proof of a named public theorem:

- `AlgebraicGeometry.coherentFormalModule_kernel_affine_section_quotients`, node
  `lem-weil-pbc-formal-kernel-affine-section-quotients`.
- `AlgebraicGeometry.affine_intersection_quotients_stalk`, node
  `lem-weil-pbc-affine-intersection-quotients-stalk`.

The first theorem has only an affine-sections conclusion, with no stalk or submodule order
map. The second has no formal modules, stabilization, finite completed module, or Noetherian
hypothesis; it localizes any compatible quasi-coherent quotient system with any prescribed
family of kernel submodules. Their combination and the quasi-coherence argument are real Lean.

## No longer needed

None. No original import was removed. All original proof dependencies remain needed in the
lower affine section or localization arguments; they were relocated in the DAG, not pruned.
In particular, completion Noetherianity and the reduced-kernel image bound remain in the
section presentation's proof plan. Artin--Rees for L inside N and finite-cover uniformization
are not used, just as the original node states.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the item's statement or plan was found. The plan did not already
expose the affine section surjections with transition and intersection-kernel equations,
or the generic localization/order-map step, in a directly applicable declaration.
`CoherentFormalModulesAffine` is stated on Spec A, so the open restriction and chart transport
still require glue. The proved `CoherentFormalModuleAffineKernelImageComparison` gives equality
comparisons of quotient images, rather than the projections required here; its
`completed_projections` helper is private and returns additive projections, not the A-linear
section quotient interface. Neither theorem alone supplies the full interface used here.

The unit `sk-thm-p1` and its realized nodes are unchanged. This split stays below the item's
node and follows its affine-then-localize route. `pqf-lem-coherent-ft-locnoeth` is used solely
as a generic coherence-to-quasi-coherence tool; it was already used by the formal-module
library and does not replace a unit step.

Source pages read: Stacks 087W and 087X for the affine quotient description, and 01IB, 01IC,
01I8, 00CS for the localization argument; source labels were checked in the Stacks tex.
The local literature tex files were absent, so the available online source was read.
Mathlib searches through msearch.py are logged in searches.jsonl. LeanSearch returned HTTP
500 (recorded unavailable); LeanFinder found adic quotient and stalk-localization primitives,
Loogle found Submodule.map_comap_subtype, and grep found no stalk filtration theorem. Direct
searches in both library roots and blueprint_refs.py found no duplicate intermediate statement.

Edge cases checked mathematically: on empty U there are no stalk conditions and section
modules are zero; if I(U) is the unit ideal, R is zero and the formal levels on U vanish;
if I(U)=0, the affine formal system is constant and the intersection kernel is zero.
Zero N or L yields zero quotients. For the generic localization statement, r=0 maps the
whole localized L onto M, D_m=0 gives injective localized quotients, and D_m=top gives zero
localized targets. No finiteness over the stalk ring is claimed. Generic localization uses
an explicit tensor/localization construction of M, not an arbitrary existential witness.

## New nodes

`lem-weil-pbc-formal-kernel-affine-section-quotients` records the affine section part of
087X: N, L, A-linear surjections with exact intersection kernels, and compatibility for
all transitions. Its module is
`lean/Sheaf/AlgebraicGeometry/CoherentFormalModuleKernelAffineSectionQuotients.lean`.

`lem-weil-pbc-affine-intersection-quotients-stalk` records localization of arbitrary kernel
families for a quasi-coherent inverse system, including the localized submodule order map
and preservation of extended-ideal powers. Its module is
`lean/Sheaf/AlgebraicGeometry/AffineIntersectionQuotientsStalk.lean`.

Both retain the item's chapter and unit, and cite the same nearest blueprint ancestor.
No change record is needed, since no existing statement, definition, or visibility changed.

## Second reading by J4

1. **Unchanged interfaces and accidental edits.** I diffed the delivered item against the repository
version. The existing theorem signature, visibility, and docstring are byte-for-byte unchanged;
the two additional modules and their three node records are the declared additions. Verdict: pass.

2. **Compilation and trust basis.** I compiled all three delivered modules with
`python3 /home/ubuntu/weil-launcher/lcompile.py --all`; all compiled cleanly. The only remaining
`sorry`s are the two named split theorems, each public and documented. No definitions contain
`sorry`, and no axiom, unsafe, opaque, extern, or implemented_by declaration was added. The
proof path uses ordinary existing declarations and the two explicitly named intermediate holes.
Verdict: pass.

3. **Truth and strength of split statements.** The affine-section theorem supplies exactly N, L,
and compatible surjections with the intersection-power zero criterion; it does not assert stalk
localization. The localization theorem applies to arbitrary quasi-coherent systems and prescribed
kernel submodules, and supplies only the stalk module, maps, order homomorphism, ideal-power
formula, and kernel formula needed by the item. Both are strictly smaller than the original
stalk-filtration statement. I checked zero and unit ideals, zero modules, r = 0, and empty-open
vacuity. Searches found no duplicate declaration. Verdict: pass.

4. **Pruning and imports.** The parent proof uses both new theorems and its coherence, kernel, image,
and locally-Noetherian imports. No original import is unused, so no import or proof dependency was
removed. The proof remains below unit `sk-thm-p1`; its affine-then-localize route and the unit's
realized records are unchanged. Verdict: pass.

5. **DAG and report agreement.** The Lean statements, declaration names, proof dependencies,
proof origins, chapter, and unit in all three node records agree with the delivered files. The
report records one closed target hole and the two named split holes, with no hollow construction.
Verdict: pass.

I changed only this second-reading report section. No Lean source, statement, node, import, or
change record required repair.
