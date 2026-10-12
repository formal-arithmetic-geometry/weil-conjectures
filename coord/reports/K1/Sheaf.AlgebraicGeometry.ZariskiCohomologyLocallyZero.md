## What changed

Proved `AlgebraicGeometry.zariski_cohomology_class_locally_zero` with its exact
original signature, following the four steps of Stacks Tag 01FW. Read the proof
at https://stacks.math.columbia.edu/tag/01FW because the local Stacks source files
are not regenerated in this clone.

The private `sectionEquiv` composes sheafification, free-forgetful, and Yoneda
adjunctions to identify maps from the sheafified free representable with sections.
Its proved naturality identifies both differentials and open restriction.
`InjectiveResolution.extMk_surjective` gives a section cocycle representing the
Ext-based cohomology class. Exactness of the resolution gives an epi onto the
kernel sheaf; kernel preservation gives the kernel section; local surjectivity
and the definition of the Zariski topology provide a neighborhood and a boundary
representative. `mk₀_comp_extMk` and `extMk_eq_zero_iff` identify the restricted
class and prove it zero.

All helpers are private and proved in the item module. No new modules or nodes
are delivered. The copied DAG node's proof and proof dependencies now describe
this implementation. The unit's route is unchanged: all four cocycle, exactness,
local lifting, and zero-boundary steps remain.

Replaced the unused public import of
`Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives` with direct Mathlib
statement imports. Added private proof imports for injective-resolution Ext,
local epimorphisms, and concrete abelian-group exactness. The change record is
`coord/changes/zariski-cohomology-locally-zero-imports.md`.

Searches through the launcher's LeanFinder, Loogle, and grep found no direct
local-vanishing theorem. Loogle and grep for `InjectiveResolution.extMk` found
its representation, precomposition, and boundary criteria, which close the
comparison rather than requiring a new sorried bridge.

## Proved and sorry left

Proved the sole original sorry:
`AlgebraicGeometry.zariski_cohomology_class_locally_zero`
(node `lem-weil-pbc-zariski-cohomology-locally-zero`). No sorry remains anywhere
in the delivered Lean file. No sorry is split off or introduced.

Single-file compilation succeeds. `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`, including all private helpers used by the
public theorem. The proof covers q=1 as well as higher degrees and all schemes;
for an empty scheme the point binder has no inhabitants. It needs no extra
hypotheses on the sheaf or scheme.

## No longer needed

Removed import `Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives` and
proof dependency `lem-weil-pbc-zariski-open-restriction-injectives`.
Computing object cohomology on an open in the original site avoids restricting
the resolution to the site's open subscheme. Its statement dependency remains
in the node because the original natural-language statement also explains that
interpretation; no statement is changed. This pruning is below the unit level.

The extension-by-zero adjunction, its exactness, and preservation of injectives
are no longer reached through this module's former restriction import. They
may still be needed by other branches. The remaining original proof-dependency
nodes are all used: the Zariski site and cohomology definitions, injective
resolutions, exact sequences, kernel preservation, epi kernel lifts, and local
surjectivity of abelian-sheaf epimorphisms.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's claimed obstruction was an API gap that can be closed
from existing Mathlib declarations. The section/Hom adjunctions connect
`cohomologyPresheaf` directly to `InjectiveResolution.extMk`. The explicit
local-lifting theorem also follows from existing kernel, exactness, epi, and
covering-sieve APIs. Both bridges are fully proved here.

The DAG's use of restriction preserving injectives in its final step is
unnecessary for the target's actual `cohomologyPresheaf` restriction map.
The proof computes cohomology over U inside the original site, then uses
naturality of Ext precomposition. This removes that dependency without changing
any binder, conclusion, definition, or unit-level step.

## Second reading by K1

1. Compared the delivered module and node with the read-only repository using
   `diff`. Independently checked that the original theorem signature through
   `:= by` is byte for byte identical, and that every non-proof node field is
   unchanged. The only public-interface difference is the documented import
   pruning, covered by the existing change record. Verdict: pass.
2. Read every helper and the final proof. Local single-file compilation succeeds
   without warnings. An independent scratch-copy `#print axioms` for the public
   theorem reports only `propext`, `Classical.choice`, and `Quot.sound`; this
   includes the entire dependency closure of its private helpers. There are no
   sorries, axioms, unsafe or opaque declarations, external implementations,
   or hollow definitions. The adjunction equivalence, its naturality, Ext
   representative and boundary criteria, kernel lift, and covering-sieve
   neighborhood selection all implement the claimed argument. Verdict: pass.
3. No statement is split off and no node or module is added. The proved private
   helpers are genuine parts of the argument, not a renamed target. Checked
   degree one (n=0 uses exactness at I^1), higher degrees, and the empty scheme
   (there is no point x). No extra assumptions enter the theorem. Verdict: pass.
4. Read Stacks Tag 01FW and checked its cocycle, exactness, local-lift, and
   boundary steps against the Lean. Repeated LeanFinder search with
   "sheafification of positive degree cohomology presheaf is zero", Loogle
   search for local surjectivity, and grep for locally exact image sieves;
   searched both Lean library roots. No direct replacement for the target was
   found. The upstream local-exactness theorem in FlatLocalRelations uses
   ModuleCat coefficients, so it does not shorten this AddCommGrpCat proof
   without a new comparison. Statement imports supply Scheme, injective
   resolutions and cohomology; the added proof imports remain private.
   `No longer needed` lists the sole removed original proof dependency,
   lem-weil-pbc-zariski-open-restriction-injectives, and its import. Read
   dag/units/sk-thm-p1.json and its realized route: this item is below its
   realized steps, and no unit route is bypassed. Verdict: pass.
5. Checked the node's four proof steps, proof_origin, and proof_deps against
   the implementation. The union of step uses equals proof_deps. The original
   statement and stmt_deps remain unchanged, including the explanatory
   open-restriction reference. There are no new nodes requiring metadata.
   Verdict: pass.

Changed only this report by appending the independent second reading. No Lean,
DAG, or change-record repair was needed.
