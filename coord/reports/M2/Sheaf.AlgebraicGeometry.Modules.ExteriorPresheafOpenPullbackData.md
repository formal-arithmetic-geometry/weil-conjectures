## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exteriorPresheaf_open_pullback_data` with its
original signature in `Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullbackData`.
The proof follows the component-map route of its node. Private, fully proved helpers
construct scalar transport of exterior powers and an explicit presheaf restriction
adjunction for open immersions. No other existing module or public interface changed.
The node's proof and proof origin now describe the implemented argument; its proof
dependencies and the module's imports are unchanged.

The unit and counit of the presheaf adjunction are actual restriction maps, following
Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`. Their naturality and
triangle identities are proved from the presheaf laws. The exterior-power maps are
constructed by `exteriorPower.alternatingMapLinearEquiv` in both directions, with inverse
identities and naturality checked on pure wedges. Nothing chooses arbitrary data from
an unproved existence theorem.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exteriorPresheaf_open_pullback_data`
(node `lem-sc-exterior-presheaf-open-pullback-data`). Holes closed: 1. Holes added: 0.
There are no remaining `sorry`s in the delivered module or in any added module; no
modules were added. Every private helper is fully proved. This is a proof, not a
decomposition.

The module compiles cleanly using the prescribed `lcompile.py` wrapper within the
60-second file limit. The proof is uniform in the degree, including degree zero, and
requires neither nonempty opens nor nonempty schemes, finite generation, or local
freeness. The explicit maps also apply to zero modules and arbitrary coefficient rings.
`#print axioms` of the completed theorem reports exactly `propext`, `Classical.choice`,
and `Quot.sound`; no `sorryAx`. The final axiom-check compile took 24.6 seconds.

## No longer needed

None. The sole import, `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`, supplies the
objects and the proved exterior-power restriction formula, so it remains necessary.
No dependency node or module is bypassed. The unit's recorded route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or definition needed correction. The original one-step plan
left the presheaf pullback/restriction adjunction implicit; this delivery supplies its
unit, counit, linearity, naturality and triangle identities explicitly. Mathlib provides
the corresponding sheaf adjunction, but its presheaf version needed a local construction.
The cited blueprint markdown is absent in this clone; the unit record embeds its
proof text, and the declaration and node supply the determinant-paragraph source.

## Second reading by M2

1. **Visible interface: pass.** Compared the delivered module and node with the
   repository versions. The sole existing declaration,
   `AlgebraicGeometry.Scheme.Modules.exteriorPresheaf_open_pullback_data`, has a
   byte-for-byte identical signature and visibility. All added declarations are
   private helpers. The public import is unchanged; no existing definition changes.
   Only `proof` and `proof_origin` change in the existing node. No change record is
   needed.
2. **Proof and constructions: pass.** Independently compiled the exact delivered
   module with `lcompile.py`: clean, 31.6 seconds. Compiled an exact scratch copy
   with `#print axioms` appended: clean, 30.2 seconds, and exactly `propext`,
   `Classical.choice`, `Quot.sound`, with no `sorryAx`. Scanned every delivered
   declaration: no `sorry`, forbidden declaration or kernel-check bypass. Read
   both alternating-map constructions, their inverse identities, the explicit
   unit and counit, both naturality laws, and both triangle identities. Data is
   constructed explicitly. `restriction_wedge` uses the already proved
   `exteriorSheafRestriction_existsUnique`, whose unique wedge formula determines
   the chosen map; it does not extract an arbitrary witness from an open theorem.
3. **Split statements and edge cases: pass.** No statements are split off and no
   public statements are added. The private transport lemmas use only a ring
   isomorphism and an arbitrary module. Span induction includes zero and scalar
   multiples; in degree zero the single empty wedge still spans the exterior
   power. Nothing assumes a nonzero ring, a nonzero module, nonempty opens, or a
   nonempty scheme. The adjunction uses only image/preimage identities valid for
   every open immersion, including the empty open immersion.
4. **Route, searches and pruning: pass.** The top theorem first compares left
   adjoints, then uses sectionwise scalar transport, then checks naturality on
   pure wedges. Independent `msearch.py` grep and Loogle searches for restriction
   adjunctions and scalar-transport equivalences, plus `rg` searches of Mathlib,
   `lean/Sheaf`, `lean/WeilConjectures`, and the upstream module directory found
   no direct replacement. Mathlib's `restrictAdjunction` and
   `pushforwardPushforwardAdj` are sheaf-level constructions and do not apply to
   this generally unsheafified exterior presheaf. The existing exterior-power
   universal property and span theorem are already used. The sole public import
   supplies objects appearing in the original signature and is necessary.
   The old sole proof dependency `def-sc-sheaf-exterior-power` is used through
   `exteriorSheafRestriction_existsUnique`; none is pruned. Read
   `dag/units/sk-thm-picard-rr.json`: its `realized` fields are unchanged and this
   argument stays within the determinant-paragraph component-map route.
5. **DAG agreement: pass.** Read the item and dependency nodes. The item's three
   recorded steps match the explicit restriction adjunction, inverse scalar
   transport maps, and natural component isomorphisms in Lean. `proof_deps`
   remains the used exterior-power definition node; `proof_origin` names M2 and
   describes the implemented route without changing the source or statement.
   There are no new nodes or remaining holes to audit.

**Changes by the second reader:** added this independent review and its search and
compilation evidence to the report. No Lean or DAG repair was necessary.
