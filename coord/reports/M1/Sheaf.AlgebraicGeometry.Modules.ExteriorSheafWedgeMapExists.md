## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_wedgeMap_exists` in
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists`, preserving its complete
signature and original docstring. Added three private, fully proved helpers: the exterior
restriction formula, explicit bilinear multiplication between graded exterior powers, and
its pure-wedge formula. There is no witness selected from an unproved existence theorem.

The sectionwise map composes exteriorPower.map, exterior-algebra multiplication, and the
target sheafification unit. Naturality is checked on concatenated pure wedges and extended
by span induction in both factors. The existing bilinear sheafification extension and sheaf
tensor universal property then give the requested morphism and section formula. Added only
proof imports of `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`
and `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.

Updated `lem-sc-exterior-sheaf-wedge-map` proof, proof_deps, and proof_origin to record the
explicit multiplication and the two generic descent tools. No public interface changed.
The unit `sk-thm-picard-rr` and its determinant route remain unchanged.

Searches: LeanFinder found exteriorPower.map_apply_ιMulti and exterior-algebra multiplication;
Loogle found ExteriorAlgebra.ιMulti_mul_ιMulti. Grep of Mathlib and the two library roots
found no existing sheaf wedge multiplication. The graded-product construction avoids writing
two separate alternating-map universal-property constructions.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_wedgeMap_exists`
(blueprint: `lem-sc-exterior-sheaf-wedge-map`).

There are no remaining sorries in the item and no new sorries or nodes. This is a proof,
not a decomposition. The two generic sheaf theorems used are already proved in the library.
The final single-file compile succeeds without warnings. The delivery dry run additionally
checks the axioms of every declaration in the delivered module.

Edge cases: no division, basis, injectivity, or rank assumption occurs. The multiplication
construction uses pow_add for arbitrary natural degrees, including either or both zero.
The pure-wedge formula uses Fin.append and Fin.addCases, including empty blocks, and does
not assume any ring characteristic or that the scheme is nonempty.

## No longer needed

None. Both original public imports are required by the statement. The original sole proof
dependency `def-sc-sheaf-exterior-power` is still used. No planned node or existing module
was bypassed or pruned; the two proof imports are both used.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The DAG's informal two-block linearization can
be implemented more directly by multiplication in the exterior algebra. Its descent step
is supplied by the already-proved bilinear sheafification extension, and the tensor step by
the already-proved sheaf tensor universal property. These generic tools were not listed in
the old proof_deps, so the node now names them explicitly.

## Second reading by M1

1. **Interface unchanged — pass.** Read the complete repository/sandbox Lean diff.
   The only existing declaration, `exteriorSheaf_wedgeMap_exists`, has a byte-for-byte
   identical signature and docstring. Its scheme, arbitrary morphism `f`, natural degrees,
   equality `ht`, existential morphism and formula on every open and both tuples are
   preserved. No target, public definition, visibility, or public import changed; there
   are no change records or forced adaptations.
2. **Proof and construction — pass.** Independently compiled the delivered file without
   errors or warnings (49.5 seconds). Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_wedgeMap_exists` (46.2 seconds): exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. No prohibited
   declaration or `sorry` occurs in the file. `wedgeMul` constructs the subtype element
   `x.val * y.val`, whose membership follows from `pow_add`; all four linearity proofs
   are supplied. `restriction_wedge` uses the specified unique restriction, not an
   arbitrary existence witness. The existential bilinear family and tensor morphism
   are eliminated inside a theorem proof, not used as data of a public definition.
3. **Split statements and edge cases — pass, none split off.** No new public statement,
   node, or hole was added. Checked the private product formula against Mathlib
   `ExteriorAlgebra.ιMulti_mul_ιMulti` (Basic.lean, lines 321 onward), and the exterior
   power definition (lines 79–80). Degree zero is the zeroth submodule power, and empty
   tuple blocks are included by `Fin.append`; both zero degrees, zero modules and zero
   rings need no extra assumption. The generic sheafification and tensor theorem
   signatures were read in full: their naturality and unit/pure-tensor equations are
   exactly the equations used by `hβ`, `hβunit` and `hψ`.
4. **Route and pruning — pass.** Read the original dependency `ExteriorSheaf`, the
   `tmulSection` definition in `TensorSection`, and both added proof-import modules.
   Both original public imports occur in the signature; both new private imports are
   used. Searched the scheme-module library for wedge/exterior multiplication and
   inspected Mathlib exterior-power multiplication infrastructure; no existing sheaf
   multiplication gives a shorter application. The small explicit multiplication
   helper already uses Mathlib's concatenation lemma. Restriction compatibility is
   checked by naturality on each tuple block and then by two span inductions, including
   the semilinear scalar cases. The old sole dependency
   `def-sc-sheaf-exterior-power` remains used, so `## No longer needed` is complete.
   Read `dag/units/sk-thm-picard-rr.json` and the imported determinant paragraph preserved
   in `lem-sc-riemann-roch.json`: this remains the wedge construction below determinant
   multiplicativity, not a replacement of the RR induction. The unit's `realized`
   record is unchanged (its existing entries are empty). The source Markdown is not
   installed on this machine; the preserved imported proof text was used for this check.
5. **DAG agreement — pass.** Compared the entire node JSON with the repository version:
   only `proof`, `proof_deps`, and `proof_origin` changed. Step 1 matches `wedgeMul`,
   `exteriorPower.map` and `hb`; step 2 matches `hpure`, `hfirst` and the second span
   induction; step 3 matches the two descent applications and the final transitivity
   chain. The two new dependency ids record precisely the public generic theorems
   applied. Their node statements and Lean records were checked against their modules;
   they supply descent tools and do not replace a unit step. The node's recorded Lean
   signature remains identical to the delivered declaration. No new nodes need fields.

Changes made in this second reading: appended this independent review only. The Lean
proof and node metadata required no repair. One original hole is closed, zero holes are
added, and zero modules are pruned.
