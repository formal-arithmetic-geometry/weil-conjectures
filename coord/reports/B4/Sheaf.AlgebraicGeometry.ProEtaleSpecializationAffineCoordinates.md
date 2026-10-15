## What changed

Proved `AlgebraicGeometry.Scheme.specialization_affine_coordinates` in the assigned module. The proof imports the source-library Replete API for single-surjective-cover lifting and uses Mathlib's affine closed-immersion and quotient-kernel APIs. The former localization and dense-subsite imports were removed because the proof does not use their declarations.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.Scheme.specialization_affine_coordinates` (node `new-lem-weil-pbc-specialization-affine-coordinates`): 1 of 1 holes proved, 0 added, 0 split off. No `sorry` remains in the delivered module. Two private helpers, `split_affine_proetale_cover` and `quotient_specialization`, are fully proved. Compilation succeeds in about 8 seconds at the default heartbeat and time limits, with no warnings. `#print axioms` confirms the compiled declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization` and `Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv` from the module. The planned localization transport and generic dense-subsite equivalence are not needed: `AffineProEt.isLocallySurjective_iff_of_isSheaf` and the existing subcanonical singleton-cover argument provide the required evaluation transport directly. Pruned proof edges to `lem-weil-proetale-weakly-etale-localization`, `lem-pc-fppf-dense-sheaf-equivalence`, and `lem-weil-pbc-ind-etale-basis`; the last remains indirectly used by the existing single-cover criterion. These nodes may have other users. No unit statement or unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's first planned step was unnecessarily general. It prescribed construction of a slice-site equivalence and a dense affine restriction equivalence, although the source library already provides the exact single-surjective-cover characterization on the affine basis. The second planned step's quotient-coordinate argument is valid and was implemented directly with `RingHom.quotientKerEquivOfSurjective` and `Scheme.toSpecΓ_naturality`. Its cited Tag 01R8 concerns scheme-theoretic images; the affine closed-immersion quotient statement is Tag 01IH, now cited in the theorem docstring. The local Stacks TeX checkout is absent on this machine, so Tags 09AC and 01IH were read on the official Stacks website.

## New nodes

`lem-weil-pbc-affine-proetale-single-cover-local-surjectivity` records the already proved source-library declaration `AlgebraicGeometry.Scheme.AffineProEt.isLocallySurjective_iff_of_isSheaf` in `WeilConjectures.AlgebraicGeometry.ProEtale.Replete`. It adds no Lean module and no hole. The recorded LeanFinder, Loogle, and Mathlib grep searches found generic local-surjectivity infrastructure; LeanSearch was unavailable. The existing declaration and its full proof were read. This criterion concerns section lifting along one cover, not the closed inverse-image evaluation theorem, weakly contractible cover existence, or the dense-basis equivalence.


## Second reading by B4

1. **Unchanged interfaces: pass.** Read the complete diff against the shared repository.
   The existing `specialization_affine_coordinates` signature is byte-for-byte identical,
   including both evaluation universes, the actual kernel ideal, and both conclusions.
   Both public imports are unchanged; the new Replete import is proof-only. The only
   existing-node fields changed are `proof`, `proof_deps`, and `proof_origin`. There are
   no definition changes, change records, or adaptations of other modules.
2. **Kernel proof: pass.** Independently compiled the delivered file without errors or
   warnings (6.8 seconds). Compiled a scratch copy with `#print axioms` for the target,
   both private helpers, and the imported single-cover criterion: each uses exactly
   `propext`, `Classical.choice`, and `Quot.sound`. There is no remaining `sorry`, forbidden
   declaration mechanism, or data chosen from an unproved existence result. In particular
   `g` uses the explicit quotient-kernel equivalence and `l` is an explicit pullback lift.
3. **New statements: pass.** There are no split-off holes. Read Replete.lean lines 47-84,
   including the complete proof of `isLocallySurjective_iff_of_isSheaf`, and matched its
   sheaf hypotheses, every section, single surjective arrow, and lift equation with the
   new node. Its finite-disjoint-union proof handles the empty cover. Searched existing
   DAG statements for local-surjectivity/affine-cover formulations and Lean sources for
   Yoneda epimorphism/cover APIs; fresh msearch grep and Loogle searches found no shorter
   exact generic lemma for the private full-site cover argument. The existing criterion
   is reused, not restated in Lean. Tested the arguments conceptually at the identity
   cover, empty affine scheme/zero ring, identity closed immersion (kernel zero), and
   empty closed fibre; none needs nonemptiness, reducedness, or an extra hypothesis.
4. **Route and pruning: pass.** The evaluation argument first uses the already proved
   source-library criterion, then proves that its affine cover splits: affine source
   and target provide quasi-compactness for the full pro-etale singleton covering;
   subcanonical Yoneda and sheaf separatedness give the required epimorphism. The section
   equation yields `t ≫ q = 𝟙 B`, and naturality proves the lift equation. The geometric
   argument uses the closed-base-change instance and Mathlib's affine closed-immersion
   surjectivity theorem, then `toSpecΓ` naturality and continuity, with the correct
   specialization direction. Read Stacks [09AC](https://stacks.math.columbia.edu/tag/09AC)
   and [01IH](https://stacks.math.columbia.edu/tag/01IH); these support respectively the
   affine reduction and closed-immersion coordinate identification. Every old proof
   dependency omitted from the new direct edges is listed under `No longer needed`.
   Read `dag/units/sk-thm-properbasechange.json`: the projective-line, reduction, and
   torsion-assembly realized steps remain intact. The ind-etale basis remains used
   indirectly through the single-cover criterion; no unit step is bypassed.
5. **DAG agreement: pass.** The item's two proof steps describe the two actual branches
   and private helpers. The first cites the proved single-cover criterion and existing
   Mathlib subcanonicality leaf; the second cites closed-immersion base change and the
   closed-immersion definition. Their union is exactly `proof_deps`. The new node has
   the same chapter/unit, a concrete existing Lean declaration and verbatim signature,
   source lines, creation/blueprint records, and recorded searches with their actual
   results. It adds no Lean file or hole and is strictly below the item.

**Second-reader changes.** Left the Lean proof unchanged. Rewrote the new node's statement
in mathematical TeX and made its local-surjectivity meaning explicit, without changing
its content; marked its failed LeanSearch request `unavailable`. Added this independent
review. Holes closed remain `AlgebraicGeometry.Scheme.specialization_affine_coordinates`;
holes added: none; split off: none.
