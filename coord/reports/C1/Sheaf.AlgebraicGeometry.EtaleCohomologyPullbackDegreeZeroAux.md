## What changed

Proved `AlgebraicGeometry.Etale.isIso_degreeZeroCohomology_cycles_factor` in
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZeroAux`, with its signature and
existing docstring unchanged. Two fully proved private helpers construct an
augmentation-compatible resolution comparison and show that a left exact additive functor
preserves degree-zero quasi-isomorphisms when the incoming differentials vanish.

The proof chooses an ordinary injective resolution, compares it to the arbitrary
K-injective complex by Mathlib's `Qh_map_bijective`, and transports the degree-zero
isomorphism through the resulting homotopy equivalence. The equality `hz` identifies the
specified cycle factor with the canonical homology map. Negative terms of the given
complex are handled by homotopy invariance, not assumed absent.

Added proof-only imports of `Mathlib.Algebra.Category.Grp.AB`,
`Mathlib.CategoryTheory.Abelian.Injective.Resolution`,
`Mathlib.CategoryTheory.Abelian.Injective.Extend`,
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`, and
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`. Updated the item's node proof,
proof dependencies and proof origin to match the implementation. No public interface,
definition, target statement, or other module changed. The item's node realizes no unit
statement or step; the unit route remains intact.

## Proved and sorry left

Proved the sole original sorry:
`AlgebraicGeometry.Etale.isIso_degreeZeroCohomology_cycles_factor`
(node `lem-weil-pbc-cohomology-pullback-degree-zero-iso-factor`).
Both private helpers are proved. No sorry remains in this module and no new sorry, module,
or node was introduced. Local compilation passes without warnings. The delivery dry run
also performs the axiom probe, server compilation and preflight.

## No longer needed

No original public import was removed: they supply the unchanged statement's objects and
instances. During development the proof-only import of
`Mathlib.CategoryTheory.Abelian.RightDerived` was replaced by the smaller injective
resolution import. The tentative import of
`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives` was removed: the existing source
Grothendieck sheaf instance and Mathlib's enough-injectives theorem suffice.

The original plan's `lem-weil-pbc-cohomology-pullback-functorial`
(`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`),
`prop-weil-pbc-cohomology-resolution-independent`
(`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective`), and
`lem-weil-pbc-module-sheaves-enough-injectives`
(`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`) are not needed by this proof.
Their imports were never added to the final module. The stronger D-plus representative
construction is unnecessary, but its node remains cited for the bounded-below-injectives
K-injectivity clause used by the ordinary resolution.

## Where the brief, the DAG or earlier work was wrong

The absence of `lean` records on the two injective-resolution dependencies is not a
missing statement: they have usable Mathlib matches. The resolution-independence lemma
recorded in the original plan supplies only an abstract homology isomorphism, with no
augmentation compatibility. Likewise geometric cohomology-pullback functoriality does
not supply that compatibility. The proof instead constructs the comparison morphism
and its augmentation homotopy directly from the existing Mathlib leaf
`lem-weil-pbc-kinjective-hom-derived`. No mathematical statement was disputed or changed.

Searches used the prescribed Lean Finder, Loogle and grep wrapper, and direct `rg` of the
project and pinned Mathlib. Relevant hits were the short-complex preservation results,
`Qh_map_bijective`, `quasiIso_iff`, `Functor.mapHomotopy`, and
`Homotopy.homologyMap_eq`; no direct theorem for the exact requested augmentation was found.

## Second reading by C1

1. Compared the entire delivered module with the repository version. The existing
   theorem signature is byte-for-byte identical, as is its docstring; no existing
   definition or declaration was changed. The only additions are two private proved
   helpers and five proof-only imports. No change record is needed. Verdict: pass.
2. Independently compiled the delivered file with `lcompile.py`: no errors or warnings.
   Scanned it for `sorry`, forbidden declarations and kernel-check bypasses: none.
   Compiled a scratch copy with `#print axioms` for the public theorem: exactly
   `propext`, `Classical.choice`, and `Quot.sound`. Read both helpers and the final proof:
   the comparison preserves the augmentation up to homotopy, and `hz` identifies the
   actual cycle factor before using homology naturality. Verdict: pass.
3. No statement was split off and no new public statement or node was added. The two
   proved private helpers have precisely the hypotheses their arguments need. In
   particular the comparison needs K-injectivity only of its target, while the
   left-exactness helper requires both incoming differentials to vanish; the main
   proof applies that helper only to the single complex and ordinary resolution.
   Negative terms of the arbitrary complex are not assumed zero. Zero objects and
   contractible negative summands cause no exception. Verdict: pass.
4. Rechecked the shorter-route search using different wording (`augmentation.*homotopy`
   and `quasiIso_map_of_preservesLeftHomology`) through the prescribed grep wrapper,
   and searched the project and pinned Mathlib directly. The existing right-derived-zero
   results concern the nonnegative resolution and still require the comparison used
   here for the specified arbitrary augmentation. Each added import supplies a used
   construction or instance: abelian-group Grothendieck axioms, ordinary injective
   resolutions, integer extension, Grothendieck sheaves in the required universe, and
   enough injectives. All remain proof-only. The three old dependencies omitted from
   the new proof are all listed under `No longer needed`. The item is absent from the
   unit's `realized` statement and steps, and the unit route is preserved. Verdict: pass.
5. Compared the node JSONs: only `proof`, `proof_deps`, and `proof_origin` change.
   Checked each of the six dependencies against its statement and Mathlib match;
   they account for the actual proof, including the bounded-below K-injectivity
   clause of the representative node. The proof-step uses have exactly the recorded
   union. No new nodes require review. Verdict: pass.

Second reading changed only this report, adding the independent checks above. No
repair to the Lean proof or DAG was necessary.
