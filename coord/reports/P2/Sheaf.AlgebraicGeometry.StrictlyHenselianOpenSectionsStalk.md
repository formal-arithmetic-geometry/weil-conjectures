## What changed

Proved `AlgebraicGeometry.Scheme.strictlyHenselianOpen_toPresheafFiber_bijective` in
`Sheaf.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk`, with its statement unchanged.
Added one proof-only import, `WeilConjectures.RingTheory.ProEtale.HenselianLocalRing`.
The original public imports and all public signatures remain unchanged.

Two fully proved private helpers implement the geometric argument:
`exists_pointed_section_spec` shrinks to an affine neighbourhood and identifies its
localization at the marked prime with the strictly henselian base using Olivier's theorem
(Stacks 092Z); `strictlyHenselianOpen_pointedSection` applies this construction to the
pullback over the open U. The ring map into Ω extends to that localization, which verifies
the prescribed geometric point exactly. The main proof combines these sections with
Mathlib's germ representatives, equality criterion, functoriality, and the monomorphism U.ι.
This follows the section construction of Stacks 03QO; the unit's route is preserved.

Updated the item's node to describe the compiled proof and its actual dependencies.
Attached the already proved source declaration
`Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing` to the existing node
`thm-weil-pbc-weak-etale-strict-local`. Its statement is exactly Stacks 092Z; no new node or
source-library module was needed. The references were checked at
https://stacks.math.columbia.edu/tag/03QO and https://stacks.math.columbia.edu/tag/092Z.

## Proved and sorry left

Proved the only original sorry:
`AlgebraicGeometry.Scheme.strictlyHenselianOpen_toPresheafFiber_bijective`
(node `lem-weil-pbc-sets-strictly-henselian-open-sections-stalk`).
Both private helpers are also fully proved. There is no sorry left or added anywhere in
the delivery, and no intermediate statements were split off.

Local compilation passed. `#print axioms` for the main theorem and Olivier's source
lemma reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
Both added-import candidates were checked for cycles; the redundant import was removed
and the final module compiled again without warnings.

Edge cases: with U = T = Spec R, the construction is precisely the closed-point section
argument. For arbitrary Ω, equality of the geometric morphisms follows from the localized
ring-map calculation and does not assume Ω equals the residue field. No separatedness of
the étale neighbourhood is assumed. Empty U cannot satisfy the given affine isomorphism
with a local ring. In fact the proof uses no sheaf condition and works for presheaves too.

## No longer needed

The following old proof dependencies, including their modules, are not used by this proof:

- `lem-weil-pbc-etale-algebra-residue-field-separable`: Mathlib residue-field instances.
- `lem-pc-sepclosed-finite-sep-trivial`: Mathlib `IsSepClosed.algebraMap_bijective`.
- `lem-weil-pbc-henselian-local-root-lifting`:
  `Sheaf.RingTheory.HenselianLocalRootLifting`.
- `lem-weil-pbc-root-lifting-etale-retraction`:
  `Sheaf.RingTheory.RootLiftingEtaleRetraction`.
- `lem-weil-pbc-colimit-initial-full-subcategory`: Mathlib cofinality/colimit lemmas.
- `lem-weil-pbc-colimit-constant-connected-diagram`: Mathlib constant connected colimits.

The affine shrinking and pointed-neighbourhood cofilteredness nodes remain dependencies.
Olivier's theorem replaces the residue-field/root-lifting steps, and the existing stalk
representative/equality API replaces the singleton-subcategory colimit calculation.
These are local removals from this proof, not claims that other targets cease to use them.

No base imports were removed: both public imports are needed by the statement.
The provisional proof-only import `WeilConjectures.Mathlib.RingTheory.Etale.Weakly` was
removed after compilation showed it is already available through the remaining import.

## Where the brief, the DAG or earlier work was wrong

The DAG's original route is mathematically valid but longer than necessary: the source
library already proves Olivier's local weakly étale isomorphism theorem, while its DAG
node had no Lean record. Attaching that declaration permits a completely proved section
construction without importing unfinished root-lifting statements. The main theorem's
existing docstring describes the original plan; the updated DAG and private helper
comments describe the implemented shorter route. No statement or definition was corrected.

## Second reading by P2

1. Interface: PASS. Independently diffed the sole delivered Lean module against the
   repository. The existing theorem signature is byte for byte identical, its docstring
   is unchanged, and both public imports are unchanged. The only added import is private
   to the proof. There are no definition or statement changes needing a change record.
2. Proof: PASS. Compiled the final module through `lcompile.py` without errors or
   warnings. Scanned it for sorry and all forbidden declarations: none occur. Refreshed
   the scratch axiom check from the exact final file and checked both private helpers,
   the main theorem, and the imported Olivier lemma independently: each uses precisely
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Read the ring-map
   identities and the pullback transport, including the equality of geometric morphisms;
   injectivity correctly uses the monomorphism U.ι, and surjectivity uses stalk
   representatives and their naturality.
3. Splits and edge cases: PASS. No statements are split off and no nodes are new. The
   proved private helpers are genuine parts of the argument, not restatements. Checked
   Spec R as the identity open, arbitrary field Ω in the affine helper, and arbitrary
   (possibly nonseparated) etale X. The geometric point prevents the empty affine
   neighbourhood case. Localization at q is local, the contraction condition supplies
   the local ring homomorphism, and the kernel calculation in Ω supplies exactly the
   units needed to extend the geometric point to the localization.
4. Route and pruning: PASS. Independently searched `lean/Sheaf`, the upstream geometry
   library, Mathlib EtalePoint, and Point.Basic for section and germ results. Compared
   `Scheme.exists_section_of_etale_of_isStrictlyHenselianLocalRing` in the upstream
   Sites.StrictlyHenselian module: it concludes only existence of a section, without
   fixing the given geometric point, so it does not directly replace this helper. The
   implementation already uses the proved Olivier theorem and Mathlib's stalk API.
   Both public imports are needed by the signature; the single proof import supplies
   Olivier and weakly etale localization. The six removed old proof dependencies are
   all listed under No longer needed. Read `dag/units/sk-thm-iff.json`, including its
   realized statement and step: this subsidiary computation preserves the degree-zero
   comparison route. The closed Olivier theorem is a tool, as SETUP.md permits.
5. Nodes: PASS. Independently compared both delivered JSON files with the repository.
   Only proof, proof_deps, and proof_origin change on the item's node, and only lean
   changes on the existing Olivier node. The item's proof_deps equals the union of
   the steps' uses; the affine shrinking and cofilteredness references match their
   Mathlib records. The attached Olivier declaration has exactly the local weakly
   etale hypotheses and bijectivity conclusion of its node. No new-node fields apply.

Second-reading changes: appended this review report and regenerated the scratch axiom
check against the final import set, adding checks of both private helpers. No delivered
Lean proof, statement, import, or DAG repair was necessary.
