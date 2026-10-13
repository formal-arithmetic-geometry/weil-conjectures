## What changed

Proved `AlgebraicGeometry.Scheme.Modules.etaleZariskiDerivedSectionsAcyclicLeray`
in `Sheaf.AlgebraicGeometry.EtaleZariskiDerivedSectionsAcyclicLeray`, with its
existing signature and visibility unchanged. Added two private, fully proved helpers:
`pushforward_injectives` and `mapResolution`. The latter generalizes the explicit
private construction in `Sheaf.CategoryTheory.SiteLerayDegenerate` to different
object universes; that module is neither changed nor imported.

The proof applies the source library's universe-general flat left Kan extension
result directly to abelian groups, constructs the pushed injective resolution,
and compares the resulting section complexes. Naturality follows from Mathlib's
resolution comparison naturality and the complex-composition natural isomorphism.
The DAG proof and proof dependencies now describe this route. The unit route is
unchanged; `sk-prop-cd` has no realized statement or step being bypassed.

Added the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Functor.Flat`; retained all public imports.
The theorem-scoped unused-variable linter setting handles the original `hF` binder
in the existential function type, preserving that binder verbatim.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.Scheme.Modules.etaleZariskiDerivedSectionsAcyclicLeray`
(node `new-etale-zariski-derived-sections-acyclic-leray`).
No holes remain in the module; no holes were added or split off.
Both private helpers are fully proved. This is a proof, not a decomposition.

The single-file compiler succeeds without warnings. An explicit `#print axioms`
check of the public theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`; the temporary print command was removed afterwards. Hence the proof
also does not rest on a `sorry` in its imported declarations. All constructions
are uniform in zero coefficients and empty schemes.

## No longer needed

Removed these three proof-only imports and their corresponding proof dependencies:

- `Sheaf.Paper.ZariskiEtaleSheafLeftExact`
  (`lem-weil-pbc-zariski-etale-sheaf-left-exact`). Direct left Kan extension with
  abelian coefficients supplies the required finite-limit preservation.
- `Sheaf.CategoryTheory.SitePullbackAbelianUnderlying`
  (`lem-weil-pbc-site-pullback-abelian-underlying`). No transport through abelian
  group objects or underlying sheaves of sets is needed.
- `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`
  (`lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`). Mathlib's
  `InjectiveResolution.isoRightDerivedObj_hom_naturality` and its inverse form
  already provide the comparison naturality.

No essentially small etale-site model, Ext model, constant integer sheaf, or
free representable enters the proof. No claim is made that the three removed
modules are globally unreachable; they are unnecessary on this item's route.

## Where the brief, the DAG or earlier work was wrong

The planned underlying-set/group-object lift and essentially small site model
were unnecessary. Although the category of etale objects lives in a larger
universe, the left Kan extension indexing categories here use only the opens
and etale homs, so the existing universe-general flat-functor result applies
with `AddCommGrpCat.{u}` directly. The separate uniqueness-of-lifts dependency
is likewise unnecessary: Mathlib already proves the resolution naturality used
in the final square. No mathematical statement, definition, target, or public
interface was changed. No new nodes or forced adaptations were needed.

## Second reading by D4

1. **Interface preservation — pass.** Read the complete module and its diff
   against the repository. The existing theorem signature is byte for byte
   identical (also checked by extracting the text before `:= by`). Its docstring,
   visibility, namespace and public imports are unchanged. The only new
   declarations are private proof helpers. No statement, definition used by a
   target, or change record is added or altered.
2. **Proof and constructions — pass.** Independently compiled the delivered
   file without errors or warnings. A scratch copy with `#print axioms` for the
   public theorem and both private helpers reports exactly `propext`,
   `Classical.choice`, and `Quot.sound` for each. There are no `sorry`s or forbidden
   declarations. Read the degree-zero kernel proof, positive-degree homology
   vanishing, and both naturality squares. `mapResolution` constructs its complex
   and augmentation explicitly; `injectiveResolution` is Mathlib's proved
   construction, so no arbitrary data is selected from an unproved theorem.
3. **Split statements — pass, none.** No new public statement or lower hole was
   split off. The private helper's degree-zero case follows from kernel
   preservation independently of the positive-vanishing hypothesis; its successor
   case uses exactly that hypothesis. The construction and naturality also work
   for the zero sheaf, zero morphisms, and empty schemes. Independent Mathlib
   search for mapped injective resolutions and acyclic compositions found the
   existing resolution machinery, rather than an exact replacement theorem.
4. **Route and pruning — pass.** Read `SiteLerayDegenerate` and the upstream flat
   Kan-extension module. The former's analogous construction is private and uses
   equal object universes; its public result uses Ext and has a different
   conclusion. The direct abelian flat-Kan-extension route and Mathlib's
   comparison naturality avoid those extra requirements. Imports supply the
   signature's categories/instances or proof ingredients, and the added import
   is proof-only. All three old dependencies absent from the new proof are
   listed under `## No longer needed`. Checked `dag/units/sk-prop-cd.json`:
   no realized statement or step is bypassed, and the unit record is unchanged.
5. **DAG agreement — pass.** The node changes only `proof`, `proof_deps`, and
   `proof_origin`. Checked the dependencies' declaration/Mathlib attachments and
   that `proof_deps` is exactly the union of the proof steps' `uses`. The steps
   describe the actual direct finite-limit preservation, explicit pushed
   resolution, composite section-complex isomorphism, and naturality argument.
   No new node is required for a split statement because there is none.

Second reading changed only this report: added the independent checks and
verdicts. No repair to the Lean proof or node was needed. One original hole is
closed, zero holes are added, and zero statements are split off.
