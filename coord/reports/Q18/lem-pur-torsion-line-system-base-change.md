## Worker report

This delivery states `lem-pur-torsion-line-system-base-change` in
`Sheaf.AlgebraicGeometry.TorsionLineSystemBaseChange`, namespace
`AlgebraicGeometry.ProEtaleTorsionSystem`. The node statement, statement dependencies,
proof and proof dependencies are unchanged. No new nodes or dependency-record changes are needed. Identity-normalized helpers
for the final internal interpretation are declared in the item module itself,
as requested by H13 at immutable head 33a04e77f0b2.

Source read: Stacks `sites-modules.tex`, section 03EK, lines 3550–3685 (the definition,
0GMW, the bilinear universal property and 03EL), and the current blueprint
`main-20261015/blueprint/sec-smooth-purity/sk-prop-an/` files
`sk-prop-sfb-cartesian-coefficients-twists.md` and its proof, especially “Finite A”.
The generic torsion-system lemma does not assume that the systems are roots of unity:
therefore it does not need the parent's hypothesis that ell be invertible on the schemes.
Its prescribed system isomorphisms are hypotheses instead. Neither rank one nor local
freeness occurs in the node or the Lean statement.

Hypotheses and objects, clause by clause:

- Any scheme morphism: `{X Y : Scheme.{u}} (h : X ⟶ Y)`. No finite-type, characteristic,
  nonemptiness, separation or invertibility hypothesis is added.
- Small pro-etale sites and the specified inverse image: the imported `Rings`, `Modules`,
  `inverse`, `inverseSection`, `moduleSetsIdentification`, and `moduleMapSets` of
  `AlgebraicGeometry.ProEtaleTensorComparison` are transparent wrappers around the recorded
  constructions. The original site has object universe u+1 and Hom universe u. Coefficients
  and sections have universe u+1; no equality of site object and Hom universes is imposed.
- Prime ell: `(ell : ℕ) (_hell : ell.Prime)`.
- A_T: `constant T A` is exactly `constantSheaf` in commutative rings, not the presheaf
  of constants and not an independently chosen sheaf. `constantMap` is that functor's map.
- Gamma_A: `gamma h A` is the existing `proEtaleConstantInverseImageMap` in commutative
  rings. The finite-ring comparison node identifies this map with its isomorphism.
- Positive exponents: `r : ℕ+` includes exactly r >= 1. `residue ell r` is the canonical
  ULift of ZMod (ell^r) into the section universe; `reduction` is ZMod.castHom conjugated
  by ULift.ringEquiv. The lift changes no residue ring or scalar map.
- P_{T,r}, semilinear q_{s,r}: `System.obj` and `System.q`. A q is a module morphism into
  `restrict` along the actual constant reduction map; this says exactly that it is additive,
  natural in site objects, and semilinear over reduction. `System.identity` and
  `System.composition` give the identities on all local sections, equivalently on sheaf maps.
- The induced reductions are isomorphisms: `System.reduction_iso` supplies an iso from
  the existing sheafified scalar extension and pins its map on every x tensor b to
  b times q(x). This specifies the induced map, not an arbitrary iso of its endpoints.
- The semilinear c_r: the input c is an iso from `inverse h R` of PY_r to
  `restrict (gamma h R)` of PX_r. Its type includes precisely gamma-semilinearity.
- Compatibility with q: `_hc` is the equality of the two sheaf-map composites after the
  existing unit-normalized underlying-set identifications. It is the stated equation
  c_r h^{-1}(q_Y) = q_X c_s. Forgetting to set sheaves is faithful and does not weaken it.
- Every finite commutative A killed by ell^r: `Coefficient` bundles the positive exponent,
  a `CommRingCat.{u+1}` ring, `Finite` and the equation `(ell^r : A) = 0`. This equation is
  equivalent to ell^r A = 0 (evaluate annihilation at 1 for the converse).
  `Coefficient.scalar` constructs the unique unital residue-ring map using
  `ZMod.castHom (ringChar.dvd killed)`, never an extra algebra assumption.

Conclusions, clause by clause:

- `extension P a` is exactly `SheafOfModules.changeOfRings` for the canonical residue-to-A
  sheaf map. This is sheafification of sectionwise A tensor P. The function `pure` evaluates
  its actual module-sheafification unit on a tensor x, and writes its arguments as x,a;
  commutative tensor symmetry identifies this with the node's P tensor A convention.
- `comparison_exists` states existence and uniqueness of a gamma_A-semilinear iso with
  predicate `IsNormalized`. This predicate is the exact local formula in the node:
  inverseSection(x tensor a) maps to c_r(inverseSection x) tensor gamma_A(unit a).
  All V and all their sections are quantified; no assertion that arbitrary pulled-back
  sections are individual unit sections is used.
- `comparison` selects that uniquely characterized iso. The main theorem asserts its
  normalization and that every iso with this normalization equals this one.
- `transition_exists` gives the unique semilinear sheaf map for every a,b, exponent
  inequality and unital coefficient morphism v, with the formula x tensor a mapped to
  q(x) tensor v(a). The node's proof step 4 supplies its complete docstring proof.
  `transition` selects this uniquely specified arrow. No arbitrary transition is assumed.
- The main theorem's first conjunct is the FULL square of sheaf maps for every such
  mixed transition, using `transitionSets` and `underlyingBaseMap` to expose both endpoints.
  This includes coefficient-only maps by equal exponents and exponent-only maps by v=id.
- `DiagramLaws PX` and `DiagramLaws PY` state identity and composition for these very
  arrows, and that `transition P a (a.atExponent r hr) hrs (𝟙 a.ring)` is an isomorphism.
  Thus the asserted independence of exponent concerns the normalized transition itself.
- Every underlying comparison is invertible (the explicit IsIso conjunct). Together with
  the full transition square and diagram laws, this is exactly an isomorphism of the
  varying-scalar diagrams. Its inverse squares follow by composing with component inverses;
  no extra choice of diagram is made.
- The final conjuncts are now `InternalComparisonAgreement h PX PY c a` and
  `InternalTransitionAgreement P a b hrs v` on X and Y. Each asserts the actual
  `Mod.Hom.hom` equals `(SheafOfModules.toSheaf _).map` of C or D. There is no
  counit in either equality. The internal source and target have exactly the
  original underlying abelian sheaves, by the data of `identitySectionModule`.
- Each final predicate ALSO states the formula on internal pure tensors for that
  specific comparison or transition. For C it is c_r(x) tensor gamma_A(a); for D
  it is q(x) tensor v(a). Both use `internalPure`, which evaluates the actual
  `comparison_internalTmul` of the internal relative tensor and then the fixed
  `internalExtensionComparison`. That comparison is uniquely characterized by
  sending every internal coequalizer pure tensor to the ordinary scalar-extension
  pure tensor, by `internalExtensionComparison_exists`. It is constructed using
  the existing normalized internal/section tensor comparison and scalar-extension
  universal property; no arbitrary isomorphism or arbitrary map is selected.
- The base-change formula quantifies over all original Y objects and sections,
  then uses the existing `inverseSection` at their base changes. It does not
  assume arbitrary inverse-image sections are unit images. Both coefficient
  actions are preserved: the scalar module is the actual coefficient sheaf with
  its restricted residue action; the coefficient factor carries its extra A-action.
- `internalRing` and `sectionCoordinates` retain the recorded internal ring on
  the actual underlying abelian sheaf, with ring coordinates fixed to identity
  on every local section. The repair adds no structure assumption or universe
  equality.

Dependency declarations used (the listed source signatures and docstrings were read):

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`,
  `proEtaleConstantInverseImageMap`, `proEtaleModuleInverseImage`, `proEtaleBaseChange`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientInverseImageMap_isIso` and its
  `finiteCoefficientConstantComparison` / constant-section comparison clauses.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, through
  the imported `Modules` abbreviation; no scheme-only substitute is used.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` at independent site universes, and its
  public imports `SheafOfModules.changeOfRings`, `changeOfRingsPresheaf`, and the tensor API.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf`, `sectionModuleEquivalence`.
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`:
  `CategoryTheory.InternalAbelianSheafModule.internal_section_tensor_comparison`,
  `comparison_internalTmul`, `comparison_sectionTmul`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`:
  `AlgebraicGeometry.ProEtaleTensorComparison.inverseImage_tensor_comparison`, and the
  constructions `inverseSection`, `moduleSetsIdentification`, `moduleMapSets`, `restrict`.
- Proof imports: `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
  (`SheafOfModules.tensor_bilinear_universal`),
  `Sheaf.CategoryTheory.SheafificationTensorLocalIso`
  (`CategoryTheory.sheafification_tensor_local_iso`). The other proof modules for
  sheafification and sheaf tensor are already public dependencies of these imports.
- `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`:
  `CategoryTheory.Sheaf.monObj_sheafCompose_obj`,
  `CategoryTheory.Sheaf.isCommMonObj_sheafCompose_obj` (used directly, not reproved).
- `def-weil-size-convention` has an explicit convention record: its universe policy is
  rendered directly by universe u, the small sites, and section/coefficient universe u+1.

The item's seven postponed theorems are `transition_exists` (step 4),
`comparison_exists` (steps 1–3), `sectionCoordinates_exists` (ring coordinates in
step 8), `internalExtensionComparison_exists` (internal tensor normalization in
step 8), `torsion_line_system_base_change` (all eight steps),
`identitySectionCoordinates_exists`, and `identitySectionModuleMap_hom` (step 8).
Each is in the item module, has this node's blueprint marker, and has a complete
natural-language proof in its docstring. Every theorem proof is `sorry`. Definitions contain actual data;
choices are only from uniquely normalized constructions.

Edge cases checked mathematically against the signatures: r=1; s=r with reduction the
identity; identity coefficient maps and composites; the zero coefficient ring and zero
systems; an empty X or Y (the ring and module sheaves then have singleton section sets);
arbitrary nonfree and nonflat P; rings killed by a smaller power than the specified one;
ell equal to the residue characteristic; and unequal site object and Hom universes.
Nothing requires a nonzero coefficient ring, an invertible ell on a scheme, a free module,
a nonempty site, or a minimal annihilating exponent. There is no statement dispute.

Searches (2026-10-21):

- msearch LeanFinder: “Inverse image of compatible torsion module sheaf systems commutes
  with tensor extension to finite rings naturally in coefficients and exponents”. Eight
  results included LightCondensed monoidal structure, AdicCompletion tensor naturality,
  lTensor.inverse_of_rightInverse and presheaf tensor maps; none states this node.
- msearch Loogle: `SheafOfModules.changeOfRings, SheafOfModules.restrictScalars` returned
  zero hits and “unknown identifier SheafOfModules.changeOfRings”. The actual upstream
  scalar-extension declarations were then opened and used directly.
- msearch grep in Algebra/Category/ModuleCat: `torsion.*[Ss]ystem|[Tt]orsionLine|changeOfRings`
  returned 14 change-of-rings import/notation hits, no compatible torsion-system theorem.
- msearch LeanSearch: “Pullback of tensor extensions of compatible torsion module sheaves
  is natural in coefficient rings and exponents”. Eight results were generic module
  pullbacks, their adjunction and TensorProduct.map; no normalized system theorem.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for torsion-system patterns and the
  exact node id: only unrelated torsion local systems and group-scheme Tate modules.
  A further full-name search for ProEtaleTorsionSystem, torsion_line_system_base_change,
  and sectionCoordinates_exists found no collision in these trees or dag/lean_names_upstream.
- API searches found and reused the existing SiteTensorFunctoriality, RingedSiteModules,
  TensorProduct changeOfRings, RingPresheaf internal ring construction, and
  InternalAbelianSheafModuleEquivalence/InternalSectionTensorComparison. None was copied.

## Repair of H13 at 33a04e77f0b2

The returned packet replaced the landed record of
`def-weil-pbc-internal-abelian-sheaf-module-equivalence` with a record whose
principal declaration was only an identity-normalized inverse construction.
That did not state the dependency's equivalence and dropped the published
`sectionModuleEquivalence` binding used by existing consumers.

Following the first permitted correction in the return, the dependency node copy
and `InternalAbelianSheafModuleIdentity.lean` are removed from this packet.
The item imports the original `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
directly. Its module, declaration, statement, declarations and all other fields
remain exactly as on live main: this delivery does not carry or replace that node.
No live dependency source is changed, so all its existing consumers retain the
same interface.

The five helpers `identitySectionModule`, `identitySectionCoordinates_exists`,
`identitySectionCoordinates`, `identitySectionModuleMap`, and
`identitySectionModuleMap_hom` now belong to
`Sheaf.AlgebraicGeometry.TorsionLineSystemBaseChange`. Their full names remain in
`CategoryTheory.InternalAbelianSheafModule`, so their accepted mathematical
signatures and all consumer expressions in the item are unchanged. Each helper
has the item's blueprint marker and is listed in the item's `lean.declarations`.
The two postponed theorems have the same complete proof docstrings.

`identitySectionModule J R M` transports the action of the existing
`liftedSheafModule J R M` along the underlying abelian-sheaf isomorphism of
`sectionModuleFunctor_counit`. Its X field is literally
`(SheafOfModules.toSheaf _).obj M`; `ModObj.ofIso` supplies the actual transported
action. `identitySectionCoordinates_exists` uniquely fixes identity on every
section, and the fully faithful section functor lifts each morphism through
these coordinates. `identitySectionModuleMap_hom` specifies exactly the original
underlying abelian-sheaf map. These helpers implement proof step 8 of the item;
they do not replace or restate the dependency's equivalence.

The accepted F1/H3/H5 substance is retained: `InternalComparisonAgreement` and
`InternalTransitionAgreement` still give identity-identified underlying maps
and the arrow-specific c tensor gamma and q tensor v formulas on internal pure
tensors through the uniquely normalized `internalExtensionComparison`.
The main theorem signature and every ordinary-system clause are verbatim from
the retained packet. No field outside the item's `lean` changes.

## Second reading by Q18

I reread the returned H13 entry, both retained module bodies, the landed
`InternalAbelianSheafModuleEquivalence` interface and the final item source.
The existing `sectionModuleEquivalence` is the dependency's principal declaration;
its inverse's choice counit is used only to construct the transported action.
The final identity formulas refer to the real original sheaves and maps, with
no equality of a chosen counit with identity assumed.

I rechecked the item against the hypothesis and clause correspondence above:
`System` still requires semilinear q, identity, composition and the specified
induced reduction isomorphisms; c and hc have precisely their old types.
`Coefficient` still includes the zero ring and every positive annihilating
exponent. `comparison_exists` gives the uniquely normalized gamma-semilinear
isomorphism, `transition_exists` gives every mixed q tensor v arrow, and the
main square quantifies over every such arrow. `DiagramLaws` includes the
specified exponent arrow's invertibility. The final internal formulas retain
the separate c tensor gamma and q tensor v evaluations. The local generic
helper section binds its independent site universes explicitly and closes
before the scheme-specific declarations.

The zero-ring, empty-scheme, equal-exponent, identity/composite coefficient-map,
nonfree and nonflat cases remain included. The relocation adds no hypotheses,
changes no objects or scalars, and introduces no statement correction.

The saved-packet dry run requested at the start passed with commit 24a5061587e.
That mechanical pass still contained the returned H13 record replacement; the
present repair removes that replacement rather than repushing it unchanged.
The combined module was checked with the prescribed 60-second scompile.py limit.
The sandbox attempt timed out; automatic confirmation against current server
sources compiled the actual module cleanly in 58.6 seconds (exit 0 overall),
with nice 19, two threads and the unchanged 60-second limit. No compiler errors
or unexpected warnings remained. The final file contains no profiling options.
Selected pure-tensor and canonical-map definitions are marked irreducible to
avoid unnecessary unfolding while preserving their data, types and formulas.
The complete main signature matches `lean.statement` verbatim; all lines are at
most 100 characters; every non-lean item field matches the current read clone.
Exactly the item module and item node remain in the packet, plus this report.

The mandatory repaired-packet dry run passed (exit 0):
“OK (dry run): commit 21734ecc760 passes the preflight and compiles; nothing pushed”.
Its staged set is exactly the item module, item node and this report. It includes
no dependency node or dependency module, so the landed equivalence binding and
all its metadata are preserved. Server confirmation again passed after a sandbox
timeout under the default limit. The prescribed delivery follows this dry run.
