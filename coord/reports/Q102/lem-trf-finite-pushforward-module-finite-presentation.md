# Q102: finite pushforward and finite presentation

## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePushforwardModuleFinitePresentation`
states
`AlgebraicGeometry.Scheme.Modules.finitePresentation_near_and_stalk_iff_pushforward_of_singleton_fibre`.
Its sole proof is `sorry`. It introduces no definitions and changes only the
item's `lean` record. The existing NW delivery was a stage-1 split, with no Lean
binding; its completion does not supersede this stage-2 assignment. The previous
attempt's unchanged-item preflight failure is addressed by supplying the Lean
statement and its actual node binding.

I read the full six-step DAG proof, every statement dependency and its recorded
Lean interface, Stacks `flat.tex`, lemma-devissage-finite-presentation (057T),
including both the neighbourhood and stalk paragraphs; `descent.tex`,
lemma-finite-finitely-presented-module (05B4); and `more-morphisms.tex`,
lemma-finite-morphism-single-point-in-fibre (05B8), all four clauses and its proof.
The node's source description retains obsolete tag references 03C4 and 0A1H;
its actual proof, NW report and the source labels identify the correct 05B4 and
05B8 passages. The module names the correct passages without changing `source`.
No mathematical statement correction or dispute is needed.

Hypothesis and clause correspondence:

- Schemes T and U and the morphism p are `{T U : Scheme.{u}} (p : T ⟶ U)`.
  The universe is explicit and arbitrary.
- A finite morphism is `[IsFinite p]`. Its finite presentation is rendered by
  `[LocallyOfFinitePresentation p]` together with finiteness: a finite morphism
  is affine, quasi-compact and separated, hence quasi-separated. Thus these
  binders express exactly finite and finitely presented, with no omitted
  compactness or separation condition. They do not strengthen the assumption.
- The chosen point is `(t : T)`. The point called u in the node is definitionally
  `p t`, so an additional point binder and equality proof are unnecessary.
- The entire fibre is the singleton t:
  `_hfibre : p ⁻¹' ({p t} : Set U) = ({t} : Set T)`. This is an equality of
  underlying topological sets, not a reduced or geometrically singleton fibre.
- An arbitrary quasi-coherent module is `(M : T.Modules) [M.IsQuasicoherent]`.
  In particular no finite-type or coherent hypothesis is assumed.
- Finite presentation on a neighbourhood of t is
  `∃ W : T.Opens, t ∈ W ∧ (M.over W).IsFinitePresentation`.
  Here `over` is the existing restriction to the open's slice site.
- Finite presentation of the direct image on a neighbourhood of u is
  `∃ V : U.Opens, p t ∈ V ∧ (((pushforward p).obj M).over V).IsFinitePresentation`.
  The first `↔` is exactly the neighbourhood equivalence.
- The node's specified Zariski direct image is the canonical
  `Scheme.Modules.pushforward p`. I read its definition and
  `pushforward_obj_obj` in Mathlib's `AlgebraicGeometry/Modules/Sheaf.lean`:
  sections on V are definitionally those of M on `p ⁻¹ᵁ V`, with the ring action
  restricted through `p.toRingCatSheafHom`, hence through `p.app V`.
- The second conjunct is the separate stalk equivalence. Its left side is
  `Module.FinitePresentation (T.presheaf.stalk t)
  ((RingedSpace.moduleStalkFunctor T.toRingedSpace t).obj M)`; its right side
  uses `U.presheaf.stalk (p t)` and the stalk of `(pushforward p).obj M`.
  Both scalar actions are the existing germ actions over their own local rings.
  Neither stalk is substituted for the neighbourhood condition, and the
  conclusion does not assert that one finitely presented stalk spreads out.

Dependency declarations and sources read:

- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, including its affine parent and
  finite affine-section condition.
- `def-sbc-locally-finite-presentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`; its full
  `finitePresentation_appLE` field and module documentation were read.
- `pqf-def-coherent`: imported its recorded module
  `Sheaf.AlgebraicGeometry.CoherentFiniteType`. Its
  `Scheme.Modules.IsQuasiCoherentFiniteType` is a conjunction of
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`.
  Only the first of the node's three separately defined notions is needed here.
  I use the existing `SheafOfModules.IsQuasicoherent` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`, as that recorded
  module itself does, rather than assuming the stronger conjunction or
  defining a private version. The module's full class docstring was read.
- `def-weil-pbc-module-finite-type-presentation`:
  `SheafOfModules.IsFinitePresentation` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` (the recorded
  secondary declaration), with its local finite-presentation data field.
- `def-sc-finitely-presented-module`: `Module.FinitePresentation` from
  `Mathlib.Algebra.Module.FinitePresentation`, finite generators and finitely
  generated kernel of the free presentation.
- `def-weil-pbc-module-stalk`: imported the recorded
  `WeilConjectures.Topology.PresheafModuleStalkFunctor`. Its full source was
  read through `scompile.py --source`, since it is absent in the older local
  source tree. `PresheafOfModules.moduleStalkFunctor` bundles Mathlib stalks
  and their germ scalar action. For scheme module sheaves I use the prescribed
  ringed-space specialization `RingedSpace.moduleStalkFunctor` from
  `Sheaf.Algebra.Homology.ModuleStalkFunctor`, whose entire source was read.
  It has exactly the same abelian-group stalk carrier and the CommRingCat
  version of Mathlib's canonical germ action over `X.presheaf.stalk x`.

The already recorded proof interfaces are imported without `public`:
`WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange`
(`Scheme.Modules.affinePushforward_baseChange`),
`WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde`
(`Scheme.Modules.pushforwardSpecMapCompΓIso`), and
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
(`Scheme.Modules.quasicoherent_finite_type_affine`). I read the exact
declarations and docstrings, obtaining current source through `scompile.py
--source` where local files were absent. The Mathlib proof leaves for affine
neighbourhoods, proper/closed maps, finite fibres and local finite presentation
are covered by `AffineScheme`, `Morphisms.Proper`, `Morphisms.QuasiFinite` and
`Morphisms.FinitePresentation`. The two ring-extension/singleton-stalk proof
nodes currently have no Lean declaration, so there is no module for those to
import; their exact roles are retained in the six-step proof docstring.

Edge cases checked against the source and the displayed statement:

- Identity maps give the same two neighbourhood assertions and the same stalk
  modules. No nonidentity or positive-rank restriction occurs.
- The zero module is permitted, including empty generator and relation sets.
- An empty source cannot supply t; an empty target admits no such p and t.
  A pointed fibre is nonempty automatically, so no empty-fibre case was lost.
- A nonreduced finite thickening such as Spec(k[e]/(e^2)) over Spec(k) meets
  the singleton condition; no reducedness or flatness was imposed.
- A closed immersion by a finitely generated ideal fits without a Noetherian
  hypothesis. Finite presentation must not be dropped: quotienting
  k[x1,x2,...] by its infinitely generated coordinate ideal gives a finite
  morphism for which restriction of scalars need not preserve presentation.
- With two disjoint branches above a point, presentation on just the chosen
  branch need not control the other one. The hypothesis quantifies over the
  entire fibre, not just the chosen preimage point.

Searches actually run with `msearch.py Q102 <item>` (the exact queries and
outputs are retained in `searches.jsonl`):

- LeanFinder: "For a finite finitely presented morphism with a singleton fibre,
  finite presentation of a quasi-coherent module near the source point is
  equivalent to finite presentation of its pushforward near the target point,
  and likewise for stalks". Eight hits, on finite-presentation data and locally
  finitely presented morphisms; no theorem of the requested form.
- Loogle: `SheafOfModules.IsFinitePresentation, AlgebraicGeometry.IsFinite`.
  Zero hits.
- Mathlib grep in `AlgebraicGeometry`:
  `finitePresentation.*pushforward|pushforward.*[Ff]initePresentation|singleton.*[Ff]ibre`.
  Zero hits.
- LeanSearch: "Finite presentation of a quasi-coherent module and its direct
  image along a finite morphism of finite presentation near a singleton fibre".
  Eight hits: finite-presentation classes and constructors, including
  `Module.Presentation.finitePresentation`, with no pushforward comparison.
- `rg` in the upstream `WeilConjectures` tree and project `lean/Sheaf` for
  finite-presentation/pushforward and singleton-fibre patterns. I opened
  upstream `AlgebraicGeometry/Modules/FinitePushforward.lean`: its finite
  presentation theorem is for the structure sheaf with a locally Noetherian
  target; the locally free results also differ. The project's
  `FinitePushforwardFiniteType` gives only finite type under a finite map.
  Neither is this theorem, which concerns arbitrary quasi-coherent modules,
  no Noetherian hypothesis, and both equivalences.
- Exact item-id grep in upstream `WeilConjectures`: no hit. Exact proposed
  declaration-name grep in upstream, Mathlib, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no hit.

Compilation with the prescribed `scompile.py` wrapper passed for the module
in both sandbox and library contexts, with no warnings or errors. The delivery
dry run and push are performed using `deliver2.py` after this report is written.

## Process note

During initial inspection I inadvertently ran read-only Git queries in the
shared checkout despite the brief's prohibition. They made no modifications.
All authored files are confined to this item's sandbox; subsequent compilation
and delivery bookkeeping use only the prescribed wrappers. No agent was started.

## Second reading by Q102

Independent maintainer second reading, 2026-10-18, of immutable delivery
cd07c00bbbce22eac35cb541be49d566c238a8ea. This section was supplied by the
maintainer reviewer, not by the worker. The delivered placeholder saying that
no reading was performed was an H11 report fault; this complete replacement
records the actual reading. The Worker report above is preserved.

I read the item node, all six statement-dependency nodes and their Lean records,
the delivered module and both docstrings, and the exact canonical declarations
used. I checked Stacks flat.tex:598-685 (057T), descent.tex:2098-2123 (05B4),
and more-morphisms.tex:13551-13601 (05B8) in the read-only Q102 clone. The two
obsolete tag numbers in the node's source description do not change the named
source passage; the module correctly identifies 05B4 and 05B8. No source-based
statement correction is necessary.

Hypothesis and conclusion audit (all match):

- `{T U : Scheme.{u}} (p : T ⟶ U)` supplies both schemes and their morphism.
  The universe is bound explicitly and arbitrary, with `autoImplicit false`.
- `[IsFinite p]` is exactly the affine morphism with finite maps on affine
  sections. `[LocallyOfFinitePresentation p]` gives the affine-local finite
  algebra presentations. Together these express the node's finite and finitely
  presented morphism: finiteness already supplies quasi-compactness and
  separatedness, hence quasi-separatedness. No extra hypothesis is imposed.
- `(t : T)` and `p t` render t and the node's u=p(t). `_hfibre` equates the
  entire set-theoretic inverse image of `{p t}` with `{t}`. It is not a condition
  on the reduced, geometric, or closed fibre alone.
- `(M : T.Modules) [M.IsQuasicoherent]` permits every quasi-coherent module.
  It does not assume coherent, finite type, Noetherian, flat, or locally free.
  The imported CoherentFiniteType module uses this same Mathlib predicate as
  the first component of its conjunction; the conjunction is not assumed.
- `∃ W : T.Opens, t ∈ W ∧ (M.over W).IsFinitePresentation` is precisely finite
  presentation on some neighbourhood of t. `over` is restriction to the slice
  site of opens, equivalent to restriction to the open subspace.
- The right-hand existential uses `U.Opens`, contains `p t`, and restricts
  `(pushforward p).obj M`. The first iff asserts both neighbourhood directions.
- Mathlib Scheme.Modules.pushforward is SheafOfModules.pushforward along
  `p.toRingCatSheafHom`. Its section equality `pushforward_obj_obj` is rfl;
  its module action is restriction of scalars through `p.app V`. This is the
  required canonical Zariski direct image.
- The second conjunct is a separate iff of Module.FinitePresentation over
  `T.presheaf.stalk t` and `U.presheaf.stalk (p t)`. RingedSpace.moduleStalkFunctor
  uses the actual additive sheaf stalk and Mathlib's germ scalar action. It is
  the scheme specialization explicitly allowed by the module-stalk record.
  Neither stalk is replaced by its sections, a residue-field fibre, or an
  arbitrarily chosen module. No stalk-to-neighbourhood implication is asserted.

Dependency inspection: IsFinite and LocallyOfFinitePresentation were read in
Mathlib Morphisms/Finite.lean:35-40 and FinitePresentation.lean:41-48;
SheafOfModules.IsQuasicoherent and IsFinitePresentation in
Sheaf/Quasicoherent.lean:251-270; Module.FinitePresentation in
Algebra/Module/FinitePresentation.lean:63-69. I read the Q102 side modules
CoherentFiniteType and Algebra/Homology/ModuleStalkFunctor, Mathlib's stalk
instances and germ_smul, and the current PresheafModuleStalkFunctor via
`scompile.py --source`. The proof imports' exact affinePushforward_baseChange,
quasicoherent_finite_type_affine and pushforwardSpecMapCompΓIso interfaces were
also checked, using current-source retrieval where needed. The ring-extension
and singleton-local-ring lemmas are proof-plan dependencies, not missing
objects needed to type this statement; stage 2 need not formalize their proofs
in this delivery. No helper or universe repair is needed.

Edge cases: identity morphisms, zero modules (zero generators and relations),
nonreduced singleton fibres, and finitely presented closed immersions are all
included. An empty scheme cannot provide the point t; the fibre is necessarily
nonempty. No characteristic, reducedness, positive-rank, or Noetherian
restriction occurs. Distinct points over p(t) are correctly excluded by the
whole-fibre equality. The finite-presentation assumption is essential over
non-Noetherian rings and has been retained.

Independent duplicate search: rg over Mathlib/AlgebraicGeometry, upstream
WeilConjectures and the Q102 lean/Sheaf tree for pushforward with presentation,
singleton fibres, and the exact proposed declaration found no exact theorem.
I opened upstream Modules/FinitePushforward.lean: its presentation result is
only for the structure sheaf over a locally Noetherian target. Finite type and
finite locally free pushforward results do not give this statement. The
worker's recorded LeanFinder, Loogle and LeanSearch searches are substantive.
No second definition or duplicate statement is introduced.

The module has one theorem and exactly one `sorry`, with no definitions, local
proof, private notation, or extra local instance. Both docstrings have source
and blueprint citations. Its six proof steps agree with the node: closed-map
shrinking; affine restriction of scalars; affine presentation criterion;
neighbourhood equivalence; scalar-compatible germ bijection; finite singleton
local-ring extension and the stalk comparison. `lean.statement` was compared
programmatically with the complete signature and is verbatim equal. No line
exceeds 100 characters. No statement_change or citer audit is applicable.
The item's statement/proof dependency ids have empty intersection with the
current route-pivot dropped list, and there is no repair note for this item.
No pro-etale, enhanced, model-category, or infinity-category substitute occurs.

Compiler reproduction: `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q102
lem-trf-finite-pushforward-module-finite-presentation
snapshot/lean/Sheaf/AlgebraicGeometry/FinitePushforwardModuleFinitePresentation.lean`
completed with exit code 0, no warnings or errors. The installed wrapper uses
server-side private overlays (rather than the older documented local wrapper):
it reported sandbox compilation in `/dev/shm/nt-tmp/nt-local-compile-zxq5ntgz/.lbuild`
[91.2 s including wrapper work] and library-context compilation [55.9 s]. No
limit was raised. An initial invocation with the nonexistent relative path
`lean/Sheaf/...` failed before compilation; the corrected snapshot path above
was used. No global build, project edit, branch mutation, or live Lean write
was performed by this reviewer. Source retrieval and compilation used only
the prescribed wrapper.

Verdict: the mathematics and Lean statement are correct. The only repair is
this report section, replacing the H11 placeholder with the independent
reading. The Lean module and all node records remain unchanged.
