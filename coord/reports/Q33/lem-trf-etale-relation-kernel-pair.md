## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleRelationKernelPair` states
`AlgebraicGeometry.Scheme.etale_relation_kernel_pair`, with one `sorry` and no new
definitions. It identifies a monomorphic equivalence relation with the kernel pair
of its fppf sheaf quotient. The equivalent pullback-square formulation avoids an
additional helper choosing the equality needed to construct the comparison map.

Every hypothesis and conclusion of the node is rendered as follows:

- The base scheme is `{S : Scheme.{u}}`. The schemes over it are `{R U : Over S}`;
  `s t : R ⟶ U` are precisely the two morphisms over this fixed base.
- The map to the fibre product is `prod.lift s t` in `Over S`. Its underlying scheme
  is the fibre product over `S`, and `[Mono (prod.lift s t)]` states the node's
  monomorphism hypothesis. Monicity in the slice is equivalent to monicity of this
  underlying scheme map; any test map into `R` inherits its map to `S`.
- For every test scheme over the base, `hrel : ∀ T : Over S, Equivalence ...`
  states that the image of `R(T)` is an equivalence relation on `U(T)`.
  Its predicate is exactly `∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b`.
- `coequalizer (yoneda.map s) (yoneda.map t)` is the presheaf quotient. Presheaf
  colimits are pointwise, so its sections are the quotient by the generated relation;
  `hrel` makes this the stated equivalence relation itself.
- `F : Sheaf (Scheme.fppfTopology.over S) (Type u)` is the quotient sheaf, and
  `η : coequalizer ... ⟶ F.obj` is its sheafification unit. The condition `hη`
  says that composition with this unit gives a bijection of morphisms to every
  fppf sheaf. This is exactly the sheafification universal property of
  `presheafToSheaf` and `sheafificationAdjunction`, rather than an extra condition
  on a quotient. This objectwise universal-property formulation is also used in
  the already landed `Sheaf.AlgebraicGeometry.EtaleRelationQuotient`; it does not
  assume that every small-valued presheaf on this large site has sheafification.
- The quotient map is the concrete composite `coequalizer.π ... ≫ η`. Both
  lower/right arrows of `IsPullback` are this same canonical map, and the upper/left
  arrows are `yoneda.map s` and `yoneda.map t`. Thus the conclusion says precisely
  that the canonical map `h_R → h_U ×_F h_U` is an isomorphism. Representables are
  fppf sheaves by subcanonicity, and the inclusion into presheaves creates limits,
  so the presheaf pullback assertion is equivalent to the sheaf assertion.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-pc-fibre-product`: `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme
  pullbacks; `CategoryTheory.Limits.pullback` and its projections/universal property
  are in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. The slice
  product `prod.lift s t` expresses the same fibre product over `S`.
- `def-pc-fppf-site`: `Mathlib.AlgebraicGeometry.Sites.Fpqc`, declarations
  `AlgebraicGeometry.Scheme.fppfPrecoverage` and `fppfTopology`; the over topology
  is `CategoryTheory.GrothendieckTopology.over` in `Mathlib.CategoryTheory.Sites.Over`.
  This is the topology called `overGrothendieckTopology` for the fppf morphism
  property in the dependency's Mathlib match. Its coverings are jointly surjective
  flat locally finitely presented families over `S`.
- `def-weil-pbc-sheafification`: `Mathlib.CategoryTheory.Sites.Sheafification`,
  `presheafToSheaf`, `sheafificationAdjunction`, `toSheafify`. Its exact defining
  universal property is the `η, hη` interface, avoiding a global existence assumption.
- Proof imports: `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`,
  `CategoryTheory.sheafification_sections_local`; and
  `Mathlib.CategoryTheory.Sites.LocallyBijective`,
  `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`. The live source of the former
  was read with the prescribed source wrapper. Its universe convention is explicit;
  in stage 3 one may enlarge coefficient universes for the local-sections proof,
  while the assertion itself retains the given representables and small-valued quotient.

Edge cases checked: the identity relation gives the diagonal kernel pair of the
identity quotient. The full relation gives locally related pairs, with monicity
ensuring unique relation sections. Empty `U` is allowed, with its only equivalence
relation; empty `R` for nonempty `U` is excluded by reflexivity, as it should be.
The empty base is allowed. No etaleness, flatness or finiteness assumption on `s,t`
is imposed: only the topology of the quotient is fppf. All universes and variables
are explicit; there is no independent smaller test universe.

Searches made for an existing declaration:

- `msearch.py leanfinder`, query “For a monomorphic equivalence relation of schemes
  the relation is the kernel pair of its fppf sheaf quotient”: eight results about
  scheme kernels, monomorphisms and pullback carriers; no quotient-kernel-pair theorem.
- `msearch.py loogle`, query `CategoryTheory.IsKernelPair`: twelve generic
  kernel-pair declarations; none proves effectiveness of this sheaf quotient.
- `msearch.py leansearch`, query “kernel pair of the quotient of an equivalence
  relation in sheaves of sets”: generic kernel pairs and setoid quotient kernels,
  with no scheme/fppf theorem.
- `msearch.py grep`, query `kernel.*pair|quotient.*sheaf|pre-equivalence` in
  `AlgebraicGeometry`: four hits in EffectiveEpi, OpenImmersion and IdealSheaf,
  none stating this result. Direct `rg` on the upstream project, the item id and
  relation/kernel-pair names found no declaration. Searching `lean/Sheaf` found
  only the downstream stronger etale quotient theorem, whose etaleness hypotheses
  make it unusable here and whose proof cites this item. It is not imported.

No statement correction, new node or dependency repair is needed. The source is
Stacks `groupoids.tex`, quotient-sheaf definition and Tag 045Y, read in full;
monicity adds injectivity to its local-surjectivity assertion. No statement dispute.

## Repair of returned delivery

The immutable returned head `024ec8b0caca233fdfbafbd76875b9abbe1c59aa` was read
without Git commands or mutations by decoding its loose Git objects. It contains
only a stage-1 split and a stage-1 report, with no Lean record or module. Its node's
statement, statement dependencies and proof agree with the current main-branch
node. The current node's search/review metadata is retained unchanged.

The return rejected `--apply-fixes` because the report had been offered under a
repository-relative path, outside the permitted stage-2 fix filenames. This
replacement is a genuine stage-2 packet: the owning module under `lean/Sheaf`,
the current node with only `lean` added, and the worker's root `report.md`, which
the prescribed delivery wrapper places at the correct report path. No reviewer
fix directory or invalid repository-relative fix file is supplied. This is not
an unchanged stage-1 re-push.

## Validation

The prescribed single-file compilation passed cleanly on the server. The delivery
dry run passed both preflight and compilation (`6bf989765a`). The node differs
from the current base only in `lean`; the recorded signature matches the module
verbatim, and every Lean source line has at most 100 characters.

## Second reading by Q33

Independent maintainer reading, 2026-10-18, of immutable delivery
22e0c228057ffdbf02c631efa320c31558e1ff51. This reading was performed by
the maintainer reviewer, not by the author or a second worker of Q33.

Hypothesis and conclusion audit:

- `S : Scheme.{u}` is the base scheme; `R U : Over S` and `s t : R ⟶ U`
  are schemes and morphisms over that same base. Mathlib `Scheme` includes
  local affineness, and `Scheme.Hom` is a locally ringed-space morphism.
- `prod.lift s t` in the slice is the map to the fibre product over S.
  Its monicity is exactly the stated monicity: maps into R acquire their
  map to S by composition, so testing monicity in the slice loses no tests.
- `hrel` quantifies over every `T : Over S`, without a smaller independent
  test universe. Its predicate is precisely the existence of one relation
  section with the prescribed two projections. `Equivalence` supplies
  reflexivity, symmetry, and transitivity, including empty-section cases.
- The coequalizer of the Yoneda maps is the quotient presheaf, since functor
  colimits are pointwise. Since the given relation is already an equivalence
  relation, generating the coequalizer relation introduces no extra pairs.
- `Scheme.fppfTopology.over S` is the induced big fppf topology, not the
  small etale or pro-etale topology. `F` is a sheaf and `η, hη` specify the
  objectwise sheafification universal property: every map from the quotient
  presheaf to every sheaf factors uniquely through η. This is the property
  of the recorded sheafification dependency, not an arbitrary quotient map
  or an additional effectiveness hypothesis. No global `HasWeakSheafify`
  assumption for all small-valued presheaves has been added.
- `IsPullback` has the two Yoneda maps as its top and left arrows and the
  SAME coequalizer projection followed by η as its right and bottom arrows.
  It includes commutativity and the full limit universal property. Therefore
  it says that the canonical map from h_R to the kernel pair is an
  isomorphism. Fppf subcanonicity and creation of limits by the inclusion of
  sheaves identify this presheaf formulation with the stated sheaf result.

Verdict on each clause: exact. No extra etaleness, flatness, finiteness,
Noetherian, nonempty, or representability hypothesis occurs. No new definition
or dependency repair was required. The single theorem has only `sorry` as
its proof. Both docstrings give the source and blueprint id; its proof
comment follows all three DAG steps.

Universe audit: the scheme and test-scheme universe is the same arbitrary u;
Yoneda sections and the given quotient are Type u. The site object universe
is larger than its hom universe; this has not been equated or truncated.
The imported local-sections theorem is stated with values in the maximum
of the site universes, so it is not directly instantiated on the displayed
small presheaf. Its use in a future proof needs universe transport (and a
comparison respecting η), or restriction to a sufficiently small fppf basis;
merely relabelling Type u as Type (u+1) is not such a comparison. This is a
proof-interface consideration, not an extra binder or a missing clause in
the present objectwise universal-property statement. The downstream landed
EtaleRelationQuotient uses exactly this same quotient interface and the
same pullback conclusion.

Edge cases: identity relation, full relation, empty U and empty S are
covered. Empty R with nonempty U cannot satisfy reflexivity (take T = U
and its identity). Empty coverings over the empty scheme are compatible
with the sheaf condition and local arguments. There is no degree, prime,
characteristic, or coefficient ring restriction to check.

Sources and exact interfaces read:

- `literature/stacks-project/groupoids.tex`, quotient-sheaf discussion and
  definition, lines 3690-3746, and Tag 045Y, lines 3785-3816. Tag 045Y gives
  local witnesses; monicity upgrades local surjectivity to an isomorphism.
- `literature/stacks-project/sites.tex`, lines 1974-2181, including Tags
  00WB, 00WH and 00WK: plus-plus, the adjunction universal property, and
  local representatives/equality.
- All four immutable statement-dependency records, and Mathlib Scheme,
  Pullbacks (`HasPullbacks Scheme`), pullback projections/lift,
  Sites/Fpqc (`fppfPrecoverage`, `fppfTopology`, subcanonicity), Sites/Over
  (`GrothendieckTopology.over`), and Sheafification (`presheafToSheaf`,
  `sheafificationAdjunction`, `toSheafify`).
- Mathlib `IsPullback`, functor-category pointwise colimits, and
  `Sheaf.isLocallyBijective_iff_isIso` with its full surrounding binders.
  The exact live `CategoryTheory.sheafification_sections_local` source
  was obtained through `scompile.py --source`; its maximum-universe
  condition and final local-equality conjunct were read.

Independent duplicate searches used `rg` for effective equivalence relations,
quotient sheaves and kernel pairs in Mathlib Sites and AlgebraicGeometry,
upstream WeilConjectures and the group's lean/Sheaf. Generic kernel-pair
and effective-epi results do not assert effectiveness of this quotient.
EtaleRelationQuotient is a downstream theorem with extra etaleness
hypotheses; it cannot replace this theorem and is not imported.

Mechanical checks: `lean.statement` equals the source signature verbatim;
maximum Lean line length is 89; one theorem and one sorry; no hollow data,
private duplicate definition, proof beyond sorry, or unbound variable.
The route-pivot dropped-node list has empty intersection with the item and
all its statement/proof dependencies. No repair note exists for this item
at origin/newtargets-dag, and no dropped machinery is used.

Compiler reproduction: ran
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q33 lem-trf-etale-relation-kernel-pair <immutable snapshot module>`.
Exit status 0; sandbox compilation 5.1 s and library compilation 10.5 s;
no Lean diagnostics. The installed wrapper (2026-10-17) actually uses the
server's persistent side overlay with confirmation; the result reports
private artifacts under `/dev/shm/nt-tmp/nt-local-compile-qnmhkqoh/.lbuild`.
This confirms the worker's recorded single-file compilation independently.
No global build, live Lean edit, claim, delivery, merge, or Git mutation
was performed.

Finding H11: the delivered second-reading section contained only a disclaimer
and no reading. Replaced it with this actual independent clause audit.
The Worker report is retained. No Lean or JSON changes were needed.
