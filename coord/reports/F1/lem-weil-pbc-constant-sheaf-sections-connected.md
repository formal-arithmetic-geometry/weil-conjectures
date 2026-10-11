## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ConstantSheafSectionsConnected.lean` states
`AlgebraicGeometry.Scheme.isIso_toSheafify_app_of_connected`, with the required `sorry`
proof only. No definitions, dependency modules, new nodes, or statement corrections are needed.

Hypothesis and clause correspondence:

- A scheme T: `(T : Scheme.{u})`.
- Its underlying space is connected and nonempty: `[ConnectedSpace T]`. Mathlib's
  `ConnectedSpace` includes both preconnectedness and `Nonempty`; it is not just
  `PreconnectedSpace`.
- E is an arbitrary abelian group: `(E : AddCommGrpCat.{max u v + 1})`. The extra
  universe v permits coefficient groups independently large relative to the scheme.
  There are no finiteness, torsion, characteristic, field, or normality assumptions.
  Groups in a smaller universe can be canonically universe-lifted; this is only
  size bookkeeping, not a restriction on the mathematical groups.
- The small étale site: `T.smallEtaleTopology` on `T.Etale`.
- The constant presheaf with identity restrictions: `(Functor.const T.Etaleᵒᵖ).obj E`.
- Its sheafification is the constant sheaf, by the recorded definition
  `constantSheaf J D = Functor.const _ ⋙ presheafToSheaf J D`.
- The canonical presheaf-to-sheafification map: `toSheafify T.smallEtaleTopology ...`,
  defined as `(sheafificationAdjunction J D).unit.app P`.
- Evaluation at the final object T: `.app (op (Etale.mk (𝟙 T)))`.
  This is specifically the identity étale morphism T → T, not an arbitrary
  terminal-object choice or a stalk. Its source evaluates definitionally to E;
  its target evaluates to the global-section abelian group of the constant sheaf.
- The conclusion: `IsIso` of that exact component, a morphism in AddCommGrpCat.
  Thus this is an isomorphism of abelian groups and equivalently says every
  section is the constant section of a unique element of E. A separate
  existential-uniqueness conjunct would repeat, rather than strengthen, this clause.

Dependencies read and used (no private definitions):

- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Scheme` (and its category morphisms).
- `def-weil-connected-scheme`: Mathlib.Topology.Connected.Basic, `ConnectedSpace`.
- `def-weil-pbc-etale-site`: Mathlib.AlgebraicGeometry.Sites.Etale,
  `AlgebraicGeometry.Scheme.smallEtaleTopology`; the identity object uses
  `Scheme.Etale.mk` from Mathlib.AlgebraicGeometry.Morphisms.Etale.
- `def-weil-pbc-sheafification`: Mathlib.CategoryTheory.Sites.Sheafification,
  `presheafToSheaf`, `sheafificationAdjunction`, and `toSheafify`.
- `def-weil-pbc-constant-sheaf`: Mathlib.CategoryTheory.Sites.ConstantSheaf,
  `constantSheaf`; its underlying presheaf is exactly `sheafify J P` for this P.
  The theorem uses the equivalent unfolded definition to name the canonical map.
- `def-weil-pbc-abelian-etale-sheaves`: Mathlib.CategoryTheory.Sites.Sheaf,
  `Sheaf J AddCommGrpCat` (the codomain of presheafToSheaf).

The two GrothendieckAbelian imports provide concrete abelian-group coefficients and
sheafification instances. As in the landed TorsorExtensionPresentation module, local
`essentiallySmallSelf` and the priority of `hasSheafify_of_essentiallySmall` allow the
site to be regarded as small in the larger coefficient universe. This supplies the
construction rather than adding a sheafification-existence hypothesis.

Source checked: [Stacks Tag 03P5](https://stacks.math.columbia.edu/tag/03P5),
Remark 59.23.2. The local literature checkout is absent on this machine, so the exact
source was read online. It identifies sections with Zariski locally constant maps;
connectedness then gives constancy and nonemptiness uniqueness. The declaration
contains all three proof steps from the node, naming both proof-lemma nodes.

Edge cases checked before writing: the empty scheme is excluded exactly by
ConnectedSpace, as required (on it the canonical map fails for a nontrivial E).
Disconnected nonempty schemes need not have constant global sections and are also
excluded exactly by that hypothesis. The zero group is allowed. Arbitrary infinite
or nontorsion groups are allowed. Nonreduced connected schemes and connected schemes
in any characteristic are allowed; no reducedness, integrality, or characteristic
condition was introduced. Coefficient and scheme universes are explicitly bound.
No statement faults or disputed assertions were found.

Searches made using `/home/ubuntu/weil-launcher/msearch.py`:

- leanfinder: "global sections of the constant etale sheaf on a connected scheme equal
  the coefficient abelian group": eight hits, all structure-sheaf sections or the
  empty scheme; no matching declaration.
- loogle: "CategoryTheory.constantSheaf, ConnectedSpace": zero hits.
- leansearch: "constant etale sheaf global sections connected scheme": unavailable,
  Internal Server Error; this is not counted as a no-match result.
- grep (Mathlib CategoryTheory):
  `constantSheaf.*connected|connected.*constantSheaf|isIso.*constantSheaf`:
  five results about the counit and constant sheaves with a fully faithful functor;
  none is this canonical unit component for a connected étale site.
- Local rg over WeilConjectures and lean/Sheaf for the same pattern: general
  constant-sheaf comparisons and normal/generic-point statements, no exact match.
  `rg -n 'lem-weil-pbc-constant-sheaf-sections-connected' WeilConjectures`:
  no occurrence. The relevant upstream module
  WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf was read in full:
  its constantSheafIsoContinuousMapSheaf gives locally constant sections for a
  discrete group, but does not state this connected-scheme canonical-map isomorphism.
- Full proposed declaration name searched in dag/lean_names_upstream.json,
  WeilConjectures and lean/Sheaf: no clash.

Server validation: scompile.py compiled the module cleanly in 1.8 seconds,
exit code 0, with no warnings. Delivery dry-run validation follows below.


## Second reading by F1

The first worker's hypothesis/conclusion translation was mathematically correct, but
its search missed an exact upstream declaration (H4). The final delivery therefore
has no Lean module: it records existing
`AlgebraicGeometry.Scheme.bijective_toSheafify_app_terminal`, module
`WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections`, slopmaster2.
The Worker report above describes the superseded proposed module and remains as history.
The node statement, dependencies, and proof are unchanged; there is no statement
correction, new definition node, or dependency module to audit.

Independent object/hypothesis/conclusion checklist against the node:

- Scheme T: upstream section binder `(X : Scheme.{u})`; exact. Read Scheme.lean:42,
  a locally ringed space locally isomorphic to affine spectra, not an affine-only notion.
- Connected and nonempty underlying space: `[ConnectedSpace X]`; exact.
  Read Connected/Basic.lean:705: extends PreconnectedSpace and has toNonempty.
- Arbitrary abelian group E: section binder `(M : AddCommGrpCat.{u + 1})`; exact.
  There is no finiteness, torsion, field, Noetherian, normality or reducedness assumption.
  Both universes are explicit in the source context. The coefficient universe one
  above the scheme universe is standard site size bookkeeping; a common larger
  universe and universe lifts accommodate arbitrarily large or small coefficients
  and schemes. It is not a bound on cardinality, nor a finite group restriction.
- Small etale site: `X.smallEtaleTopology`, on `X.Etale`; exact. Read Sites/Etale.lean:51
  and Morphisms/Etale.lean:157,191: etale schemes over X and their X-morphisms, with
  jointly surjective etale covering families (ofArrows_mem_smallEtaleTopology_iff).
- Constant presheaf: `((Functor.const X.Etaleᵒᵖ).obj M)`; exact, identity restrictions.
- Constant sheaf: `sheafify X.smallEtaleTopology` of that presheaf; exact.
  Read ConstantSheaf.lean:66: constantSheaf is Functor.const composed with
  presheafToSheaf, so this is its underlying presheaf, not a second definition.
- Abelian sheaves: values are AddCommGrpCat, and presheafToSheaf has codomain
  `Sheaf X.smallEtaleTopology AddCommGrpCat`; exact. Read Sheaf.lean:302 and
  Sheafification.lean:73,81,98,102. The unit is exactly `toSheafify`.
- Canonical map iota_T: the existing theorem uses precisely
  `(CategoryTheory.toSheafify X.smallEtaleTopology
  ((Functor.const X.Etaleᵒᵖ).obj M)).app (op (Etale.mk (𝟙 X)))`; exact.
  The identity etale X-scheme is the final object (the source explicitly names
  MorphismProperty.Over.mkIdTerminal); this is global sections, not a geometric stalk.
- Conclusion, including unique constant value: `Function.Bijective` of this exact
  homomorphism; exact. ConcreteCategory.isIso_iff_bijective (EpiMono.lean:186) and
  AddCommGrpCat's forget-reflects-isomorphisms instance identify this with IsIso.
  Surjectivity supplies a constant section and injectivity supplies its uniqueness.
  The theorem is universally quantified over X and M, then ConnectedSpace X;
  it introduces no extra hypothesis or existential choice of an unrelated isomorphism.

All six statement dependency nodes were opened and matched with their recorded
Mathlib declarations. Their signatures and defining bodies above give the actual
notions, not similar names. The upstream declaration's full docstring and proof
were also read, including injectivity by evaluation at a point, and local constancy
from etale coverings and openness followed by connectedness.

Source: the local Stacks checkout is absent. Independently read Tag 03P5 online
(https://stacks.math.columbia.edu/tag/03P5), and retrieved the raw Stacks
etale-cohomology.tex from https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex.
Read remark-constant-locally-constant-maps and section-big-small, which it references:
S is any scheme and tau may be etale; no separatedness, finite type or base field
is assumed. The source identifies sections with Zariski locally constant maps;
connectedness and nonemptiness give exactly this node's conclusion.

Edge cases: empty schemes are excluded by the explicit nonemptiness in ConnectedSpace,
exactly as the node requires; for a nontrivial group on the empty scheme uniqueness
would fail. The zero group is allowed. Disconnected schemes are excluded as required.
Infinite groups, schemes with nilpotents, and every characteristic are allowed.
There is no index set, integer n, or characteristic binder, so empty-index and n=0
cases introduce no hidden restriction. Universe parameters are bound and can be
increased; no auto-implicit object or extra typeclass hypothesis is present.

Independent searches, using other words and broader paths than the first worker:

- LeanFinder via msearch: "unit of sheafification constant presheaf is bijective at a
  connected nonempty scheme": eight hits about stalks, locally bijective maps and
  constant-sheaf counits; none is this statement.
- LeanFinder: "constant etale sheaf canonical constant section homomorphism connected
  scheme isomorphism": eight hits about structure sheaves and counits; no exact hit.
- Loogle: `CategoryTheory.toSheafify, IsIso` reported an unknown short identifier;
  retried with `CategoryTheory.toSheafify, CategoryTheory.IsIso`: three hits, including
  isIso_toSheafify for a presheaf already a sheaf and stalk versions; no exact match.
- Local rg over all WeilConjectures, Mathlib, lean/Sheaf and dag/lean_names_upstream.json
  with `toSheafify.*connected|connected.*toSheafify|constant.*sections.*connected|
  connected.*constant.*sections|isIso_toSheafify_app_of_connected` found the exact
  existing theorem in AlgebraicGeometry/Sites/ConstantSheafSections.lean:99.
  The first worker searched only the Mathlib/AlgebraicGeometry/Sites subtree of the
  source for the comparison result; this independent whole-library search mattered.
- Read that source module in full. Its bijective theorem is the exact map and
  conclusion, not just the sheaf-of-continuous-maps comparison in the other module.

Mismatch and repair: H4 duplicate theorem removed from the sandbox; replaced the
item's lean record by existing:true with the upstream module, declaration, exact
verbatim theorem signature, branch slopmaster2 and a note explaining the categorical
isomorphism/bijectivity equivalence. No correct mathematical statement was rewritten.
No new proofs or hollow definitions were introduced. New-module docstring conventions
and sorry-only proof checks are vacuous for this existing-declaration delivery.
The original node's complete three-step proof remains available to stage 3.

Validation: scompile.py imported the existing module and checked the exact declaration
and ConcreteCategory.isIso_iff_bijective remotely, cleanly in 1.8 seconds with no warnings.
