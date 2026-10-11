## Worker report

Existing declaration: `TopCat.Sheaf.IsFlasque.subsingleton_H`, in
`WeilConjectures.Mathlib.Topology.Sheaves.Flasque` (source lines 111–140).
Read its complete signature, preceding section variables, docstring and proof.
No new module or notion is delivered.

Hypothesis and clause matching:
- A topological space is `{X : TopCat.{u}}` in the declaration's section variables.
- An abelian sheaf is `F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
  AddCommGrpCat.{u}`, definitionally `TopCat.Sheaf AddCommGrpCat.{u} X`.
- Flasque is `[Presheaf.IsFlasque F.obj]`. This is exactly `TopCat.Sheaf.IsFlasque F`;
  epimorphisms in AddCommGrpCat are surjective, hence precisely the restriction-surjectivity
  condition for all pairs of opens, not merely global-to-open restrictions.
- Positive degree is `n + 1`, for arbitrary `n : ℕ`, which exhausts precisely `q > 0`.
- Vanishing is `Subsingleton (CategoryTheory.Sheaf.H F (n + 1))`:
  the abelian group consists only of its zero element.
- The resolution interpretation is the recorded cohomology dependency
  `def-sc-zariski-cohomology`, `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`,
  `CategoryTheory.Sheaf.H'`. Read its full signature and docstring. `H'` is Ext from the
  sheafification of the free abelian representable; at the terminal open this sheaf is
  canonically the constant integer sheaf used in `H`. The adjunctions identify Hom from
  either with evaluation at the terminal open, so their Ext computes the same right
  derived functor of global sections. This is exactly the resolution interpretation in
  the dependency's recorded note, rather than a different cohomology theory.

The existing theorem's ambient `HasExt.{u}` and `EnoughInjectives` describe structures
available on the abelian category of sheaves; they impose no extra restriction on X or F.
`hasExt_of_enoughInjectives` supplies the first from the second and local smallness.
Read the full `H` definition, `H.equiv₀` (Hom/degree-zero cohomology identified with sections
at a terminal object), and `IsFlasque` definition. The DAG already carries flasqueness as
`def-sc-zariski-flasque`, recorded as `TopCat.Sheaf.IsFlasque` in
`Mathlib.Topology.Sheaves.Flasque`; no private copy is needed.

The theorem's dimension-shifting proof has the same three steps as the node: injectives
are flasque; short exact sequences with flasque kernel are sectionwise surjective and
have flasque quotient; iteration kills every positive cohomology group.
Checked the source [Stacks Tag 09SY](https://stacks.math.columbia.edu/tag/09SY):
its module statement specializes to abelian sheaves using the locally constant integer
ring sheaf, as explained in the node's proof. No statement correction or dispute.

Edge cases: the empty space and zero sheaf remain allowed; degree one is n=0, while
cohomology in degree zero is correctly not asserted to vanish. No scheme, noetherian,
separatedness, or finiteness hypothesis is introduced. The universe is arbitrary u,
including all spaces and abelian sheaves after choosing a common bounding universe.

Searches performed:
- msearch leanfinder, `flasque abelian sheaf higher sheaf cohomology vanishes`: eight hits
  on H, cohomologyPresheaf, and injective-resolution Ext, no exact theorem in Mathlib.
- msearch loogle, `TopCat.Sheaf.IsFlasque`: six hits; the flasque definition and the
  short-exact-sequence section-surjectivity and quotient-flasqueness results.
  An earlier query containing an escaped apostrophe was malformed (unknown x27).
- msearch grep, `flasque|flabby`, Topology/Sheaves: five hits in Flasque.lean, no
  higher-cohomology theorem in Mathlib.
- msearch leansearch, `flasque abelian sheaf cohomology vanishes`: unavailable,
  Internal Server Error.
- rg over WeilConjectures and lean/Sheaf for flasque, H', cohomology, and acyclic;
  followed by `isZero_cohomology_of_isFlasque|flasque.*acyclic|isFlasque.*cohomology`
  over Mathlib, WeilConjectures and lean/Sheaf: found the upstream Flasque module.
  Opened it fully and found the exact theorem above. The upstream CechFlasque theorem
  is instead Čech cohomology and was not used. Searching the item id in WeilConjectures
  returned no hit; the exact declaration does not carry this blueprint id.

A draft H' statement compiled locally after specifying the Ext instance explicitly;
removed that draft on discovering the upstream theorem, as required by one declaration
per statement. Final validation is the existing-declaration preflight in the dry run.

## Second reading by M1

Read the item's complete node, its recorded upstream declaration including all section
variables and proof, and the recorded dependencies `def-sc-zariski-cohomology` and
`def-sc-zariski-flasque` with their source declarations. Independently obtained and read
Stacks `cohomology.tex`, Section "Cohomology of sheaves" and Section "Flasque sheaves",
including `definition-flasque`, `lemma-injective-flasque`, and `lemma-flasque-acyclic`
(Tag 09SY). The source assumes an arbitrary ringed space, with no finiteness or separation
condition. Applying it to the locally constant integer ring sheaf gives the node's abelian
sheaf statement. The node requests global vanishing; the source's additional assertion on
each open does not become an extra conclusion of this node.

Object/hypothesis/conclusion list, matched item by item:

- Object X: arbitrary topological space, rendered by the upstream section variable
  `{X : TopCat.{u}}`. PASS: no scheme structure or other geometric assumption required.
- Object F: abelian sheaf on X, rendered by
  `F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}`.
  PASS: sheaves on the opens site are precisely topological abelian sheaves.
- Hypothesis flasque: `[Presheaf.IsFlasque F.obj]`. Opened Mathlib's class and the
  dependency's `TopCat.Sheaf.IsFlasque` abbreviation. The class requires `Epi (F.map i)`
  for every arrow of opposite opens; `AddCommGrpCat.epi_iff_surjective` identifies this
  with surjectivity of F(V) -> F(U) for every U contained in V. PASS: exactly the node.
- Degree q > 0: `(n : ℕ)` and degree `(n + 1)`. PASS: every positive natural degree
  occurs uniquely; quantification over n and F is universal and may be exchanged.
- Conclusion H^q = 0: `Subsingleton (CategoryTheory.Sheaf.H F (n + 1))`.
  PASS: H has an abelian-group structure, so subsingleton means every element is zero.
- Resolution meaning: opened Mathlib's definitions of `H`, `cohomologyPresheafFunctor`,
  and the dependency's `H'`, plus `H.equiv₀` and its naturality theorem. H is Ext from
  the constant integer sheaf; H' at the terminal open is Ext from the sheafified free
  abelian representable. Both representing objects corepresent the same section functor,
  by the constant-sheaf adjunction and by sheafification/free-forgetful/Yoneda adjunctions
  (the upstream `freeOpenHomEquiv` spells out the latter). They are canonically isomorphic
  by Yoneda, hence their Ext groups agree in every degree. With enough injectives these
  compute the stated right derived global sections, exactly as the dependency note
  specifies. PASS: no new cohomology definition; the formal comparison is stage-3 work.
- Ambient category structures: full elaborated signature has `HasExt.{u}` and
  `EnoughInjectives` for the same category. PASS: these impose no restriction on X or F.
  A scratch compile importing Mathlib's Grothendieck-sheaf and Grothendieck-HasExt modules
  successfully synthesized both for arbitrary X; they are available structures, not
  assumptions on the geometry. HasSheafify is already supplied by the topology machinery.

Edge cases: empty topological space (and hence empty scheme) is allowed; zero sheaf is
allowed; n = 0 asserts degree-one vanishing, while degree-zero vanishing is correctly
absent. No index set, characteristic, coefficient field, noetherianity, or separatedness
occurs. Universe u is arbitrary: spaces and their abelian sheaves of different sizes may
be placed in a common bounding universe, without excluding any mathematical case.

Independent searches (different wording from the writer):

- `msearch leanfinder "flabby sheaf acyclic derived global sections"`: eight hits on
  H, cohomologyPresheaf, and Grothendieck-sheaf infrastructure; no exact Mathlib theorem.
- `msearch loogle "TopCat.Sheaf.IsFlasque, Subsingleton"`: zero hits.
- `msearch grep "flabby|subsingleton_H|acyclic" Topology/Sheaves`: zero service hits.
- Direct rg over Mathlib/Topology/Sheaves, upstream WeilConjectures, and project lean/Sheaf
  for `flabby|subsingleton_H|flasque.*cohomology|acyclic.*flasque` independently located
  `WeilConjectures.Mathlib.Topology.Sheaves.Flasque` and its exact theorem. The upstream
  CechFlasque result concerns a different cohomology and is not used.

No statement, dependency, universe, or definition mismatch found. No new nodes or modules
are needed; retained the existing record and its verbatim signature. H5/H6/H8/H9 introduce
no new obligations because this delivery adds no Lean declarations. Read the existing
proof: sectionwise surjectivity kills H1, flasque quotient and injective vanishing give
successive dimension shifts, precisely realizing the node's three resolution steps.
The scratch import/check file compiled cleanly in 1.9 seconds with autoImplicit disabled;
`#print axioms TopCat.Sheaf.IsFlasque.subsingleton_H` returned only `propext`,
`Classical.choice`, and `Quot.sound`. The second reading changes only this review report,
adding the independent source/signature checks and compiler evidence.
