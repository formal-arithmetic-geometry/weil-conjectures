## Worker report

The module `Sheaf.AlgebraicGeometry.FppfLocalFiniteFreeRefinement` states
`AlgebraicGeometry.Scheme.exists_finite_locally_free_fppf_refinement`, with its entire
proof `sorry`. It states the two-level refinement of Stacks Project, More on Morphisms,
Tag 05WN, `lemma-dominate-fppf`. I read the statement and all three proof paragraphs
in `literature/stacks-project/more-morphisms.tex`, lines 13648–13683. No definition,
new node, dependency repair, or statement correction is needed.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`.
- The small original family is `{I : Type v} (Si : I → Scheme.{u})
  (f : ∀ i, Si i ⟶ S)`. The explicitly declared universes `u`, `v` do not constrain
  the original family to a finite or nonempty set.
- The fppf hypothesis is `hf : Presieve.ofArrows Si f ∈ fppfPrecoverage S`, using the
  dependency's exact Mathlib notion. `fppfPrecoverage` is `precoverage
  (@Flat ⊓ @LocallyOfFinitePresentation)`; `ofArrows_mem_precoverage_iff` identifies
  its conditions as joint surjectivity and flatness plus local finite presentation
  of each morphism. No quasi-compactness, separatedness, or affine hypothesis is added.
- The Zariski covering of `S` is the existential `U : OpenCover.{u} S`.
  Its index set, members and inclusions are `U.I₀`, `U.X j`, `U.f j`.
  `OpenCover` is Mathlib's jointly surjective family of open immersions, so the
  inclusions identify its members with open subschemes and their images cover `S`.
- The first schemes and maps are `W : U.I₀ → Scheme.{u}` and
  `q : ∀ j, W j ⟶ U.X j`. Their properties are exactly
  `∀ j, (q j).IsFiniteLocallyFree ∧ Surjective (q j)`.
- The second Zariski open coverings are `V : ∀ j, OpenCover.{u} (W j)`.
  The index sets, members and inclusions are `(V j).I₀`, `(V j).X k`, `(V j).f k`.
- The second schemes and maps are `T : ∀ j, (V j).I₀ → Scheme.{u}` and
  `t : ∀ j k, T j k ⟶ (V j).X k`. Their properties are exactly
  `∀ j k, (t j k).IsFiniteLocallyFree ∧ Surjective (t j k)`.
- Factoring each composite through an original member means
  `∀ j k, ∃ (i : I) (r : T j k ⟶ Si i),
  r ≫ f i = t j k ≫ (V j).f k ≫ q j ≫ U.f j`.
  Thus this is an actual morphism and equality of scheme morphisms, rather than
  containment of underlying pointwise images. Composition is in Lean's left-to-right order.
- Empty schemes and index families remain allowed: there is no `Nonempty` or
  `Nontrivial` hypothesis. For empty `S`, take `U.I₀` empty, so all further families
  and conditions are empty. For empty `I`, fppf joint surjectivity forces `S` empty.
  An empty second index set is allowed when the corresponding `W j` is empty;
  no positive degree, nonempty open, or nonempty source is assumed.
- Smallness is expressed by the explicit universe levels: the input index universe
  is arbitrary `v`; the output open covers have index types in `Type u`, the
  universe of the underlying points of the schemes. The standard open-cover
  refinements can be indexed by points. All supplied schemes remain `Scheme.{u}`.

Dependency interfaces read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom` (full structure signatures
  and docstrings read).
- `def-pc-fppf-site`: the Mathlib leaf's `AlgebraicGeometry.Scheme.fppfPrecoverage`
  from `Mathlib.AlgebraicGeometry.Sites.Fpqc`; its other declarations
  `fppfTopology` and `overGrothendieckTopology` describe the site's generated
  topology and over-site and are unnecessary for stating a covering family.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` from
  `Mathlib.AlgebraicGeometry.OpenImmersion`; `OpenCover` from
  `Mathlib.AlgebraicGeometry.Cover.Open` uses precisely this notion.
- `def-pc-finite-locally-free`: `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`
  from `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`, read at lines
  778–783. This is the class extending `IsFinite`, `Flat`, and
  `LocallyOfFinitePresentation`; it is used at both levels. The node's degree
  variant is not required by this statement.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective` from
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, with field
  `surj : Function.Surjective f`, used for both levels.
- `def-weil-size-convention` is recorded as a metatheoretic convention, with no
  declaration or module; it is rendered by explicit universe binders.

The named proof plan is preserved in the theorem docstring. Private proof imports
supply the already-stated fibre-product and finite/flat/local-finite-presentation/
surjectivity base-change inputs. The two new refinement proof dependencies
`lem-trf-fppf-etale-finite-free-refinement` and
`lem-trf-etale-finite-free-open-refinement` currently have no Lean records; there
are no modules to import for them. They are named in the proof docstring, and the
maintainer can add their proof imports once they are stated.

Searches (2026-10-17 UTC; exact msearch outputs are in the sandbox's searches.jsonl):

- LeanFinder via msearch: “Every fppf covering admits a two-level refinement by
  Zariski coverings and surjective finite locally free morphisms”. Eight hits:
  `Scheme.precoverage`, `JointlySurjective`, `jointlySurjectivePrecoverage`,
  `instJointlySurjectivePrecoverage`, `Cover`, `zariskiPrecoverage`, `Cover.ulift`,
  `JointlySurjective.exists_eq`; none states the requested refinement.
- LeanSearch via msearch: “fppf covering admits two successive finite locally
  free surjective refinements and open covers”. Eight hits include `OpenCover`,
  `openCoverOfIsOpenCover`, `instSmallPrecoverage`, `OpenCover.finiteSubcover`,
  `precoverage`, and affine-transition-limit auxiliary covers. None is this lemma.
- Loogle via msearch: `AlgebraicGeometry.Scheme.fppfPrecoverage,
  AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`. Zero hits; Loogle does not
  know the project-only `IsFiniteLocallyFree` identifier. Its source declaration
  was separately opened and checked.
- Mathlib grep via msearch, AlgebraicGeometry: `fppf.*(refin|dominat)|dominat.*fppf|
  finite.*locally.*free.*cover`. Zero hits.
- Source/project rg: `lem-trf-fppf-local-finite-free-refinement|fppf.*(refin|dominat)|
  dominat.*fppf` across the prescribed `WeilConjectures` and `lean/Sheaf` trees.
  No upstream two-level refinement, and no item-tag declaration. The project
  has finite affine fppf refinement, finite-surjective fppf refinement, and site
  comparison applications, which have different hypotheses and conclusions.
  I opened the first two theorem signatures to check the differences.
- Declaration-name collision rg for `exists_fppf_local_finite_free_refinement|
  exists_finite_locally_free_fppf_refinement` in the upstream name index and
  both project source trees returned no matches.

Validation: `scompile.py NW lem-trf-fppf-local-finite-free-refinement <file>`
compiled the sandbox and library module cleanly (3.3 and 2.5 seconds respectively).
No warning or error was emitted. The node copy changes only `lean` and records
its signature verbatim. There are no disputed statements or node faults.

## Second reading by NW

This is the author's second reading; the dispatch brief assigns the independent
review to the maintainer and forbids starting other agents. I reopened the node,
source statement, and module and compared each clause above. The fppf presieve
hypothesis has all three defining conditions, the two `OpenCover` witnesses carry
both openness and covering, the two pairs of finite-local-freeness and surjectivity
are on the exact requested arrows, and the final equality has source `T j k`
and target `S` on both sides. In particular the second open inclusion occurs
between `t j k` and `q j`, so no intermediate refinement was lost. The original
index type is arbitrary and no empty case was excluded. No mismatch was found,
and no statement or dependency record was changed during this reading.
