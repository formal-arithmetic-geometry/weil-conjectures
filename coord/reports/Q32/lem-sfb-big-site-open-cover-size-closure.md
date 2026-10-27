## Worker report

The module `Sheaf.AlgebraicGeometry.BigSiteOpenCoverSizeClosure` states
`AlgebraicGeometry.Scheme.exists_iso_of_openCover_cardinalSize_le`, with its entire
proof `sorry`. It uses the existing scheme size and chosen-category definitions;
there are no new definitions, new nodes, dependency modules, or statement corrections.
The node's mathematical statement, proof, and proof dependencies are unchanged.
Two already landed definition nodes are added to `stmt_deps`, as permitted by
brief-stage2 §5: `def-sfb-stacks-big-site-category` and
`def-sfb-scheme-cardinal-size`.

Clause-by-clause correspondence:

- The fixed chosen full category of the big fppf site is
  `StacksBigSiteCategory code α`, with admissibility hypothesis
  `hα : IsStacksBigSiteCategory code S₀ α`. This is precisely the underlying-category
  choice of Stacks 021R(2), referring to 000J(1)--(4). The injective code, initial
  set S₀, and ordinal α expose that choice; they are not extra geometric restrictions.
  The full-subcategory construction retains all morphisms of schemes. The topology
  and the choice of a set of fppf covering families do not affect this assertion.
  In particular, the conclusion concerns this fixed category, not another category
  chosen after seeing X.
- The given object T is `T : StacksBigSiteCategory code α`; its underlying scheme
  is `T.obj`. No nonemptiness hypothesis on S₀ or on T's underlying space is imposed.
- The universe convention is rendered by `universe u v`, schemes in `Scheme.{u}`,
  and the existing ZFC coding in `ZFSet.{u+1}` with `α : Ordinal.{u+1}`.
  The cover index is `I : Type v`, independent of u. Explicit lifts place all cardinal
  comparisons in `Cardinal.{max u v}`. In particular, this does not impose v = u
  or any smallness assumption on I.
- For every scheme Z, the displayed s(Z) is the existing `Z.cardinalSize`:
  max ℵ₀ (max (#Z.affineOpens) (sup over affine opens of #Γ(Z,U))). Affine opens
  are actual opens and the sections are those of the structure sheaf. No separate
  presentation of affine charts or alternative size function is introduced.
- The scheme X is `X : Scheme.{u}`. The family of open subschemes is
  `U : I → X.Opens`, with induced scheme structures `(U i).toScheme`.
- The covering equality X = union Uᵢ is `hU : (⨆ i : I, U i) = ⊤`.
- The index bound |I| ≤ s(T)^ℵ₀ is `hI`, comparing
  `Cardinal.lift.{u} (Cardinal.mk I)` to
  `Cardinal.lift.{v} (T.obj.cardinalSize ^ Cardinal.aleph0)`.
- Each member bound s(Uᵢ) ≤ s(T)^ℵ₀ is `hsize : ∀ i : I, ...`, with both
  scheme-size cardinals lifted by `Cardinal.lift.{v}`.
- The conclusion is exactly `∃ X₀ : StacksBigSiteCategory code α,
  Nonempty (X₀.obj ≅ X)`: an object of that chosen category with a scheme isomorphism
  in the direction X₀ ≅ X. No restriction on X already belonging to the category
  occurs.
- The empty index set is permitted: there is no `Nonempty I` binder. Its supremum
  of opens is bottom, so hU forces X empty. Size of the empty scheme is ℵ₀, while
  ℵ₀ ≤ s(T) ≤ s(T)^ℵ₀, so the conclusion includes this case.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`. Its local-affineness field and full Hom
  signature were read; they give the schemes and scheme isomorphisms here.
- `def-pc-fppf-site`: `AlgebraicGeometry.Scheme.fppfPrecoverage` and
  `fppfTopology`, in `Mathlib.AlgebraicGeometry.Sites.Fpqc`, were read. They define
  the topology on the ambient scheme category and do not themselves record the
  bounded underlying-category choice. That choice is already supplied by the
  landed `def-sfb-stacks-big-site-category`, used directly here. No duplicate site
  definition or repair of the topology API is needed. Fpqc is not imported because
  the statement uses only the underlying category, with no coverings or sheaves.
- `def-weil-size-convention`: its record explicitly says it is a metatheoretic
  convention with no Lean declaration; the universes are explicit as described above.
- `def-sfb-stacks-big-site-category`: `stacksBigSiteObjects`,
  `StacksBigSiteCategory`, and `IsStacksBigSiteCategory`, in
  `Sheaf.AlgebraicGeometry.StacksBigSiteCategory`. Read the entire definitions and
  docstrings; hα is the complete four-clause admissibility predicate, not merely
  an assumption of the desired open-cover closure.
- `def-sfb-scheme-cardinal-size`: `AlgebraicGeometry.Scheme.cardinalSize`, in
  `Sheaf.AlgebraicGeometry.SchemeCardinalSize`, publicly reexported by the chosen
  category module. Read its full definition and source docstring.
- Proof dependency `lem-sfb-scheme-size-open-cover-bound`:
  `AlgebraicGeometry.Scheme.cardinalSize_le_openCover`, in
  `Sheaf.AlgebraicGeometry.SchemeSizeOpenCoverBound`, imported with plain `import`.
  The signature and proof docstring were read, including independent index universe
  and the countable term for the empty cover.
- Proof dependency `lem-sfb-big-site-bounded-size-representative` currently has
  no Lean record or module. It is not required to type the present statement:
  its full category and size notions are already available, and its mathematical
  content is clause (2) of the existing admissibility predicate. The module docstring
  records the original three-step argument, including this node, for stage 3.
  There is no missing notion requiring a new module here. This unstated proof
  dependency has no module to import yet.
- `Mathlib.AlgebraicGeometry.Restrict` supplies `Scheme.Opens.toScheme` and the
  induced open scheme structures.

Source reading: read sets.tex section-categories-schemes (definition of size),
equation-bound, Tag 000J(1)--(4), Tag 000Q and its proof, and Tag 000R(6) and its
proof; read topologies.tex Tag 021R(2). The node already corrects the empty-cover
error in the printed size bound through its proof dependency. No further source
correction is necessary. No `STATEMENT-DISPUTED` finding.

Edge checks: an empty cover is allowed as above; an arbitrary family of empty
opens also forces X empty; singleton covers and repeated opens are allowed;
T itself may be empty, in which case its size is still ℵ₀. Neither X nor Uᵢ
needs to be quasi-compact or quasi-separated. The index universe may exceed the
scheme universe: lifts express the actual cardinal bound rather than forcing
universe equality. The conclusion requires only a representative up to isomorphism,
not literal membership of X, as is needed for skeletal presentations under the
size convention.

Searches performed before writing:

- `msearch.py leanfinder`: “A scheme with an open cover bounded by size(T) to aleph
  zero belongs up to isomorphism to the chosen big fppf site containing T”. Eight
  hits, including Scheme.OpenCover, affine covers and small precoverages; no exact
  chosen-category bounded-open-cover closure result.
- `msearch.py loogle`: `"Scheme", "Small"`. Twelve hits, covering small precoverages,
  small-index coproducts, and small Grothendieck topologies; no exact result.
- `msearch.py grep`: `(cardinalSize|bigSite|bounded).*(cover|fppf)|(cover|fppf).*cardinal`
  in AlgebraicGeometry. Zero hits.
- `msearch.py leansearch`: “A scheme with an open cover of bounded size has an
  isomorphic representative in a chosen big fppf site”. Eight hits on ordinary
  open-cover and gluing constructions; no exact result.
- Direct `rg` for `cardinalSize|StacksBig|stacksBig|boundSize|BoundedSize` in
  `lean/Sheaf` and `lean/WeilConjectures`: found the existing size definition,
  admissible-category definition, and size estimate. These are used rather than
  redefined. Further searches for open-cover size/representative theorem names
  found no declaration of this statement.
- Direct search for the item ID in `lean/WeilConjectures`: no match. Search in
  `dag/lean_names_upstream.json` for the size/category names: no upstream match.
- Direct search for `openCover_cardinalSize|exists_iso_of_openCover` in Mathlib,
  `lean/WeilConjectures`, and `lean/Sheaf`: no preexisting declaration with the
  selected theorem name.

Validation: `scompile.py Q32 lem-sfb-big-site-open-cover-size-closure` compiled
this file both as its sandbox module (2.2 seconds) and at its library module path
(2.3 seconds), cleanly with no non-sorry warnings. The file explicitly sets
`autoImplicit false` and binds all universes and variables.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
