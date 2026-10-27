## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFpOverSpaceLimitDescent` states
`AlgebraicGeometry.AlgebraicSpace.fp_over_space_limit_descent`, with one postponed
proof and no additional theorem obligations. Its helper `spaceLimitPullbackIso`
is the actual composite of equality transport and Mathlib `Over.pullbackComp`.
It supplies the canonical comparison required to say that a descended map pulls
back to the prescribed map. No arbitrary comparison map or isomorphism is assumed.

The previous worker ending concerned an unchanged stage-1 split. The current
queue assigns stage 2, the node is split and reviewed, and has no Lean record.
The stage handoff paragraph of the current brief explicitly permits this statement
delivery. The accepted natural-language statement and proof remain unchanged.

Clause-by-clause correspondence:

- A scheme S and algebraic spaces over S: `{S : Scheme.{u}}` and
  `AlgebraicSpace S`, the recorded fppf-sheaf full subcategory, throughout.
- The size convention: explicit universe `u`, with schemes in `Scheme.{u}`,
  coefficient sets in `Type u`, and the small directed index set `I : Type u`.
  No independent smaller index or test-scheme universe is introduced.
- Quasi-compactness of every base: `hqc` is
  `CompactSpace (Point (D.obj (op i)).obj.obj)`, using the existing atlas topology.
- Absolute quasi-separatedness of every base: `hqs` tests compactness of
  `Point (Limits.pullback a b)` for every pair of affine scheme maps into the
  base. This is exactly the equivalent criterion (3) of Properties of Spaces,
  `lemma-characterize-quasi-separated` (read in spaces-properties.tex), already
  used in the landed IntegralSpaceFinitePresentationLimit module. It imposes
  no quasi-separatedness or separatedness on S. It is equivalent to the
  absolute diagonal over Spec Z being quasi-compact, as required.
- A nonempty directed set: `[Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. Opposite preorder arrows give the inverse direction.
- The inverse system: `D : Iᵒᵖ ⥤ AlgebraicSpace S` includes all transition
  identity and composition laws. `ha` requires `MapIsAffine` for each
  transition corresponding to `i ≤ j`, with no schematic-base restriction.
- The limit B and its canonical projections: `c : Cone D`, `hc : IsLimit c`,
  vertex `c.pt`, and `c.π.app (op i)`. A supplied limit cone states the
  proposition for any chosen limit, without a further existence assumption.
- Local finite presentation is `MapIsLocallyOfFinitePresentation`, exactly
  the recorded compatible-etale-chart test; morphism quasi-compactness is
  `MapIsQuasiCompact f.hom.hom`; relative quasi-separatedness is
  `MapIsQuasiCompact (pullback.diagonal f.hom.hom)`. Every occurrence of
  finite presentation is the conjunction, or implication binders, of these
  three conditions. Finite type is not an additional hypothesis.
- Object descent is the first conjunct: every `Z`, `f : Z ⟶ c.pt` with
  those three properties admits `i`, `Zi`, `fi : Zi ⟶ D.obj (op i)` with
  the same three properties, and an isomorphism in `Over c.pt.obj`
  between its actual sheaf pullback and `Over.mk f.hom`. Sheaf fibre products
  are algebraic spaces by the recorded fibre-product theorem; the full
  subcategory has exactly the same morphisms and isomorphisms. Thus this
  is precisely a B-isomorphism, with no replacement of Z by a scheme.
- Map descent is the second conjunct: arbitrary finitely presented f and g
  over stage i and arbitrary `α` between their pullbacks to B admit j,
  `h : i ≤ j`, and a map β between their actual pullbacks to B_j. The
  displayed equation identifies α with the pullback of β, conjugated by
  `spaceLimitPullbackIso` at f and g. Its equality argument is specifically
  `congrArg (fun k ↦ k.hom) (c.w (homOfLE h).op)`, the cone equation.
- Eventual equality is the third conjunct: arbitrary maps α and β at i
  whose pullbacks to B are equal have equal pullbacks at a stage j ≥ i.
  Maps originally given at different stages are first moved to a common
  stage by directedness; therefore the common-stage formulation includes
  the later-common-stage clause of the node.
- All B_i, Z, W, Zi remain algebraic spaces. None is required to be a scheme,
  representable, separated, nonempty, or equipped with a chosen atlas.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsRepresentableWith`, `IsAlgebraicSpace`, with sheaf maps `.hom.hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `pointTopologicalSpace`; its imported Point is the recorded quotient of
  field-valued representatives.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocallyOfFinitePresentation`, defined by `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`: `MapIsAffine`.
  Its owning, already-landed node `def-sfb-space-affine-quasifinite-properties`
  is added to stmt_deps, as authorized for landed statement prerequisites.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` ensures that the actual sheaf pullbacks
  used in the signature represent algebraic-space pullbacks.
- Mathlib `Over.pullback`, `Over.pullbackComp`, `eqToIso`, `Cone`, and
  `IsLimit` supply the canonical categorical constructions.

Proof imports include the available recorded
`AlgebraicSpaceRepresentableEtaleSchemeTests` module, and Mathlib
AffineScheme and Morphisms.QuasiSeparated for the affine-scheme qcqs leaf.
Other proof dependencies have no recorded Lean module on this base, so
there is no module to import for those proof-only nodes. Their complete
accepted proof is retained in the main theorem's docstring; the theorem
proof is only `sorry`. There are no missing statement notions to add.

Edge cases checked before stating:

- Empty index sets are explicitly excluded by the source's directed-set
  convention and by `[Nonempty I]`; a singleton constant system gives
  identity descent and equality.
- Empty bases and empty spaces are allowed. Every finite-presentation
  condition and every map/isomorphism clause remains the actual condition
  on those objects; no nonemptiness is imposed on a space or its points.
- A constant system with a non-scheme qcqs algebraic space is included;
  all base and object binders use AlgebraicSpace rather than Scheme.
- Non-separated and even non-quasi-separated auxiliary S is included:
  hqs tests the absolute affine-pair criterion, not the diagonal over S.
- Equal indices and preorder-equivalent indices use the canonical transition
  and cone equations. No strict increase or antisymmetry is required.
- In the map clause the canonical comparison is oriented from direct
  pullback to iterated pullback, and its inverse returns to the direct
  target. Thus the equation has exactly the desired source and target.

Searches for an existing statement (2026-10-23):

- msearch.py leansearch, query “Finitely presented algebraic spaces descend
  along inverse limits with affine transition morphisms”: eight hits,
  including scheme affine-open and global-section descent in
  AffineTransitionLimit, and scheme finite presentation/flat descent.
  None states algebraic-space object/map/equality limit descent.
- msearch.py leanfinder, query “Algebraic spaces of finite presentation
  descend over inverse limits”: eight hits, scheme local finite presentation,
  its stability and flat descent. None is this algebraic-space theorem.
- msearch.py loogle, query “AlgebraicSpace, OfFinitePresentation”:
  zero hits; AlgebraicSpace is not a Mathlib identifier.
- msearch.py grep, query `AlgebraicSpace|descend.*[Ff]inite[Pp]resentation`
  in AlgebraicGeometry: three hits, all scheme FlatDescent/LocalFlatDescent.
- rg of WeilConjectures for AlgebraicSpace/algebraic space and this node id:
  no matching statement or definition.
- rg of Sheaf for this node id and 07SK: no existing statement. Focused
  searches of the space modules found MapIsAffine, MapIsQuasiCompact,
  and MapIsLocallyOfFinitePresentation and these existing notions are used.
  IntegralSpaceFinitePresentationLimit is a different theorem (Tag 09YA)
  and provided a checked precedent for the absolute affine-pair test.
- The DAG's scheme-base descent node and affine-base category node are
  restricted-base theorems and are not duplicates of this full-base item.

Source read: spaces-limits.tex, lemma-descend-finite-presentation (Tag 07SK),
including its object and full-faithfulness paragraphs; spaces-properties.tex,
lemma-characterize-quasi-separated, including all three equivalent conditions
and its proof. The accepted 11-step node proof was read in full and rendered
in the theorem's eight-paragraph proof docstring without changing its route.

Validation: scompile.py checked this module both under the sandbox module name
and its final library module name, with exit 0 and no warnings (15.6 s and
18.5 s respectively). The helper contains real data. Only the main theorem
has sorry. Every binder and the universe are explicit. No statement fault
or STATEMENT-DISPUTED issue was found.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
