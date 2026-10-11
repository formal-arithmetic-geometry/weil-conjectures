## Worker report

Module: `Sheaf.AlgebraicGeometry.AffineFpqcDescent`. It states
`CategoryTheory.Over.DescentDatum.isEffective_of_isAffineHom_fpqc` with a `sorry`
proof. Source checked: Stacks Project, Descent, Lemma 35.37.1, Tag 0245,
at `https://stacks.math.columbia.edu/tag/0245`. The local
`literature/stacks-project/descent.tex` checkout is absent on this machine.

Statement correspondence:

- Schemes `S`, `X` and `f : X ⟶ S`: `{X Y : Scheme.{u}} (p : X ⟶ Y)`;
  `Y` is the node's `S` and `p` its `f`.
- The singleton family `{f}` is fpqc: `hp : Presieve.singleton p ∈
  Scheme.fpqcPrecoverage Y`. This is the precoverage of flat, jointly
  surjective, quasi-compact families; for a singleton it is the node's fpqc
  covering hypothesis, including an empty-base case.
- An `X`-scheme `V ⟶ X`: `{V : Over X}`, whose structure map is `V.hom`.
- The structure morphism is affine: `[IsAffineHom V.hom]`. Mathlib's class
  says the inverse image of every affine open is affine.
- The isomorphism `φ` of the two pullbacks and its cocycle: `(D :
  Over.DescentDatum p V)`. Its recorded upstream definition uses natural
  transport of points, whose docstring identifies it via Yoneda with exactly
  this pullback isomorphism and cocycle. The unit and naturality conditions
  follow from the cocycle and do not restrict the datum.
- The descended `U ⟶ S`, isomorphism `ψ : U ×_S X ⟶ V` over `X`, and
  compatibility `φ ∘ pr₀*ψ = pr₁*ψ ∘ can_U`: `D.IsEffective`.
  Its definition supplies `V₀ : Over Y`, `q : V.left ⟶ V₀.left`, an
  `IsPullback q V.hom V₀.hom p`, and invariance of `q` under every transport.
  The pullback square gives `ψ`, while invariance is the displayed
  compatibility equation via the same Yoneda identification.

Dependency declarations checked:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (Mathlib/AlgebraicGeometry/Scheme.lean).
- `def-weil-pbc-fpqc-covering`: `AlgebraicGeometry.Scheme.fpqcPrecoverage`
  (Mathlib/AlgebraicGeometry/Sites/Fpqc.lean).
- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom`
  (Mathlib/AlgebraicGeometry/Morphisms/Affine.lean).
- `def-pd-descent-datum`: `CategoryTheory.Over.DescentDatum` and
  `CategoryTheory.Over.DescentDatum.IsEffective`
  (WeilConjectures.CategoryTheory.Comma.Over.DescentDatum).
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, its projections
  and universal property (Mathlib/CategoryTheory/Limits/Shapes/Pullback/
  HasPullback.lean); Scheme has pullbacks (Mathlib/AlgebraicGeometry/
  Pullbacks.lean). These are implicit in the recorded descent definitions.

Edge cases: no nonempty or finite-type hypothesis is imposed on `X`, `Y`,
or `V`; the empty scheme and zero ring are included. The singleton cover of
an empty base is allowed. The result is universe-polymorphic in schemes,
with no characteristic assumption. The index set is the singleton only,
as specified by this node; no arbitrary-family assertion is claimed.

Searches for an existing statement:

- `msearch leanfinder "descent data for affine morphisms of schemes are
  effective for an fpqc covering"`: eight hits; none state effectivity of
  affine-scheme descent.
- `msearch loogle "Over.DescentDatum.IsEffective, IsAffineHom,
  fpqcPrecoverage"`: zero hits; the upstream descent predicate is not in
  Mathlib's Loogle index.
- `msearch grep "IsEffective|descent.*affine|affine.*descent"
  AlgebraicGeometry`: zero relevant Mathlib hits.
- `rg` in `WeilConjectures` and `lean/Sheaf` for descent datum, effectivity,
  and affine descent: upstream `isEffective_of_isFinite` requires a finite
  covering and an additional affine-neighbourhood hypothesis; no exact match.
- `rg` in Mathlib and upstream for the new full declaration name, and
  `grep -rn` for the node id in upstream: no match.

The proof docstring follows the node's eight steps and cites their nodes.
The server compile completed in 1.6 seconds with no errors or warnings.

## Second reading by F1

Independent comparison with the node and Stacks Project, `descent.tex`,
Lemma `lemma-affine` (Tag 0245), Definition `definition-descent-datum`
(Tag 023V), and the opening of the descending-affine-morphisms section:

- Base schemes `S`, `X` and map `f : X ⟶ S`: `{X Y : Scheme.{u}}`
  and `(p : X ⟶ Y)`, with `Y = S` and `p = f`. Exact; no field,
  characteristic, Noetherian, or finiteness hypothesis is introduced.
- One-member fpqc covering `{f}`: `(hp : Presieve.singleton p ∈
  Scheme.fpqcPrecoverage Y)`. Exact for the node's singleton, by the
  recorded `def-weil-pbc-fpqc-covering` match. The Stacks lemma is for an
  arbitrary family, but this node explicitly states its singleton case.
- Scheme `V` over `X` and its structure map: `{V : Over X}` and `V.hom`.
  Exact; `Over X` is the recorded project's category of schemes over `X`.
- Affineness of `V ⟶ X`: `[IsAffineHom V.hom]`. Exact by the declaration
  matched to `pqf-def-affine-morphism`: preimages of affine opens are affine.
- Descent isomorphism `φ` over `X ×_S X` and its cocycle over the triple
  product: `(D : Over.DescentDatum p V)`. Exact by the recorded
  `def-pd-descent-datum` declaration and its source: Yoneda transport is
  natural, self-trivial, and cocyclic, hence identifies with precisely that
  pullback isomorphism. `def-pc-fibre-product` is implicit in this
  identification. The self-trivial condition follows from the cocycle;
  it adds no mathematical hypothesis.
- Descended `U ⟶ S`, isomorphism `ψ : U ×_S X ≅ V` over `X`, and
  compatibility of `ψ` with `φ` and `can_U`: `D.IsEffective`. Exact by
  the recorded `IsEffective` definition: `∃ V₀ : Over Y`, a map
  `q : V.left ⟶ V₀.left`, `IsPullback q V.hom V₀.hom p`, and transport
  invariance of `q` for every test scheme and pair of points. The
  pullback condition supplies `ψ`; invariance is the compatibility
  equation after Yoneda. No affineness of the descended `U` is demanded
  by either statement.

Edge cases: `X`, `Y`, and `V` may be empty; the empty-base singleton cover
is included. An affine structure map includes the empty scheme and the
zero-ring case. The node has no arbitrary index set or numeric parameter:
its index set is a singleton, and `n = 0` is relevant only to the
underlying fpqc-cover definition over an empty base. The `Scheme.{u}`
binder is universe-polymorphic and adds no characteristic restriction.

Independent searches: `msearch leanfinder` with "effective descent of
affine morphisms along fpqc covering of schemes" returned property-descent
results, not effectivity; `msearch loogle` with
`Over.DescentDatum.IsEffective, IsAffineHom, fpqcPrecoverage` returned no
hit (the project predicate is absent from that index); `msearch grep`
with "effective descent affine fpqc scheme" returned no hit. `rg` with
"effective.*descent|descent.*effective|descent.*affine|affine.*descent"
over Mathlib, upstream `WeilConjectures`, and this project's `lean/Sheaf`
found only narrower or different results, including finite descent and
descent of the property of being affine. `rg` for the full proposed name
and node id found no existing declaration. I opened the finite descent
theorem: it assumes finite locally free `p` and an affine-neighbourhood
condition on `V`, so it is not this node.

No mismatch or code change was needed. The module has one named theorem,
proof `sorry`, no hollow definitions, and an eight-step source docstring
following the node's proof. The declaration binds its universe and all
variables. The node's `lean.statement` matches its signature. Sandbox
compile succeeded without diagnostics.
