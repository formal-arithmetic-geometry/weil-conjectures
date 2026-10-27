## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePushoutEtaleBaseChange` states
`AlgebraicGeometry.AlgebraicSpace.affineThickeningPushout_etaleBaseChange`.
It also constructs `pushoutEtaleBaseChangeMap`, the actual map of sheaf fibre
products induced by a commuting triangle. Its data are `Limits.pullback.map`,
bundled by `ObjectProperty.homMk`; its two equation proofs are discharged from
the triangle equation. No definition contains postponed data or a postponed
proof, and the sole theorem has proof `sorry`.

Hypothesis and conclusion correspondence:

- The base scheme is `{B : Scheme.{u}}`, with explicit universe `u`. All spaces
  belong to the recorded category `AlgebraicSpace B`, whose morphisms are
  natural transformations of the underlying fppf sheaves.
- The spaces A, A+, C and Q are `(A A' C Q : AlgebraicSpace B)`; A+ is called
  `A'` in Lean. No scheme, flatness or finite-presentation hypothesis is imposed
  on these four spaces.
- The maps of the original square are `i : A ⟶ A'`, `a : A ⟶ C`,
  `j : C ⟶ Q` and `b : A' ⟶ Q`.
- The representable closed-immersion condition is `hi : IsRepresentableWith
  (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`. This quantifies over
  every scheme mapping to the target, supplies an actual representing scheme
  pullback and requires its projection to be a closed immersion.
- The other thickening condition is
  `hiTop : IsHomeomorph (mapPoint i.hom.hom)`. The existing point topology is
  final for representable étale scheme charts and equals the atlas quotient
  topology. There is no finite-order or bounded-nilpotence hypothesis.
- Affineness is `ha : IsRepresentableWith
  (fun _ _ p ↦ IsAffineHom p.left) a.hom.hom`, including representability and
  affineness of every scheme base change.
- The original universal property is `hp : IsPushout a i j b`, in the category
  of algebraic spaces over B. It includes the compatibility `hp.w` and the
  universal property against every algebraic-space target over B.
- The scheme E over B is `E : Over B`, regarded as its actual representable
  algebraic space by `schemeSpace E`. The specified map is
  `e : schemeSpace E ⟶ Q`, and its representable étaleness is
  `he : IsEtale e.hom.hom`.
- The three restrictions are exactly `enlargedFibreProduct e j` (C_E),
  `enlargedFibreProduct e (a ≫ j)` (A_E), and
  `enlargedFibreProduct e b` (A_E+). These are the chosen pullbacks of the
  underlying sheaves, bundled with their algebraic-space property.
- The overlap maps are `pushoutEtaleBaseChangeMap e (a ≫ j) j a rfl` and
  `pushoutEtaleBaseChangeMap e (a ≫ j) b i hp.w.symm`. The latter uses precisely
  the equality `i ≫ b = a ≫ j`. The helper keeps the E-coordinate fixed and
  applies respectively a or i to the A-coordinate.
- The two maps from C_E and A_E+ to E are the existing
  `enlargedFibreProductFst e j` and `enlargedFibreProductFst e b`.
- The conclusion is `IsPushout` for precisely these four maps. By the
  categorical pushout universal property this states that, for every
  `H : AlgebraicSpace B`, compatible maps C_E → H and A_E+ → H extend uniquely
  to E → H. Existence gives surjectivity of the displayed restriction map in
  the node; uniqueness gives injectivity. Thus the explicit bijection and
  the categorical pushout clause are the same conclusion, with no additional
  conjunct or restriction on targets.

Recorded dependency declarations used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith` and `AlgebraicSpace.IsEtale`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, the recorded closed-immersion notion.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, used by the existing bundled
  fibre-product definition. Its full signature and docstring were read,
  together with `etaleCover_pullback` and `etale_fibreProduct_isScheme`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `AlgebraicSpace.schemeSpace`, `AlgebraicSpace.enlargedFibreProduct` and
  `AlgebraicSpace.enlargedFibreProductFst`. Their already-landed definition
  owners `def-trf-scheme-algebraic-space` and
  `def-sfb-space-sheaf-fibre-product` are added to `stmt_deps`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace`, owned by the added landed dependency
  `def-a1-space-point-topology`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.mapPoint`, owned
  by the added landed dependency `def-sfb-proper-curve-moduli`. Only this
  point-map construction is used, with no proper-curve hypothesis.
- `def-weil-size-convention` is a metatheoretic convention; the explicit
  universe and the dependency category implement it, with no new object.
- Mathlib's `IsAffineHom`, `CategoryTheory.IsPushout`, `Limits.pullback.map`
  and `ObjectProperty.homMk` supply the remaining standard notions and maps.

Proof-only imports are the available recorded modules
`Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout` and
`Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`. The former's three
signatures and docstrings were read. The other three proof-only nodes
`lem-sfb-space-thickening-base-change`,
`lem-sfb-space-pushout-etale-morphism-criterion` and
`lem-sfb-space-etale-thickening-detects-iso` have no recorded Lean modules in
the read snapshot; their proof steps are retained in the theorem docstring.
They are unnecessary to type the statement.

Source read: `literature/stacks-project/spaces-pushouts.tex`,
`lemma-equivalence-categories-spaces-pushout-flat` (Tag 07W3), in particular
part (5) and the final assertion that the flat counit G(F(W')) → W' is an
isomorphism, and the proof of those assertions. The étale scheme instance
is exactly the node's assertion. No statement correction was needed.

Edge cases checked before writing: E may be empty; i may be an identity;
A may be empty; the base and other spaces may be empty; no nonempty,
separated, quasi-compact, Noetherian, finite-order, flat or locally finitely
presented assumption has been inserted. The universal property allows every
target H, including empty H. Arbitrary non-scheme A, A+ and C are permitted.
The scheme E and all test schemes have exactly the universe of the recorded
algebraic-space interface; no site-universe identification has been added.
The map on the overlap is fixed by hp.w rather than an arbitrary compatible
map or a choice from an existence theorem.

Searches for an existing statement or duplicate construction:

- `msearch.py leanfinder`, query “Etale base change preserves a pushout of
  algebraic spaces along a thickening and an affine morphism”: eight hits,
  including scheme étale permanence and Spec converting ring pushouts to
  scheme pullbacks. None states this algebraic-space pushout assertion.
- `msearch.py leansearch`, query “An etale scheme base change of an algebraic
  space affine thickening pushout is a pushout”: eight hits on étale
  base change, tensor products and scheme affine permanence; no match.
- `msearch.py loogle`, query `"IsPushout", "Etale"`: zero hits.
- `msearch.py grep`, query
  `pushout.*[Ee]tale|[Ee]tale.*pushout|thickening.*pushout`, restricted to
  Mathlib/AlgebraicGeometry: zero hits. The same direct Mathlib rg search
  gives zero hits.
- `rg` with the pushout/étale expression in `lean/WeilConjectures` and
  `lean/Sheaf` finds ring étale pushout facts, torsor extension, finite-étale
  scheme gluing, Rees algebra results, and the existing affine-thickening
  pushout theorem. None gives this statement for algebraic-space targets.
- `rg` for this item's exact id in `lean/WeilConjectures`: zero hits.
- `rg` for `pushoutEtaleBaseChangeMap` and
  `affineThickeningPushout_etaleBaseChange` in Mathlib, WeilConjectures,
  Sheaf and `dag/lean_names_upstream.json`: zero hits before creating the
  module. Existing schemeSpace, fibre-product and point-map owners were
  located in `dag/nodes` and reused; no new definition node is needed.

Validation: the module passed the prescribed `scompile.py N5
lem-sfb-space-pushout-etale-base-change` server compile, both as a sandbox
module and at its intended library module name, with no errors or unexpected
warnings. All variables and universes are explicitly bound; no line exceeds
100 characters. There is no STATEMENT-DISPUTED flag or unresolved node fault.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
