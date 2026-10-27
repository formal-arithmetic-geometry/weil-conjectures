## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceClosedLimitStabilization` states
`AlgebraicGeometry.AlgebraicSpace.exists_isIso_projection_of_closed_limit_locallyOfFinitePresentation`.
Its sole proof is `sorry`. No definitions, additional theorems, or axioms are introduced.
The source read is `literature/stacks-project/spaces-limits.tex`, Tag 0828,
`lemma-finite-type-eventually-closed`, clause (3) and its proof (lines 1234–1300),
specialized to Y = X by the identity map, exactly as the node requests.

Hypothesis and clause correspondence:

- S is an arbitrary scheme: `{S : Scheme.{u}}`.
- Algebraic spaces over S are the recorded `AlgebraicSpace S`, the full subcategory
  of big-fppf sheaves with representable diagonal and a surjective étale scheme atlas.
  `B : AlgebraicSpace S` is the arbitrary space base. No separation assumption is added.
- The universe convention is explicit `universe u`, with schemes and index set both
  in universe u, and the existing larger category of sheaves and spaces unchanged.
- A small nonempty directed set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. A preorder is intentional; neither linearity,
  antisymmetry, nor an initial index is required.
- The inverse system over B is `D : Iᵒᵖ ⥤ Over B`. Its stages are
  `(D.obj i).left`, their structure maps are `(D.obj i).hom`, and the transition maps
  are `(D.map f).left`. The functor and slice morphism laws supply exactly the
  inverse-system identities and compatibility with B.
- Closed immersion transitions are `hclosed`: `IsRepresentableWith
  (fun _ _ p ↦ IsClosedImmersion p.left) (D.map f).left.hom.hom` for every transition.
  This uses the existing representability predicate and the Mathlib scheme predicate.
  It asserts scheme representation and closed immersion of each scheme base change,
  precisely the node's explicitly supplied meaning. The representability witnesses
  are genuine pullback squares, rather than arbitrary comparison maps.
- Every stage is quasi-compact: `hqc` supplies an S-scheme U and a presheaf map a to
  that stage with `CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a`.
  This is exactly the node's atlas definition and does not require the atlas to be affine.
- Every structure map is locally of finite type: `hlft` uses the existing
  `MapIsLocally (@LocallyOfFiniteType) (D.obj i).hom`, which tests every compatible
  étale scheme chart pair.
- The limit exists in algebraic spaces over B: `(c : Cone D) (hc : IsLimit c)` is a
  cone and its universal property in `Over B` itself. Its vertex `c.pt.left` is C,
  its structure map is `c.pt.hom`, and its canonical projections are
  `(c.π.app (op i)).left`. No sheaf-limit preservation assumption is imposed.
- The limit map to B is locally of finite presentation: `hlfp` is the existing
  `MapIsLocallyOfFinitePresentation c.pt.hom`, the compatible-chart definition.
- The conclusion is `∃ i₀ : I, ∀ i : I, i₀ ≤ i →
  IsIso (c.π.app (op i)).left`. It says every projection on the eventual tail is an
  isomorphism of algebraic spaces. These projections already commute with B by their
  slice type; an inverse is automatically over B, so this also expresses an
  isomorphism over B. It asserts the canonical projections themselves are invertible.

Recorded dependency declarations used and source signatures/docstrings read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (locally ringed spaces locally isomorphic to spectra, and their morphisms).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, and `IsSurjective`, all at the original universe u. The last three
  operate on presheaf natural transformations, hence `.hom.hom` in the statement.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme` supply the sheaf fibre-product and atlas framework.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally` and
  `MapIsLocallyOfFinitePresentation`. Its existing owner node
  `def-sfb-space-morphism-properties` is added to `stmt_deps` under the rule allowing
  landed definition dependencies. It was absent from the inherited list; the node's
  prose already specifies these chart tests. No statement correction is needed.
- `def-weil-size-convention` is metatheoretic; it supplies no declaration or import.

Plain proof imports cover every currently stated proof dependency: the chart-test
module above; `Sheaf.AlgebraicGeometry.ClosedLimitLfpStabilization` and its
`AlgebraicGeometry.exists_isIso_limitProjection_of_isClosedImmersion_of_locallyOfFinitePresentation`;
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` with `schemeSpace`;
`Mathlib.AlgebraicGeometry.AffineScheme` with `Scheme.compactSpace_of_isAffine`;
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` with `quasiSeparatedSpace_of_isAffine`;
`Mathlib.AlgebraicGeometry.Morphisms.Etale` with `Etale`; and
`Mathlib.AlgebraicGeometry.Sites.Fpqc` with `Scheme.fppfTopology`.
The remaining proof-only nodes `lem-sfb-space-relative-lfp-permanence`,
`lem-trf-space-qc-finite-affine-atlas-refinement`, and
`lem-sfb-space-affine-limits-schematic-stages` have no recorded Lean module at reading
time. Their imports are therefore omitted, and the six-step source proof is retained
in the theorem docstring for stage 3. None is required to type the statement.

Edge cases checked against the source and signature: a singleton or constant system;
an empty stage and hence an empty tail and limit (the allowed atlas is the empty
scheme, Spec 0); an empty limit with initially nonempty stages; an index preorder
with no least element; distinct mutually comparable indices; and an arbitrary,
possibly empty or non-quasi-compact base B. There is no nonemptiness assumption on
any space, no qcqs or finite-presentation requirement on a stage, and no compactness
assumption on B. The empty index set is excluded exactly as in the node. Closed
immersions of arbitrary presentation are allowed. No characteristic is fixed.

Searches actually run, recorded also by `msearch.py` in `searches.jsonl`:

- LeanFinder: "Directed inverse limit of quasi compact algebraic spaces with closed
  immersion transitions stabilizes if the limit is locally of finite presentation".
  Eight results, including scheme finite-type factorization/equality lemmas and
  `LocallyOfFinitePresentation`; none states the algebraic-space assertion.
- Loogle: `"IsClosedImmersion", "IsLimit"`: zero hits.
- Mathlib grep via msearch, subdirectory `AlgebraicGeometry`:
  `AlgebraicSpace|[Cc]losed.*[Ll]imit.*[Pp]resentation|[Ll]imit.*[Ss]tabiliz`:
  zero hits.
- LeanSearch: "A directed inverse limit of quasi compact algebraic spaces with
  closed immersion transitions stabilizes when its limit is locally finitely
  presented over the base". Eight hits, including scheme compactness and open-set
  descent, inverse systems, and first-order direct limits; no exact match.
- Project searches: `rg` for `IsQuasiCompact|IsClosedImmersion|MapIsLocally` and for
  closed-limit/stabilization patterns in `lean/Sheaf/AlgebraicGeometry`, and
  `AlgebraicSpace|closed.*[Ll]imit|[Ll]imit.*[Ss]tabiliz` in
  `lean/WeilConjectures`. Read the scheme-only stabilization declaration and the
  existing space morphism properties. No algebraic-space stabilization declaration
  was found. `grep -rn lem-sfb-space-closed-limit-stabilization
  lean/WeilConjectures` returned no match. `dag/lean_names_upstream.json` likewise
  has no attachment for this item. The proposed full declaration name is new.

There are no new nodes, dependency repairs, statement corrections, or disputes.
The recorded node copy changes only `lean` and adds the landed definition dependency.

Validation: prescribed `scompile.py` compiled this file in both sandbox and actual
module contexts with no messages, in 1.5 s and 1.4 s respectively. `autoImplicit` is
explicitly false, and every Lean line is at most 100 characters.

## Second reading by Q07

This is a second reading within the dispatcher worker session; no other agent was
started, as required by the assignment. The maintainer performs the independent review.
I reopened the node, the source clause and the completed signature. The diagram is
in `Over B`, not merely over S: this accounts for the base in all transitions and
in the limit universal property. I checked each `.left` against the slice type and
each `.hom.hom` against the full-subcategory/sheaf wrappers. The atlas codomain is
the presheaf of the actual stage, and `CompactSpace` applies to its scheme source.
The local finite-type hypotheses apply to stage-to-B structure maps, and the local
finite-presentation hypothesis applies to the limit-to-B structure map. The only
inequality in the conclusion is `i₀ ≤ i`, followed by invertibility of the canonical
projection at precisely `op i`. No object has been replaced by a scheme or by a
chosen chart, and no separation or affine-stage hypothesis has entered the statement.
The existing chart-property node was added as a dependency after this interface check.
The final signature has no remaining mismatch with any hypothesis or clause of the node.
