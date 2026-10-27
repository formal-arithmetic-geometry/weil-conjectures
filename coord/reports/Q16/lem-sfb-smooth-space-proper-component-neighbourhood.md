## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothSpaceProperComponentNeighbourhood` states
`AlgebraicGeometry.AlgebraicSpace.exists_proper_smooth_component_neighbourhood`.
Its sole theorem has proof `sorry`. Four canonical, real-data helper definitions expose
Yoneda scheme maps, structural scheme maps, scheme tests over a scheme, and the second
projection of the existing sheaf pullback. There are no new mathematical notions,
postponed helper theorems, new nodes, dependency repairs, or statement corrections.

Hypothesis and clause correspondence:

- The locally Noetherian scheme is `{S : Scheme.{u}} [IsLocallyNoetherian S]`.
  `X : AlgebraicSpace S` and `f : X ⟶ schemeSpace (Over.mk (𝟙 S))` express the given
  algebraic space over S and its structural morphism. This codomain is the representable
  terminal S-scheme; f is its unique structural arrow, not additional geometric data.
- Separatedness is `hf_sep : MapIsSeparated f`; smoothness is
  `hf_sm : MapIsLocally (@Smooth) f`; local finite presentation is
  `hf_lfp : MapIsLocallyOfFinitePresentation f`. There is no quasi-compactness
  hypothesis on f or X.
- The geometric point is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`
  with `s : Spec (.of Ω) ⟶ S`. It retains the specified field and morphism.
- The geometric fibre is the existing `enlargedFibreProduct f (smoothComponentBaseMap s)`.
  Its open component is `Copen : OpenSubspace` of that fibre.
  `C : AlgebraicSpace S`, `eC : C.obj.obj ≅ Copen.val.toFunctor`, and `hiC` identify
  a model of precisely this open subfunctor and fix its inclusion iC. Providing a model
  introduces no geometric restriction: an open subspace is automatically algebraic.
- `hC` says the point image of Copen is `connectedComponent c` for an actual fibre
  point c. Mathlib's component is maximal connected and contains c; this includes
  both nonemptiness and the full connected-component condition, not just connectedness.
- `hC_proper` is properness of the composite of iC with the canonical projection
  to the scheme `Spec Ω`, using `MapIsProper` exactly as recorded for algebraic spaces.
- The conclusion quantifies over `(T : Scheme.{u}) (t : T ⟶ S) (_ : Etale t)` and
  `(st : Spec (.of Ω) ⟶ T) (hst : st ≫ t = s)`. Thus the neighbourhood is a scheme
  and the specified Ω-valued point lifts unchanged.
- `Vopen : OpenSubspace (enlargedFibreProduct f (smoothComponentBaseMap t))`, with
  its model V, isomorphism eV, and inclusion equation, gives an actual open subspace
  of `X ×_S T`. The equation defining p fixes its map to T as the second projection.
- `MapIsProper p` and `MapIsLocally (@Smooth) p` give properness and smoothness.
  Finite presentation is the conjunction of `MapIsLocallyOfFinitePresentation p`,
  `MapIsQuasiCompact p.hom.hom`, and
  `MapIsQuasiCompact (Limits.pullback.diagonal p.hom.hom)`. The last condition is
  quasi-separatedness, so no finiteness clause is omitted.
- For every field-valued point `z : Spec K ⟶ T` and every field extension L/K,
  `ConnectedSpace (Point (...))` asserts nonemptiness and connectedness of the actual
  sheaf fibre over `Spec L → Spec K → T`. The identity extension is included.
  This is equivalent to nonempty geometrically connected fibres at each scheme point:
  residue-field points are included, and all other field-valued tests are their field
  extensions. K and L range over `Type u`, the established scheme-test size convention.
- Finally k maps C to V, the displayed equation fixes its composite to X, and
  `IsPullback k (iC ≫ smoothComponentFibreSnd ...) p
  (smoothComponentSchemeMap (Over.homMk st hst))` identifies C with the st-fibre.
  The square fixes the Ω projection as well. Consequently the two fibre inclusions
  into `X_s` agree, which is equality as open subspaces, not just an abstract
  isomorphism of C with some fibre.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are inline
  as recorded by def-weil-geometric-point. Its alternative residue-field signature
  `Scheme.SpecToEquivOfField` in Mathlib.AlgebraicGeometry.ResidueField was also read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsAlgebraicSpace`; no private algebraic-space predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsSeparated`, `MapIsLocallyOfFinitePresentation`, `MapIsProper`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  `pointImage`, using the recorded `Point` classes from AlgebraicSpacePointClasses.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, the algebraic-space closure used by the construction.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedFibreProduct`. The already-landed definition owners
  `def-trf-scheme-algebraic-space` and `def-sfb-space-sheaf-fibre-product` are added
  to stmt_deps; their node records and the full definitions/docstrings were read.
- `ProperCurveModuli.MapIsQuasiCompact` (namespace AlgebraicGeometry.AlgebraicSpace)
  supplies the existing quasi-compactness predicate. No substitute is defined.

Every recorded proof-dependency module is imported as a non-public import unless it
already supplies statement vocabulary via a public import. The Mathlib leaves for
relative separable closure, cofiltered reindexing, and smooth-flat are imported too.
The proof dependencies currently without a Lean record are not restated: they are
not needed to type this statement. The theorem docstring carries all nine proof steps
and their node citations.

Sources read: spaces-more-morphisms.tex at lemma-split-off-proper-part-henselian
(Tag 0CWI) and lemma-proper-flat-geom-red (Tag 0E1E); spaces-limits.tex at
lemma-descend-opens (Tag 0827) and lemma-eventually-proper (Tag 08K1).
These agree with the node's description of an assembled consequence. The finite-type
restriction is made only on a quasi-compact open around C in the proof, never on X.

Edge cases: the empty ambient fibre cannot satisfy hC, since a point c must exist;
empty C is excluded by that same witness. An empty S has no geometric point s.
An infinite disjoint union of smooth components is allowed because no compactness
of X or f is assumed. Identity field extensions occur in the fibre clause, in every
characteristic. Ω is not required finite, algebraic, or finitely presented over the
residue field. The eC/iC and eV/iV clauses fix representation only and add no
smoothness or finiteness assumptions. The pullback square does not assert an
unjustified literal equality between differently constructed objects.

Searches actually run:

- msearch.py leanfinder: "A proper connected component of a smooth geometric fibre
  extends to a proper smooth open subspace after an etale pointed neighbourhood".
  Eight hits: scheme smooth-chart and étale declarations, no exact algebraic-space
  proper-component-neighbourhood theorem.
- msearch.py loogle: "IsConnected, connectedComponent, Smooth, Proper, Etale".
  Service returned zero hits with `unknown identifier 'Smooth'`; this query was
  inconclusive, not evidence of absence.
- msearch.py grep: `proper.*component|component.*proper`, subdirectory AlgebraicGeometry.
  Four incidental occurrences in geometrically reducedness and module files,
  no matching statement.
- rg of WeilConjectures/AlgebraicGeometry and Sheaf/AlgebraicGeometry for
  `proper.*component|component.*proper|connectedComponent|IsConnected` found scheme
  connected-component results and the existing SpaceSteinFactorizationAffine use of
  `ConnectedSpace` for all field extensions, but no match for the item.
- grep of WeilConjectures for the exact item id found no declaration.
- rg of Mathlib, WeilConjectures, Sheaf, and dag/lean_names_upstream.json for all five
  new declaration names found no collisions. Source searches for schemeSpace and
  enlargedFibreProduct located the existing construction and both definition owners.

Validation: scompile.py compiled the sandbox and library module without errors or
warnings (40.6 s and 8.9 s). The first attempt reached a deterministic elaboration
heartbeat limit because the domain of structural `Over.homMk` maps was left to
inference; explicit-source canonical helper definitions resolved it under the
unchanged 60-second limit. No timeout or heartbeat limit was raised.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
