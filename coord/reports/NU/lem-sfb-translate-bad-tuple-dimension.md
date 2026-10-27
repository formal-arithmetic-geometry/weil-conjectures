## Worker report

The module `Sheaf.AlgebraicGeometry.TranslateBadTupleDimension` states
`AlgebraicGeometry.AlgebraicSpace.TranslateBadTuple.translate_bad_tuple_dimension`,
with its proof `sorry`. Its nine preceding definitions/abbreviations are explicit
helpers for this node's own tuple, incidence, geometric-fibre and image constructions;
they introduce no independent geometric notion and contain no postponed data or proofs.
No source statement is corrected.

Hypotheses, matched to the node:

- The Noetherian scheme T is `S : Scheme.{u}` with `[IsNoetherian S]`, not merely
  locally Noetherian. This includes quasi-compactness, following Mathlib's definition.
- The algebraic space H is `H : AlgebraicSpace S`. Its group structure, without
  commutativity, is the actual group-valued functor `F : (Over S)ᵒᵖ ⥤ GrpCat.{u}`
  with `e : F ⋙ forget GrpCat ≅ H.obj.obj`. Multiplication, inverse and identity
  are the group operations in each value of F; functoriality says restrictions
  preserve them. The natural isomorphism identifies these operations with H's
  functor of points. It is not an arbitrary map or an assumed scheme presentation.
- `hH : IsSmoothIntegralGroupSpace H` is the existing conjunction of chartwise
  smoothness, closed relative diagonal, chartwise local finite presentation,
  quasi-compact structure map and diagonal, and integral geometric fibres. This
  predicate does NOT take a `CommutativeSpaceGroup`; its definition is independent
  of the commutative group structure defined elsewhere in that same module.
  `GroupSpaceIntegralFibres` means irreducible (therefore nonempty) point spaces
  and reduced etale scheme charts of every geometric fibre, exactly integrality.
- The open subspace is the existing `V : OpenSubspace H`, with
  `hVqc : IsCompact (pointImage V.val.ι)`. The open immersion identifies its point
  space homeomorphically with this subset, so this is precisely absolute
  quasi-compactness of V. No relative quasi-compactness is silently substituted.
- `hV` says `Nonempty (V.val.obj (op (Over.mk s)))` for every algebraically closed
  field K and `s : Spec K ⟶ S`. This means V meets every geometric fibre: a
  nonempty finite-type algebraic space over an algebraically closed field has
  a rational point, as seen on a finite-type etale scheme chart. Conversely a
  section is such a point. The finite-type condition is provided by hH.
- `d : ℕ` includes d=0; `hd` says the topological Krull dimension of every
  geometric fibre is the same d. The fibre helper is exactly the existing
  presheaf pullback of the structure map along Spec K -> S.
- `n : ℕ`, `hn : 1 ≤ n` are the integer n>=1, with no extra bound involving d.
  All fields and test schemes use the scheme universe u, matching the algebraic
  space API; there are no auto-bound universes or variables.

Constructions and every conclusion, matched to the node:

- `tuples P n` has actual sections `Fin n → P.obj U` and componentwise
  restriction. The theorem supplies algebraic spaces X and M with natural
  isomorphisms `eX` and `eM` to these presheaves, for n and n+1 respectively.
  These are H^n and H x H^n over S, on every test scheme. They are supplied
  in the conclusion, not added as hypotheses. Their representing objects are
  determined up to the usual unique compatible isomorphism. Nothing chooses
  data from an undetermined `sorry`-existence theorem.
- M's coordinate 0 is x and coordinate `j.succ` is g_j. `difference F n j`
  is literally `g_j⁻¹ * x`, not `x * g_j⁻¹`. `tail` is the actual projection
  forgetting x. Their functor/naturality proofs are structural proof fields
  in real constructions, not independent mathematical theorems.
- `E : ClosedSubspace M` has the existing reducedness predicate and image
  exactly `incidenceSupport F e V n M eM`. That support requires the image
  under every difference map to lie outside `pointImage V.val.ι`.
  Reducedness plus this exact closed support determines the reduced induced
  structure uniquely by `exists_unique_reduced_closed_subspace`; this does
  not replace E by an unspecified incidence map or a set with no structure.
- `locus F n eX eM E` is the existing point image of E's inclusion followed
  by eM, the tail projection, and eX inverse. This is exactly Z_n in |X|.
  `Topology.IsConstructible` is the requested constructibility assertion.
- Smoothness, separatedness and finite presentation of X -> S are the five
  conjuncts `MapIsLocally Smooth`, `MapIsSeparated`,
  `MapIsLocallyOfFinitePresentation`, and `MapIsQuasiCompact` of the structure
  map and its relative diagonal. They are the original predicates.
- For every geometric s, the inverse image of Z is taken along
  `mapPoint (fibreProjection X s)`. The displayed equality identifies it with
  the inverse image of `geometricBadPoints` under the canonical fibre-to-tuple
  map. `geometricBadPoints` uses a field-valued representative and an actual
  extension `Over.mk s' ⟶ Over.mk a.base` to an algebraically closed field L,
  and asks for an x with every `g_j⁻¹x` outside V(L). Thus the finite union
  of the left translates fails to cover. This tests geometric tuples after
  extending their residue fields; it does not test only k-rational tuples
  or replace extension by an arbitrary map. Failure of coverage of a finite
  union of opens over an algebraically closed field is equivalent to the
  existence of such an L-point, since its nonempty complement is finite type.
  The condition is invariant under further field extension. Its use on total
  tuple point classes therefore also describes the inverse image over every
  fixed geometric base point, including tuples with nontrivial residue fields.
- The dimension clause is
  `topologicalKrullDim (closure (fibreProjection ⁻¹' locus)) + n ≤ n*d+d`
  in `WithBot ℕ∞`. For finite nonnegative dimensions this is exactly
  `dim <= nd-n+d`. Bottom plus n is bottom, so it also expresses the negative
  bound when d=0 correctly; it does not use truncated natural subtraction.
- `Nonempty (Point (fibre X s))` and the assertion that every member C of
  `irreducibleComponents (Point (fibre X s))` has
  `topologicalKrullDim C = n*d` are exactly nonempty pure nd-dimensional
  geometric fibres. These are algebraic-space point spaces with the atlas
  topology, not products of the topological point spaces.
- Finally `d=0` implies `IsEmpty (Point E)` and `locus = ∅`. Absence of
  field-valued point classes is emptiness of the algebraic space: any point
  on a nonempty atlas gives a residue-field representative.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, the sheaf-valued
  full subcategory, representable etale maps and scheme-test definitions.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`; the existing
  chart test uses this precise scheme predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`, used by the recorded morphism properties.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`,
  an actual subfunctor with representable open-immersion inclusion.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, and its
  quasi-compact strengthening `IsNoetherian` for the node's Noetherian base.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage` and
  `pointTopologicalSpace`, using `Point` and `PointRepresentative` from
  `AlgebraicSpacePointClasses`. `mapPoint` is the existing map from
  `ProperCurveModuli`, exposed through `AlgebraicSpaceMorphismProperties`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible` (the recorded
  Mathlib match of def-weil-constructible-subset, which needs no lean repair).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, the closure/universal-property input;
  imported transitively through the public dependency modules.
- Added the already-landed statement dependencies
  `def-sfb-smooth-integral-group-space` (`RegularGroupSpace`:
  `groupSpaceProjection`, `GroupSpaceIntegralFibres`, `IsSmoothIntegralGroupSpace`),
  `def-sfb-space-morphism-properties` (`AlgebraicSpaceMorphismProperties`:
  `MapIsLocally`, `MapIsSeparated`, `MapIsLocallyOfFinitePresentation`),
  `def-sfb-space-closed-subspace` (`AlgebraicSpaceClosedSubspace`:
  `ClosedSubspace`), and `def-sfb-reduced-algebraic-space`
  (`ReducedAlgebraicSpace`: `IsReduced`). These reuse the live definitions;
  their nodes themselves are not modified.

All recorded proof-dependency modules that have declarations are imported privately
(or are already in public dependency imports). These include the reduced closed
support, point-open calculus, group-space representation, binary product dimension,
scheme/topological dimension comparison, image-closure dimension, constant local
dimension and smooth relative-dimension permanence modules. The four proof nodes
without a recorded declaration need no new notion to state this theorem; their
proof plan is retained in the theorem docstring.

Edge cases checked before writing: empty S (geometric hypotheses are vacuous and
products/incidence are empty); d=0 (n>=1 forces empty incidence and bottom dimension);
V=H (empty support, empty Z); n=1 (the bound is 2d-1, with bottom at d=0);
noncommutative groups (the order of inverse/multiplication and automorphism inverse
are retained); arbitrary characteristic; tuples over transcendental residue fields
(the explicit algebraically closed extension remains); and topological dimension
of the empty closure (bottom, not zero). For n>d the dimension estimate becomes
strictly less than nd, as needed by the finite-translate argument. No disputed
statement or source-based correction was needed.

Searches (2026-10-24):

- `msearch.py` LeanFinder: "bad tuples of translates of an open subset in a
  smooth group algebraic space constructible dimension bound": 8 hits, on
  constructible polynomial data and Haar-measure covering/index bounds; no match.
- `msearch.py` Loogle: `AlgebraicGeometry.Smooth, topologicalKrullDim`: 0 hits.
- `msearch.py` Mathlib grep: `badTuple|bad_tuple|translate.*dimension`: 0 hits.
- `msearch.py` LeanSearch: "constructible locus of tuples of translates of an
  open subscheme covering a group scheme": 8 hits on constructibility local
  criteria and scheme covers/zero loci, no bad-tuple theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for group-space, translate,
  tuple and bad-tuple names found the recorded group functor/commutative group
  interfaces, morphism properties and reduced closed support, but no theorem
  with this conclusion. Searching the exact node id upstream found no declaration.
- `rg` for all new full/short declaration names in both roots and
  `dag/lean_names_upstream.json` found no full-name collision; unrelated `tail`,
  `difference` and `tuples` declarations live in other namespaces.
- DAG search and `tools/blueprint_refs.py search 'bad tuple'` found no second
  blueprint statement to reuse. The current latest direct-images blueprint proof
  was read; the bad-tuple result is its inherited auxiliary input. The source
  records the Deligne PDF as WANTED, so the existing agent-written proof route
  and Stacks support citations are retained rather than claiming to have read it.

Validation: every compile uses the prescribed `scompile.py`; a clean compile took
3.5 s on the server fallback. The first local attempt encountered a temporary
no-space error, and the wrapper itself confirmed on the server; no tool or library
was changed. The prescribed deliver2.py --no-push completed with OK: commit 18805d6138a
passed server preflight and per-file compilation. The final delivery repeats these checks.

## Second reading by NU

No second worker was launched: the dispatcher explicitly prohibits other agents,
and the maintainer supplies the independent review. A separate self-review pass
compared the complete node and module. It corrected two implementation details:
Type-valued maps use Mathlib's bundled function morphisms, and the naturality proof
of the difference map needs the reverse orientation of the group-homomorphism law.
It also replaced relative quasi-compactness of V's inclusion by `IsCompact` of its
point image to express the absolute condition directly. The statement-by-statement
mapping above is the resulting reading. In particular, no commutative law, bound
n>d, rational-tuple restriction, or unstructured replacement for E is assumed.
