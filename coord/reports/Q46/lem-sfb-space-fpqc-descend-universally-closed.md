## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceUniversallyClosedFpqcDescent`
states `AlgebraicGeometry.AlgebraicSpace.universallyClosed_of_fpqc_cover`.
Its only theorem has proof `sorry`. No definition is introduced, no dependency
interface is replaced, and the natural-language statement is unchanged.

Source read: `literature/stacks-project/spaces-descent.tex`, lines 1245–1283,
lemma-descending-property-universally-closed, Stacks Tag 041O (confirmed in the
local tags table). This is its descent implication with a scheme target and a
covering by schemes. The theorem docstring gives all five steps of the accepted
node proof, including the scheme-source-only use of the point lifting lemma and
the non-Hausdorff two-point continuous-function gluing argument.

Clause-by-clause rendering:

- A scheme target is `(T : Over S)` with explicit `{S : Scheme.{u}}`. Its
  underlying scheme is `T.left`; `schemeSpace T` is its actual representable
  fppf sheaf. `Over S` supplies the ambient base required by the existing
  algebraic-space category, as in the source's first line “Let S be a scheme”.
  This does not impose a geometric condition on T: one can take the ambient
  base to be the target itself and T to be its identity map. General schemes
  over a common base are retained as well.
- The source is `(X : AlgebraicSpace S)`, with no scheme-representability
  restriction, and the morphism is `(f : X ⟶ schemeSpace T)`.
- The arbitrary index type is `{I : Type w}`; there is no Nonempty or finiteness
  assumption. `(Tᵢ : I → Over S)` and `(g : ∀ i : I, Tᵢ i ⟶ T)` are the
  covering schemes and their morphisms. Taking underlying schemes in `hcover`
  gives exactly the family of scheme maps in the node.
- `hcover : Presieve.ofArrows (fun i ↦ (Tᵢ i).left)
  (fun i ↦ (g i).left) ∈ Scheme.fpqcPrecoverage T.left` is precisely the
  recorded fpqc-covering definition. It includes flatness and the finite
  quasi-compact-open refinement condition on every affine open, not
  quasi-compactness of each g_i. Mathlib's
  `QuasiCompactCover.exists_isAffineOpen_of_isCompact` recovers the equivalent
  finite affine-open formulation of the dependency node.
- The morphism
  `(ObjectProperty.homMk ⟨yoneda.map (g i)⟩ :
    schemeSpace (Tᵢ i) ⟶ schemeSpace T)` is the canonical representable
  morphism of algebraic spaces. `enlargedFibreProductFst` of this map and f
  is the projection `T_i ×_T X → T_i`. This is the stated
  `X ×_T T_i → T_i` via the canonical interchange of factors; neither the
  source nor its arrow is arbitrary. The actual underlying sheaf pullback
  and its first projection are the recorded definitions.
- `hclosed : ∀ i : I, MapIsUniversallyClosed (...)` expresses every local
  universal-closedness hypothesis, using the existing predicate verbatim.
- The conclusion `MapIsUniversallyClosed f` uses the very same predicate.
  Its full definition quantifies over every `(Y' : AlgebraicSpace S)` and
  `(g : Y' ⟶ schemeSpace T)` and asks that the induced second projection
  on `Point` be an `IsClosedMap` for `pointTopologicalSpace`. These are
  field-valued point classes with the final atlas topology. A space mapping
  to T already has the required S-structure, so this quantifies over all
  algebraic-space base changes, not just scheme tests.
- There are no hypotheses on f of quasi-compactness, separatedness, finite
  type, finite presentation, flatness or Noetherianity.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace` and the scheme-test representability/etaleness definitions.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage`. Its definition
  is `propQCPrecoverage @Flat`; its three derived precoverage instances supply
  the isomorphism, composition and base-change axioms in the proof plan.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`; full signatures and docstrings read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsUniversallyClosed`, whose definition uses all algebraic-space base changes.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedFibreProduct`, `enlargedFibreProductFst`. The existing definition
  owners `def-trf-scheme-algebraic-space` and `def-sfb-space-sheaf-fibre-product`
  are added to stmt_deps under the permission to cite landed definition nodes.
  Both node records and the actual definitions were read. No new nodes or
  dependency modules are needed.

The following proof-only modules are imported with plain `import`:
`AlgebraicSpacePointTopology`, `AlgebraicSpaceAffineEtaleCover`,
`AlgebraicSpaceFibreProductPoint` under `Sheaf.AlgebraicGeometry`, and
`Mathlib.AlgebraicGeometry.Sites.ConstantSheaf`. Their recorded declarations
`pointTopologicalSpace`, `exists_affine_etale_cover_and_point_topology`,
`exists_scheme_fibreProduct_point`, and
`AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf` were read,
including their docstrings and full signatures. The last theorem allows any
TopologicalSpace with no separation assumption. All recorded statement and
proof dependency modules are imported; none is omitted for a cycle.

Edge cases checked before writing and rechecked against the signature:

- Empty index: allowed by `I : Type w`. Fpqc joint surjectivity forces T empty;
  any space mapping to its representable sheaf is empty, so all tested point
  images are closed. No Nonempty binder excludes this case.
- Empty source, empty ambient base and empty closed subset: all point images
  are empty and therefore closed, with no additional hypothesis.
- Identity cover: the identity pullback identifies the local hypothesis with
  the conclusion. Repetition of indices and an arbitrary size of cover are
  permitted; the index universe w is independent of the scheme universe u.
- Covering maps need not be individually quasi-compact. Only family membership
  appears in the signature. The proof's two-point target has no T2 assumption.
- Universal closedness remains quantified over spaces in universe u, in the
  established common size convention of the dependency definitions; no
  smaller independent universe is used for the base-change test objects.
- Nonseparated, non-Noetherian and non-finite-type source/target cases are
  retained; no auxiliary structure narrows them.

Searches made (all on 2026-10-24):

1. `msearch.py ... leanfinder "Universal closedness of a morphism from an
   algebraic space to a scheme descends under an fpqc covering family of
   schemes"`: 8 hits, including
   `AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`
   and scheme-only universal-closedness definitions and permanence lemmas.
2. `msearch.py ... loogle "AlgebraicGeometry.UniversallyClosed, AlgebraicGeometry.Flat"`:
   one hit, the same scheme descent instance. Read FlatDescent.lean:48–62 and
   UniversallyClosed.lean:35–41: they require scheme sources, unlike this item.
3. `msearch.py ... grep
   "AlgebraicSpace|[Uu]niversally[Cc]losed.*[Dd]escend|[Dd]escend.*[Uu]niversally[Cc]losed"
   AlgebraicGeometry`: 3 lines in Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean;
   no algebraic-space descent declaration.
4. `msearch.py ... leansearch "Universal closedness descends under fpqc scheme
   covering families for a morphism from an algebraic space to a scheme"`:
   8 hits, all on scheme morphisms; the same descent instance is the first hit.
5. `rg -n` for `MapIsUniversallyClosed`, the two orders of fpqc/universallyClosed,
   and the item id in `lean/WeilConjectures` and `lean/Sheaf`: no upstream match;
   the side library has the existing predicate, other results using it, and
   `AlgebraicGeometry.universallyClosed_of_fpqc_cover` in
   `Sheaf.AlgebraicGeometry.UniversallyClosedOfFpqcCover`. The latter's full
   declaration was read and is scheme-only. Its namespace is different from
   the new `AlgebraicGeometry.AlgebraicSpace.universallyClosed_of_fpqc_cover`.
6. `rg -n 'universallyClosed_of_fpqc_cover' dag/lean_names_upstream.json
   lean/WeilConjectures lean/Sheaf`: only that scheme theorem was found.
   Searching the upstream tree for the item id and Tag 041O found no declaration.
7. Declaration/ownership searches for `schemeSpace` and `enlargedFibreProduct`
   found the existing definitions in EnlargedEtaleRingedSite and their two
   landed definition-node owners. Those constructions are reused directly.

No STATEMENT-DISPUTED issue or node fault was found. The unchanged statement
is a specialization of Stacks 041O; the only node changes are lean and the
addition of the two existing definition dependencies. No external repository
files were edited directly.

Validation: the delivered module compiled through the prescribed scompile.py
on the live server, in required module mode (5.9 s), with no errors or warnings.
All variables and both universes are explicitly bound, with autoImplicit false.
The sole theorem proof is sorry. The independent reading is left to the
maintainer as required by the direct-delivery brief.

## Second reading by Q46

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
