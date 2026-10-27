## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceEventuallyProper` states
`AlgebraicGeometry.AlgebraicSpace.eventually_proper_of_isLimit`, with proof `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The natural-language proof in the declaration docstring follows all seven DAG steps.
The source was read locally: `literature/stacks-project/spaces-limits.tex`, Situation
084W and Tag 08K1 (lemma-eventually-proper). The source allows locally finite type
qcqs spaces; the node intentionally specializes to a finitely presented space over an
affine base. The statement preserves that specialization.

Clause-by-clause correspondence:

- Work over Spec Z: the common base is `Spec (.of (ULift.{u} ℤ))`. `ULift` places the
  integer ring in the schemes' universe without changing it mathematically. Scheme
  objects, algebraic spaces, and the small index set all use the explicit universe `u`.
- Small nonempty directed set: `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. This uses the current directed-set convention;
  neither antisymmetry nor a least element is assumed.
- Inverse system of affine schemes: `D : Iᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ))))`
  with `[∀ i : I, IsAffine (D.obj (op i)).left]`. The transition-map hypothesis is
  `[∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a).left]`. Affineness of transitions
  is already implied by affine source and target, but is explicitly present in the node.
- The inverse limit T and its projections: `(c : Cone D) (hc : IsLimit c)`. Limits in
  the slice over Spec Z have the usual underlying scheme limit; the slice does not
  restrict the system. No extra affineness, nonemptiness or surjectivity of T is required.
- Initial stage: `(i₀ : I)` with no minimality assumption.
- Initial algebraic space and morphism: `X₀ : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`
  and `f₀ : X₀ ⟶ schemeSpace (D.obj (op i₀))`. `schemeSpace` is the existing represented
  fppf sheaf of the scheme; X₀ need not be a scheme or initially separated.
- Finite presentation: `hfp` is the conjunction of
  `MapIsLocallyOfFinitePresentation f₀`, `MapIsQuasiCompact f₀.hom.hom`, and
  `MapIsQuasiCompact (pullback.diagonal f₀.hom.hom)`. The first predicate tests the
  recorded scheme locally finite presentation property on all compatible etale charts;
  the last is quasi-separatedness, not separatedness.
- The limiting base change is proper: `hf` asserts `MapIsProper` for
  `enlargedFibreProductFst` with first input the represented cone map and second input
  `f₀`. This constructs T ×_{T₀} X₀ with its projection to T, canonically the displayed
  X₀ ×_{T₀} T of the node. The product ordering changes no object or property.
- Properness has exactly the three required constituents: `MapIsProper` unfolds to
  `MapIsSeparated ∧ MapIsFiniteType ∧ MapIsUniversallyClosed`. These use a diagonal
  represented by closed immersions, quasi-compactness and the locally finite type
  scheme chart test, and closedness on point spaces after every algebraic-space base
  change. No scheme-only restriction of universal closedness is substituted.
- Eventual conclusion: `∃ (i : I) (hi : i₀ ≤ i), ∀ (j : I) (hj : i ≤ j), ...`.
  The base map is precisely `D.map (homOfLE (le_trans hi hj)).op`, represented by
  `yoneda.map` and `ObjectProperty.homMk`; the projection is the same canonical
  fibre-product construction used for `hf`. It is asserted proper for all such j.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, representability,
  representable etale maps, fppf sheaf and atlas condition.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and the relative `pullback.diagonal` construction.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation` (via the existing chartwise predicate).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`,
  `UniversallyClosed` (scheme conventions underlying the existing space predicates).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `def-weil-size-convention` has a convention record: rendered by explicit universes.
- Added already-landed dependency `def-sfb-space-morphism-properties`, whose recorded
  module is `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`,
  `MapIsSeparated`, `MapIsFiniteType`, `MapIsUniversallyClosed`, and
  `MapIsLocallyOfFinitePresentation`. Quasi-compactness is the existing
  `MapIsQuasiCompact` in `Sheaf.AlgebraicGeometry.ProperCurveModuli`, publicly imported
  by this module.
- Added already-landed dependency `def-sfb-space-sheaf-fibre-product`, whose recorded
  module is `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `enlargedFibreProduct`, `enlargedFibreProductFst`. Its `schemeSpace` uses the existing
  representable sheaf, and `schemeSheaf_isAlgebraicSpace` supplies its space property.
  All these declarations' full source signatures and docstrings were read.

The stated proof dependencies are imported: point topology, finite-presentation/properness
locality, algebraic-space fibre products, projective space, and descent of closed
immersions, together with the Mathlib permanence modules. The proof-dependency nodes
`lem-sfb-space-descend-separated`, `lem-sfb-space-proper-base-change`,
`lem-sfb-space-proper-composition`, and `lem-sfb-space-weak-chow` have no recorded
Lean declarations yet and therefore have no module to import. They are not statement
prerequisites, and their natural-language uses remain in the proof docstring.

Edge cases checked before writing: the empty source and empty affine bases are allowed;
nonempty I is explicit, and i₀ is arbitrary. Constant and singleton systems recover
properness under identity base change. The conclusion includes j = i. No transition
surjectivity or flatness is assumed, and the limit may be empty even if stages are
nonempty. Nonseparated initial models are allowed: hfp requires a quasi-compact diagonal,
not a closed diagonal. The preorder encoding allows equivalent indices and has the
same inverse-system meaning. Finite presentation excludes none of the node's cases.
Universes do not independently shrink the index set relative to its scheme diagram.

Searches made (2026-10-24):

- `msearch.py ... leanfinder "A finitely presented morphism of algebraic spaces proper
  after base change to an inverse limit of affine schemes is eventually proper"`:
  eight hits, all scheme properness or scheme finite presentation; no match.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper, CategoryTheory.Limits.IsLimit"`:
  zero hits.
- `msearch.py ... grep "eventually.*[Pp]roper|[Pp]roper.*[Ll]imit" AlgebraicGeometry`:
  sixteen Mathlib hits, only imports/ordinary scheme permanence, no match.
- `rg` of those concepts and of `lem-sfb-space-eventually-proper` in
  `lean/WeilConjectures` and `lean/Sheaf`: the existing scheme theorem is
  `AlgebraicGeometry.exists_isProper_baseChange_of_isLimit` in
  `WeilConjectures.AlgebraicGeometry.EventuallyProper`; its full signature requires
  scheme sources and cannot state this node. Other hits were consumer proof docstrings.
- `rg` of `MapIsProper`, `MapIsLocallyOfFinitePresentation`, fibre-product and scheme
  embedding declarations located the existing space notions above. DAG searches found
  their existing owning nodes, which are reused; no private definitions were written.
- `rg` of the proposed theorem name and `MapIsProper` in `dag/lean_names_upstream.json`
  found no conflicting theorem. The module compiles without duplicate declarations.

No STATEMENT-DISPUTED flag or node fault was found. The only first-compile diagnostic
was an extra whitespace warning, which was repaired. All compiling uses `scompile.py`.

## Second reading by Q12

Independent reading by the maintainer's stage-2 reviewer. The delivered Lean is unchanged;
this section replaces the worker's self-audit (H11). I read the node, Stacks 08K1 in
Situation 084W and 04WP, the module, and the signatures of every declaration it uses
(side-live `AlgebraicSpaceMorphismProperties`, `ProperCurveModuli.MapIsQuasiCompact`,
`EnlargedEtaleRingedSite.schemeSpace/enlargedFibreProduct/enlargedFibreProductFst`).

Node clauses and their Lean:

- Base Spec Z, universes of def-weil-size-convention: `Spec (.of (ULift.{u} ℤ))`,
  `Scheme.{u}`, `I : Type u`. Every scheme is uniquely over Spec Z, so `Over (Spec ℤ)`
  is the category of schemes. Correct.
- Small nonempty directed set: `[Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`.
  Antisymmetry is not needed. Correct.
- Inverse system of affine schemes with affine transitions:
  `D : Iᵒᵖ ⥤ Over _`, `IsAffine (D.obj (op i)).left`, `IsAffineHom (D.map a).left`. Correct.
- T = lim T_i: `(c : Cone D) (hc : IsLimit c)` in `Over (Spec ℤ)`. Iᵒᵖ is cofiltered and
  hence connected, so the forgetful functor creates this limit and `c.pt.left` is the scheme
  limit. Correct.
- i₀ arbitrary: `(i₀ : I)`, with no minimality assumed. Correct.
- f_{i₀}: X_{i₀} → T_{i₀} from an algebraic space:
  `X₀ : AlgebraicSpace (Spec ℤ)` and `f₀ : X₀ ⟶ schemeSpace (D.obj (op i₀))`.
  Here `schemeSpace` is the representable fppf sheaf (owner def-trf-scheme-algebraic-space).
  Correct.
- f_{i₀} finitely presented, i.e. lfp on étale charts, quasi-compact and quasi-separated:
  `MapIsLocallyOfFinitePresentation f₀` is the all-compatible-chart test (Tag 0410(7)).
  `MapIsQuasiCompact f₀.hom.hom` uses affine tests with compact point space of the pullback.
  `MapIsQuasiCompact (pullback.diagonal f₀.hom.hom)` makes the diagonal quasi-compact.
  These are exactly the node's three clauses. Separatedness is not assumed. Correct.
- X = X₀ ×_{T₀} T and f proper: `hf : MapIsProper (enlargedFibreProductFst g f₀)`, where
  g is the representable map of `c.π.app (op i₀)`. `enlargedFibreProduct g f₀` is
  `Limits.pullback g.hom f₀.hom`, and its fst is the projection to `schemeSpace c.pt`.
  This is f, with the product factors in the other order. Correct.
- Properness: `MapIsProper` is `MapIsSeparated ∧ MapIsFiniteType ∧ MapIsUniversallyClosed`.
  Separated means the diagonal is representable by closed immersions.
  Finite type means quasi-compact plus chartwise `LocallyOfFiniteType`.
  Universally closed means `IsClosedMap mapPoint` after every algebraic-space base change.
  This matches the node's definition. Correct.
- Conclusion: `∃ i, ∃ hi : i₀ ≤ i, ∀ j, ∀ hj : i ≤ j, MapIsProper (fst (T_j → T₀) f₀)`.
  The transition is `D.map (homOfLE (i₀ ≤ j)).op`, and X_j = X₀ ×_{T₀} T_j as in the node.
  The quantifier order is the same and the case j = i is included. Correct.

Edge cases: I may not be empty, since the node requires nonempty I. The empty limit, empty
stages and an empty X₀ are allowed. A constant system gives identity base change. No
surjectivity, flatness, separatedness of X₀ or least index is assumed. Universes are all u,
which is the node's convention, and there is no extra restriction.

One definition per notion: the scheme theorem `exists_isProper_baseChange_of_isLimit`
(WeilConjectures.AlgebraicGeometry.EventuallyProper) applies only to scheme sources, so it is
not a duplicate. All space notions are the recorded owners. No local definition is added.

Records: the item node differs from the base only by `lean` and by two added landed
definition nodes in `stmt_deps` (def-sfb-space-morphism-properties and
def-sfb-space-sheaf-fibre-product). `lean.statement` is verbatim the signature in the file.
The proof is `sorry`. Docstrings carry the source place, the blueprint id and all seven
steps.

Advisory: the owners of `schemeSpace` (def-trf-scheme-algebraic-space) and
`MapIsQuasiCompact` (def-sfb-proper-curve-moduli) are not in `stmt_deps`; both are landed
definition nodes. The module docstring calls the chapter "Spaces and Morphisms of Spaces";
Tags 084W/08K1 are in "Limits of Spaces". The tags themselves are correct.
