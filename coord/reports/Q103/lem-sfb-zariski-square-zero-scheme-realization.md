## Worker report

This stage-2 packet states `AlgebraicGeometry.zariski_square_zero_scheme_realization`
in `Sheaf.AlgebraicGeometry.ZariskiSquareZeroSchemeRealization`. Its only theorem
has proof `sorry`. The auxiliary module contains real extension data and real
ringed-space constructions, with no choice from an existence theorem.

I read the full statement and nine proof steps of the item, every statement dependency
and its recorded module, the source Stacks `more-morphisms.tex`,
`lemma-first-order-thickening` (05YV), and the recorded proof dependency interfaces.
The accepted Q39 stage-1 split is unchanged. The old stage-1 live-wins failure does
not prevent this stage-2 statement, as the current brief explicitly explains.
No repair note for this item was present.

Clause-by-clause rendering:

- Schemes `X`, `B` and their specified morphism are `{X B : Scheme.{u}} (f : X ⟶ B)`.
  There is no finiteness, separatedness, affineness or characteristic assumption.
- The specified quasi-coherent module is `(G : X.Modules) [G.IsQuasicoherent]`.
  This uses Mathlib's module sheaves and quasi-coherence, imported by the recorded
  `Sheaf.AlgebraicGeometry.CoherentFiniteType` dependency module. Its stronger
  `IsQuasiCoherentFiniteType` predicate is deliberately not assumed: the node
  requires quasi-coherence alone, which that module publicly imports.
- `ZariskiSquareZeroExtension f G` records `algebra : TopCat.Sheaf CommRingCat X`,
  `quotient`, and the additive `inclusion` with naturality. `injective` and `kernel`
  express the first two exactness clauses sectionwise. `locally_surjective` says that
  every quotient section lifts near each point, exactly sheaf surjectivity; it does
  not require a lift on every open.
- `square_zero` states that any two kernel sections multiply to zero. `scalar`
  identifies their prescribed quotient-module action with multiplication by a lift.
  This also makes the included additive kernel an ideal. No O_X-algebra structure
  on the middle ring is assumed (the non-split Z/4 example must be allowed).
- `base` is the sheaf map O_B → f_*E. By inverse/direct image adjunction it is exactly
  the f⁻¹O_B-algebra structure. `base_quotient` states that the quotient respects it.
- `space` constructs precisely the ringed space `(carrier X, E)`, and `reduction`
  constructs its quotient arrow with identity point map. The first existential
  gives a scheme and an isomorphism to this very ringed space. `Realizes` demands
  `IsFirstOrderThickening j`, `j ≫ q = f`, and equality of the actual ringed quotient
  and base arrows under the marking. Thus the assertion concerns E itself, rather
  than a different structure sheaf with an unspecified comparison.
- For every affine open `U`, the second conjunct asserts
  `Function.Surjective (D.quotient.app (op U))`. Its kernel is already exactly
  `inclusion U (G(U))` by the data, with injectivity; this is the full section sequence.
  The affine target is explicitly `Spec (D.algebra.obj.obj (op U))`. The isomorphism
  `h` has its induced map on global sections normalized by `toSpecΓ` to the marking
  `e` and the canonical identification of restricted global sections with E(U).
  The Γ–Spec adjunction therefore makes it the canonical affine comparison, not
  an arbitrary abstract affine isomorphism.
- The converse quantifies over every first order thickening `j : X ⟶ Y` over B,
  with no fixed module G. It produces a quasi-coherent G and extension whose
  quotient arrow is exactly j under the marking. Injectivity plus the sectionwise
  `kernel` field identifies G with the actual sheaf kernel, not a larger ideal or
  an unrelated abstract coefficient module.
- `IsOpenExtensionMap` is the ringed-space form of a ring-extension map. Its point
  map is the identity; it commutes with the actual quotient arrow `reductionOpen`
  and the base arrow. The ring-sheaf component of a ringed morphism runs in the
  opposite direction, so this expresses the required contravariance.
  The last conjunct gives existence and uniqueness of the corresponding scheme
  arrow for every such ringed arrow, normalized by
  `schemeToRinged.map g ≫ d.hom = e.hom ≫ a`. Its second half gives the inverse
  operation on every scheme arrow. These two clauses give bijectivity, not merely
  a map between the sets. Composition is that of the already existing ringed-space
  category and thus composes structure-sheaf maps contravariantly.
- The construction and correspondence are stated on every open U, not only on X
  or an affine cover. `RealizesOpen` uses the literal restriction of the ringed space
  and its quotient. For V ≤ U the unique open arrow is normalized by its composite
  to the original ringed space, with both reduction and base triangles.
  The map correspondence on every open has equality with the marked ringed arrow,
  not an arbitrary bijection; restricting that equality gives the same component
  sheaf maps on V. Together with uniqueness of the restriction arrows this states
  that the correspondence commutes with open restriction. Identity, empty and
  nested restrictions are included; affine intersections are not assumed.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: publicly imports
  `Scheme.Modules` and `SheafOfModules.IsQuasicoherent` used here.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` transparently
  abbreviates the same Mathlib `SheafOfModules`; the scheme specialization is
  `X.Modules`. No duplicate module category is introduced.
- `WeilConjectures.AlgebraicGeometry.Thickening`: `IsFirstOrderThickening` means
  closed immersion with square-zero actual defining ideal.
- The new node below supplies `ZariskiSquareZeroExtension` and its markings.
  The proof imports the recorded stalkwise exactness, affine vanishing,
  module/abelian cohomology comparison, universal derived delta functor,
  affine germ-localization and closed-immersion annihilated-module modules.
  Mathlib proof imports supply the Γ–Spec adjunction, localized exactness,
  Spec stalks/function field, short five lemma and sheaf stalk criterion.
  No recorded proof import is omitted for a cycle.

Edge cases checked before and during writing: empty X and empty open U (the pointwise
local-lifting condition is correctly vacuous and empty-open sections have a unique
lift); G=0; arbitrary infinitely generated modules in a split extension A⊕M;
non-split Z/4 → F₂; characteristic two; arbitrary nonaffine X and nonaffine overlaps;
identity and repeated open restrictions. The hypotheses admit each. All schemes,
rings and modules use the same explicit ambient universe u, with no independently
smaller test universe or forbidden equality of site object and morphism universes.

Searches actually run through msearch.py (also saved in searches.jsonl):

- LeanFinder: “A square zero extension of a scheme structure sheaf by a quasi
  coherent module is a scheme with the same topological space”: eight results,
  including Scheme.Modules, IdealSheafData.glueDataObj and AffineSpace; none is this
  ring-sheaf extension or its realization theorem.
- Loogle: `AlgebraicGeometry.IsFirstOrderThickening, TopCat.Sheaf`: no results;
  the service reports the project identifier IsFirstOrderThickening as unknown.
- Mathlib grep: `square.zero|SquareZero` in AlgebraicGeometry: zero results.
- LeanSearch: “square zero extension of sheaves of rings on a topological space
  with prescribed module kernel”: eight ring-level results, principally TrivSqZeroExt;
  none is a sheaf extension with arbitrary, possibly non-split middle algebra.
- `rg` of the project's WeilConjectures and Sheaf sources for the item id,
  ZariskiSquareZero and square-zero extensions found the algebraic-space/étale
  family but no Zariski equivalent. The source files
  `SpaceSquareZeroExtensionData` and `SpaceSquareZeroRingedRealization` were opened:
  their sites are étale sites, not the Zariski open category used here.
- DAG search for the concept found the same étale-chart family and this theorem;
  `tools/blueprint_refs.py search 'square-zero extension'` found zero blueprint nodes.
  `ancestor` reports the inherited null ancestor, which is retained without inventing one.
- A final grep of Mathlib, WeilConjectures, Sheaf and lean_names_upstream found none
  of the new declaration names.

Validation: both modules compile through scompile.py in dependency order with no
errors or warnings. Every variable and universe is explicit (`autoImplicit false`).
The sole postponed proof is the named main theorem, with the nine-step proof
in its docstring. No statement correction or disputed mathematical claim is needed.

## New nodes

`def-sfb-zariski-square-zero-extension` defines the missing Zariski extension datum,
its ringed space, reduction, base arrow, marked realization and extension maps in
`Sheaf.AlgebraicGeometry.ZariskiSquareZeroExtension`. This is not the existing
étale algebraic-space extension notion: it uses the original topological space
and its Zariski opens. All data are real structure fields or canonical constructors.
`reductionOpen` is whiskering of the specified quotient by the open inclusion,
not a new arbitrarily chosen arrow. The new node is cited by the item; the accepted
statement and proof are unchanged. Its searches reproduce the queries and actual
search log results above, and its blueprint lineage retains the item's null ancestor.

Preflight repair: the first dry run requested the required empty `import_flags`
field on the new definition node. I supplied it and separated grouped DAG
citations so each dependency is recognized individually. The ringed-space
definition node is also cited explicitly. No Lean signature changed in this repair.

## Second reading by Q103

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
