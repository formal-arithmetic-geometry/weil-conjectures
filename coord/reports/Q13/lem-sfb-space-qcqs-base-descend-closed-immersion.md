## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceQcqsBaseDescendClosedImmersion` states
`AlgebraicGeometry.AlgebraicSpace.eventually_closedImmersion_of_qcqs_scheme_limit`.
Its sole theorem has proof `sorry`; it introduces no definitions or auxiliary theorems.
The natural-language statement and proof are unchanged. Two landed owning nodes were
added to `stmt_deps` for the predicates actually used, as permitted by brief §5.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- Working over Spec Z: the base of `Over` and `AlgebraicSpace` is explicitly
  `Spec (.of (ULift.{u} ℤ))`. The lift puts the integer ring in the schemes' universe;
  it does not change the base scheme. Mathlib `specULiftZIsTerminal` confirms terminality.
- Size convention: `universe u`, `J : Type u`, and the corresponding `Scheme.{u}` and
  algebraic spaces follow the project's index-universe convention. Every variable is
  explicit, and `autoImplicit` is false.
- Small, nonempty directed index set: `[Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]`.
  A preorder is the usual thin-category encoding of a directed set; allowing equivalent
  indices has no mathematical effect.
- Inverse system of schemes: `D : Jᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ)))`. Because the base
  is terminal, specifying these structure maps adds no restriction on the schemes or
  their morphisms. All scheme inverse systems have these unique structure maps.
- Each base is quasi-compact and quasi-separated: `hqc` gives `CompactSpace (D.obj j).left`;
  `hqs` gives `QuasiSeparatedSpace (D.obj j).left`. Neither asserts that the base is affine,
  separated, or Noetherian.
- Affine transitions: `haff` requires `IsAffineHom (D.map a).left` for every transition.
- Limit: `c : Cone D`, `hc : IsLimit c`, with limit base `c.pt`. A limit in the category
  of schemes over a terminal scheme is precisely a limit of the underlying schemes,
  since cones and their factorizations have unique compatible structure maps.
- Chosen initial index: `j₀ : J`.
- Initial algebraic spaces: `Y₀ Z₀ : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`.
  The natural transformations `pY`, `pZ` to `yoneda.obj (D.obj (op j₀))` are their structure
  maps to the initial base. The full subcategory encoding retains arbitrary algebraic
  spaces, rather than assuming that either source is a scheme.
- Finite presentation of each structure map: `hYqc`, `hZqc` use the existing
  `MapIsQuasiCompact pY` and `MapIsQuasiCompact pZ`; `hYqs`, `hZqs` use
  `MapIsQuasiSeparated pY` and `MapIsQuasiSeparated pZ`; `hYlfp`, `hZlfp` use
  `MapToSchemeIsLocally (@LocallyOfFinitePresentation)` for all representable etale charts.
  Thus each structure map is quasi-compact, quasi-separated and locally finitely presented.
  The quasi-compact predicate tests compactness of the point spaces of pullbacks along
  affine schemes. For algebraic spaces this is equivalent to admitting a surjective
  etale quasi-compact scheme atlas, as required by the node. `MapIsQuasiSeparated` is
  defined as `MapIsQuasiCompact` of the canonical relative diagonal.
- Initial morphism over the initial base: `h₀ : Over.mk pY ⟶ Over.mk pZ`. Its `.left` is
  the underlying natural transformation and its slice-morphism condition is the required
  equality of the composites to the base. Morphisms of the full algebraic-space
  subcategory are exactly these natural transformations, so no additional maps are allowed.
- Limit base change: `((Over.pullback (yoneda.map (c.π.app (op j₀)))).map h₀).left` is the
  canonical induced map between the presheaf fibre products. These are also the underlying
  sheaf fibre products; limits of sheaves are computed on their presheaves. Algebraicity
  is supplied by the recorded fibre-product dependency.
- Closed immersion of that limit base change: `hclosed` uses
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)`, which supplies an actual
  representing scheme and closed-immersion projection for every scheme test. It includes
  representability and adds no separate stage representability assumption.
- Descent conclusion: `∃ (j : J) (hj : j₀ ≤ j)` followed by the same scheme-test closed
  immersion predicate for the canonical pullback along `D.map (homOfLE hj).op`.
- Persistence: the second conjunct quantifies `∀ (k : J) (hk : j ≤ k)` and tests the
  canonical pullback along `D.map (homOfLE (le_trans hj hk)).op`. This is exactly the
  original morphism base changed to every later stage, including `k = j`.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, and the actual fppf-sheaf full subcategory.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` and the underlying sheaf fibre products.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.MapIsQuasiCompact` and
  `AlgebraicSpace.MapToSchemeIsLocally`,
  owned by the added landed `def-sfb-proper-curve-moduli`. No curve-family hypotheses
  or dimension conditions from that module are used.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: `AlgebraicSpace.MapIsQuasiSeparated`,
  owned by the added landed `def-sfb-stack-qcqs-morphism`. Only this algebraic-space
  predicate is used; no stack-specific assumptions occur.
- Mathlib's `Over.pullback`, `yoneda.map`, `Cone`, `IsLimit`,
  `CompactSpace`, `QuasiSeparatedSpace`, `IsAffineHom`, and thin-category `homOfLE`.
- The size-convention dependency has no declaration: explicit universe binders render it.

Proof imports retain the recorded, stated dependencies: `ChartwiseEtalePermanence`,
`WeilConjectures.AlgebraicGeometry.LimitAffineTransition`, and the Mathlib modules for
scheme affine-qcqs, open-immersion-etale and proper/fp permanence. The five proof-only
nodes `lem-sfb-space-closed-immersion-atlas-locality`, `lem-sfb-space-descend-closed-immersion`,
`lem-sfb-space-fp-qcqs-source`, `lem-sfb-space-qcqs-source-products`, and
`lem-sfb-space-relative-lfp-permanence` have no recorded Lean module in the read snapshot;
there is consequently no module of theirs to import. All six natural-language proof
steps, including their node references, are in the theorem docstring.

Edge cases checked before writing: empty initial/limit bases and empty source or target
spaces are allowed; neither atlases nor finite affine covers are required nonempty.
The directed set is nonempty as specified; singleton and constant systems are included.
A limit can be empty despite nonempty stages: finite-presentation/compactness gives
an eventual empty stage, so this causes no counterexample. Identity morphisms, nilpotent
closed immersions, and zero rings are included. No transition is required surjective.
Nonaffine qcqs bases are allowed, including ones whose affine-open intersections are
not affine. No extra characteristic, reducedness, or representability restriction occurs.

Sources checked: the full local Stacks `spaces-limits.tex` Situation
`situation-descent-property` (084W) and `lemma-descend-closed-immersion` (0850).
The source assumes qcqs initial spaces and local finite type of the stage map; the
node supplies these through finite presentation over the qcqs initial base, exactly
as its first proof step explains. This is not an extra assumption in the Lean.
No statement fault or dispute found. No statement correction, new nodes, or dependency
repairs were necessary.

Searches for an existing assertion and definitions:

- `msearch.py`, leanfinder: "Closed immersions of finitely presented algebraic spaces
  descend over qcqs scheme inverse limits with affine transitions" returned eight
  scheme-level results, including `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`,
  `exists_mem_of_isClosed_of_nonempty`, and fpqc descent declarations. None states
  this algebraic-space inverse-limit assertion.
- `msearch.py`, loogle: "AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.AlgebraicSpace"
  returned zero hits (Mathlib does not know the project's AlgebraicSpace identifier).
- `msearch.py`, grep: "descend.*closed|closed.*descend" in `AlgebraicGeometry` returned
  three flat-descent/universally-closed references, not this assertion.
- `rg` of `lean/WeilConjectures` for the item id returned no match. Broader searches
  for closed-immersion descent found `DescendClosedImmersion.lean` and scheme closed
  subscheme approximation, neither an algebraic-space assertion.
- `rg` of `lean/Sheaf`, including algebraic-space modules, found no matching assertion.
  Searches for quasi-compactness and local finite-presentation predicates found the two
  existing modules cited above; both definitions and their full docstrings were read.
- `rg` of `dag/lean_names_upstream.json` and source names found no collision for
  `eventually_closedImmersion_of_qcqs_scheme_limit`.

Validation: prescribed `scompile.py` compiled the repaired sandbox and library views
without errors or warnings (7.5 seconds and 5.1 seconds respectively). The repaired
delivery is then checked with `deliver2.py --no-push` before submission.

## Repair of return ad22b2296c42

H2/H4 repaired exactly as requested. The four finite-presentation hypotheses now use
`MapIsQuasiCompact pY`, `MapIsQuasiCompact pZ`, `MapIsQuasiSeparated pY`, and
`MapIsQuasiSeparated pZ`. I read the full signatures and source docstrings of
`MapIsQuasiCompact` in `ProperCurveModuli.lean` and `MapIsQuasiSeparated` in
`StackQcqsMorphism.lean`, together with the latter owning node's statement and Lean record.
The direct import of `SpaceQCSeparatedEtaleLocal` and its theorem-node statement
dependency `lem-trf-space-qc-separated-etale-local` are removed. The direct import of
`StackQcqsMorphism` and definition-node statement dependency
`def-sfb-stack-qcqs-morphism` replace them. `def-sfb-proper-curve-moduli` remains cited.
The node's `lean.statement` is extracted verbatim from the repaired theorem signature.

Compared the retained sandbox with returned head ad22b2296c42 using the return's
four old hypotheses and import/dependency details, and with the current shared main
node: main has no Lean record and has the original six statement dependencies; all
other node fields agree with the retained delivery. The repaired node was reconstructed
from current main, adding only the two owning definition dependencies and the repaired
Lean record. The prescribed delivery wrapper rebases the packet on current server main.
All remaining binders, the descent and persistence conclusions, the proof plan and
`by sorry` proof are unchanged. No natural-language statement correction is needed.
The prior review accepted those clauses and edge cases; the changed predicates retain
the same mathematical meanings and include the empty cases. No new nodes or dependency
modules are introduced.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
