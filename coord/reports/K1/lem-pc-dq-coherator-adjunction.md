## Worker report

The module `Sheaf.AlgebraicGeometry.DQCoheratorAdjunction` states the coherator
adjunction and global-sections detection, with every proof `sorry`. No definition,
axiom, or alternative derived category is introduced. The node statement is unchanged.

Hypotheses and clauses:

- The scheme is `Y : Scheme.{u}`. Quasi-compactness is `[CompactSpace Y]`, and
  quasi-separatedness is `[QuasiSeparatedSpace Y]`. These hypotheses are present
  on every declaration.
- `D(O_Y)` is the dependency's `schemeDerivedCategory Y`, with exactly its shared
  `[HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]`
  localization binder; this is universe infrastructure, not a restriction on Y.
- `D_QCoh(O_Y)` is the dependency's `schemeDerivedQCohCategory Y`. Its inclusion is
  `(schemeDerivedQCohProperty Y).ι`, the canonical full-subcategory inclusion.
- Existence of a right adjoint is
  `∃ DQ_Y : schemeDerivedCategory Y ⥤ schemeDerivedQCohCategory Y,
  Nonempty (Adjunction (schemeDerivedQCohProperty Y).ι DQ_Y)`.
  An `Adjunction` contains `homEquiv M E` with source
  `((schemeDerivedQCohProperty Y).ι.obj M ⟶ E)` and target `(M ⟶ DQ_Y.obj E)`,
  and its naturality in both M and E. Thus the natural bijection clause is
  included in the adjunction data, not just a bare collection of bijections.
- Detection is `dqCoherator_detects_globalSections`: for *any* right adjoint with
  `adj : (schemeDerivedQCohProperty Y).ι ⊣ DQ_Y`, any K-injective complexes I,J,
  and a chain map f representing u, `IsIso (DQ_Y.map (DerivedCategory.Q.map f))`
  implies `QuasiIso` of termwise global sections of f.
  I and J are arbitrary unbounded integer cochain complexes, with their
  `[I.IsKInjective]` and `[J.IsKInjective]` computational representative conditions.
  This is the node's RΓ clause in its defining K-injective computation, not a
  restriction to bounded E,E': every derived object has a K-injective
  representative and every derived morphism between those representatives is
  represented by a chain map. These conditions specify how RΓ is computed;
  they do not assume that E or E' is itself quasi-coherent or an injective sheaf.
  The conclusion is genuinely `QuasiIso` of the global-sections complexes.
- `O_Y[-i]` is the degree-zero `DerivedCategory.singleFunctor` applied to
  `SheafOfModules.unit (moduleRings Y.toRingedSpace)`, then shifted by `-i`.
  `structureSheaf_shift_is_derivedQCoh` states `schemeDerivedQCohProperty Y` of
  this object for every `i : ℤ`.
- The explanatory equality `H^i(Y,E)=Hom(O_Y[-i],E)` is rendered by
  `globalSections_homology_equiv_structureSheaf_shift`: an additive equivalence
  between the degree-i homology of global sections of any K-injective I and
  the derived Hom group into `DerivedCategory.Q.obj I`. It does not replace
  global cohomology by a new definition or by degree-zero sheaf cohomology.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, `schemeDerivedQCohProperty`,
  `schemeDerivedQCohCategory`. Their signatures and full docstrings were read.
  Cohomology is Mathlib's derived-category homology of the shared O_Y-module carrier.
- `Sheaf.Topology.RingedSpaceModuleCohomology`:
  `AlgebraicGeometry.RingedSpace.globalSectionsFunctor` and its additive instance.
  This is the existing evaluation at `op ⊤` into `ModuleCat` over O_Y(Y).
  Its landed node `def-sc-ringed-space-module-cohomology` is added to stmt_deps
  under the rule allowing already-landed nodes; its module was not copied.
- Mathlib `ObjectProperty.ι`, `Adjunction`, `DerivedCategory.Q`,
  `DerivedCategory.singleFunctor`, `SheafOfModules.unit`, `CochainComplex.IsKInjective`,
  `Functor.mapHomologicalComplex`, and `QuasiIso` supply the remaining standard notions.
  In particular `unit` is the existing free rank-one sheaf, not a new structure sheaf.

Edge cases: the empty scheme and zero complexes are allowed; no Nonempty Y,
Noetherian, separated, affine, finite-dimensional, or boundedness hypothesis is
present. All integer degrees, including zero and negative degrees, are allowed.
The localization universe w is the same as the dependency's. I and J have the
same unrestricted O_Y-module carrier as the ambient category. The detection
hypothesis is on DQ of the particular morphism, not on all morphisms, and the
conclusion is not assumed as a hypothesis.

Searches:

- `msearch.py ... leansearch "coherator right adjoint quasi coherent derived category"`:
  unavailable, Internal Server Error. No verdict drawn from this unavailable service.
- `msearch.py ... leanfinder "coherator right adjoint inclusion quasi coherent derived
  category detects global sections"`: eight generic sheaf adjunction hits, none
  involving the scheme quasi-coherent derived full subcategory.
- `msearch.py ... loogle "Adjunction, DerivedCategory"`: zero hits, unknown identifier
  Adjunction in the service.
- `msearch.py ... grep "coherator|DQ_Y"`: zero hits.
- `rg` in source `WeilConjectures` for coherator and the node id: no match.
  `rg` for derived global sections gave only unrelated étale/Fourier declarations.
- `rg` in project `lean/Sheaf` for schemeDerivedCategory/schemeDerivedQCohCategory:
  only the dependency definition module. Searches for global sections found the
  shared ringed-space evaluation functor, reused here. No coherator statement.
- `tools/lean_names_upstream.py show lem-pc-dq-coherator-adjunction`: no declaration
  for this item in the upstream name lists.

Source checked: https://stacks.math.columbia.edu/tag/0B6I, final proof paragraph,
explicitly states detection, the Hom/cohomology equality, and the shifted structure
sheaf's membership in D_QCoh. Its current numbering is 48.3.10, whereas the node's
source metadata uses an older lemma number; the stable tag is the same. The
right-adjoint reference follows through Tag 0A9Q to the coherator lemma. No mathematical
statement correction or disputed claim was needed.

Validation: compiled the module on the server through `scompile.py`; no errors or
warnings. The dry-run delivery check is run after setting the node record.

## Second reading by K1

I read the item node, its source metadata (Stacks Project, `duality.tex`, Tag
0B6I, Lemma 48.1.1 proof and the `perfect-lemma-better-coherator` reference),
and the dependency declarations. The node's objects and clauses match the
Lean as follows:

- The object `Y` is the same `Scheme.{u}` in every declaration, with exactly
  `[CompactSpace Y]` and `[QuasiSeparatedSpace Y]`; no nonemptiness,
  Noetherian, separatedness, affineness, or boundedness assumption is added.
- `D(O_Y)` is `schemeDerivedCategory Y`, using the dependency's shared
  `[HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]`.
  `D_QCoh(O_Y)` is `schemeDerivedQCohCategory Y`, and its inclusion is the
  canonical `(schemeDerivedQCohProperty Y).ι`.
- `exists_dqCoheratorAdjunction` states existence of a functor `DQ_Y` and
  `Nonempty (Adjunction ... DQ_Y)`. The `Adjunction` object supplies the
  natural Hom bijection, with both source and target categories exactly those
  in the node.
- `dqCoherator_detects_globalSections` renders the node's consequence through
  K-injective representatives: arbitrary integer cochain complexes `I,J`, a
  chain map `f`, and `IsIso (DQ_Y.map (DerivedCategory.Q.map f))` imply
  `QuasiIso` of the termwise global-sections complex. This is the defining
  representative-level meaning of `RΓ(Y,u)`; no boundedness or
  quasi-coherence hypothesis is introduced for `I` or `J`.
- `structureSheaf_shift_is_derivedQCoh` states membership of the explicit
  degree-zero structure-sheaf complex shifted by `-i`, for every `i : ℤ`,
  exactly the node's `O_Y[-i]` clause.
- `globalSections_homology_equiv_structureSheaf_shift` gives the final
  equality `H^i(Y,E)=Hom(O_Y[-i],E)` in its representative form: an additive
  equivalence between degree-`i` global-sections homology and the derived Hom
  from the shifted structure sheaf to `DerivedCategory.Q.obj I`.

The empty scheme, zero complexes, degree `i = 0`, negative degrees, and all
integer shifts are admitted. The localization universe is the dependency's
`w`, and the complex index universe is fixed to `ℤ`; no edge case is excluded.

I searched Mathlib and `WeilConjectures/` with `rg`, the project declarations
with `rg`, `tools/lean_names_upstream.py show`, and the requested
LeanFinder/Loogle/LeanSearch queries recorded in `searches.jsonl`. They found
no existing coherator or equivalent statement. The two dependency modules
(`DerivedCategory` and `RingedSpaceModuleCohomology`) were opened and their
signatures match the node; no private replacement or new definition was
needed. No mismatch was found, so no source or statement correction was made.
The module was recompiled with `scompile.py` and produced no errors or warnings.
