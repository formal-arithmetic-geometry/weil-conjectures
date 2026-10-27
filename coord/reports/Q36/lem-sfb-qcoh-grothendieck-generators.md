## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiCoherentGrothendieckGenerators` states
`AlgebraicGeometry.Scheme.Modules.quasiCoherent_grothendieck_generators` with proof
`sorry`. No definitions, dependency repairs or statement changes are introduced.
The five-step source proof is included in the theorem docstring.

Clause-by-clause correspondence:

- Fixed universes: the explicit `universe u` is simultaneously the scheme, ring,
  module-section and small-diagram universe. `IsGrothendieckAbelian.{u}` and
  `CreatesColimitsOfSize.{u, u}` make the colimit size explicit. The full
  subcategory is large, with hom sets in `Type u`, exactly as for `X.Modules`.
- Every scheme: the sole input is `(X : Scheme.{u})`, with no geometric typeclass
  hypotheses. There is no quasi-compact, quasi-separated or Noetherian condition.
- QCoh is the full category of quasi-coherent module sheaves:
  `(SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory` is exactly the
  existing Mathlib full subcategory, not a new category or copied predicate.
  Its inclusion is the existing property inclusion `.ι` into
  `SheafOfModules X.ringCatSheaf`, namely module sheaves on the scheme's ringed
  Zariski site (the underlying type of `X.Modules`).
- Abelian and Grothendieck: `∃ hAb : Abelian ...` supplies the structure in the
  conclusion, and `@IsGrothendieckAbelian.{u} _ _ hAb` uses precisely that structure.
  It is not assumed as an input. This class supplies small colimits via
  `IsGrothendieckAbelian.hasColimits`, and includes a separator and AB5.
- Exact inclusion: the two clauses `PreservesFiniteLimits ...ι` and
  `PreservesFiniteColimits ...ι` express left and right exactness. Between these
  abelian categories this is equivalent to preserving short exact sequences.
- Creates all small colimits: `Nonempty (CreatesColimitsOfSize.{u, u} ...ι)`
  asserts Mathlib's standard creation structure exists for every small diagram.
  The class includes a lift of each ambient colimit cocone and reflection of
  colimits. Its lift identifies the ambient vertex with a quasi-coherent vertex;
  quasi-coherence is invariant under isomorphism. Thus every ambient colimit of
  quasi-coherent objects is quasi-coherent and has the full-subcategory universal
  property, including the empty-diagram case. `Nonempty` is required because this
  class contains cocone data and is not Prop-valued; no arbitrary datum is chosen.
- Generator: `∃ G : ...FullSubcategory, (coyoneda.obj (Opposite.op G)).Faithful`
  literally states faithfulness of Hom(G,-), as in the node.
- Filtered colimits exact: this is the `ab5OfSize` field of the explicit
  `IsGrothendieckAbelian.{u}` conclusion. It covers arbitrary small filtered
  categories, not just sequential systems.

Dependency declarations read and used:

- `def-weil-size-convention` is the recorded metatheoretic convention, rendered
  by explicit universes rather than a Lean object.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and the standard
  module-sheaf category `AlgebraicGeometry.Scheme.Modules` from
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`, the recorded module for
  `pqf-def-coherent`, publicly imports the exact existing notions
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.isQuasicoherent` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`. Only quasi-coherence
  is needed here; no finite-type or coherence hypothesis is imposed. The module's
  `IsQuasiCoherentFiniteType` conjunction is not substituted for quasi-coherence.
  Mathlib's local-presentation definition agrees with the affine tilde definition
  by the recorded tilde/counit equivalence on schemes.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  transparently abbreviates `SheafOfModules`; the theorem uses that same existing
  category, not a replacement module-sheaf construction.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`:
  `CategoryTheory.IsGrothendieckAbelian`, its `ab5OfSize`, `hasSeparator` and
  `hasColimits` declarations (the recorded Mathlib match).

The stated proof-dependency modules are plain imports: ambient scheme modules
Grothendieck abelian, open restriction and affine tilde/global-sections
adjunction, ring modules Grothendieck abelian, quasi-coherent kernels and
cokernels/images, the full abelian subcategory criterion, and bounded-generated
quasi-coherent submodule unions. The genuine proof dependency
`lem-sfb-bounded-generated-module-isoclasses` currently has no recorded Lean
module, so it has no import to add; its role remains explicit in proof step 4.
It is not needed to type this statement and no substitute is introduced.

Edge cases checked against the source:

- Empty scheme and zero module: the quasi-coherent category can be trivial;
  the zero object is a valid generator since all parallel maps coincide.
- Empty colimit diagram: `CreatesColimitsOfSize` quantifies over it and creates
  the zero/initial module; no nonempty-diagram hypothesis appears.
- Infinite coproducts, infinitely many affine charts and non-affine intersections
  are allowed. Neither the statement nor the source's cardinal construction
  requires a finite cover or quasi-separatedness.
- Arbitrary small filtered categories are covered by AB5. There is no larger
  independent indexing universe, and no accidental restriction to finite,
  countable or directed-poset diagrams.

Source inspection: read `literature/stacks-project/properties.tex`,
`proposition-coherator` (Tag 077P), statement and proof (1), and
`literature/stacks-project/schemes.tex`, `lemma-colimit-quasi-coherent` (Tag 01ID).
The statement imposes no extra hypotheses relative to either source. No
STATEMENT-DISPUTED issue or node fault was found.

Searches made (2026-10-24):

- `msearch.py ... leanfinder "For any scheme quasi coherent sheaves form a
  Grothendieck abelian category and the inclusion creates all small colimits"`:
  eight hits, including ambient `Scheme.Modules.instHasColimits`, ambient
  `Scheme.Modules.instAbelian`, ordinary sheaf Grothendieck instances and the
  existing quasi-coherent object property. None states the QCoh theorem.
- `msearch.py ... leansearch "The full subcategory of quasi coherent module
  sheaves on a scheme is Grothendieck abelian"`: eight hits, again ambient
  module/sheaf Grothendieck results and definitions, with no matching theorem.
- `msearch.py ... loogle '"IsQuasicoherent", "IsGrothendieckAbelian"'`: zero hits.
- `msearch.py ... grep
  'quasicoherent.*(Grothendieck|CreatesColimits)|Grothendieck.*quasicoherent'`:
  zero hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and Mathlib for quasi-coherent
  full subcategories, quasi-coherent colimits, and Grothendieck instances:
  Mathlib already has `SheafOfModules.isQuasicoherent` and its full subcategory;
  existing scheme results concern ambient module sheaves, kernels, cokernels,
  coproducts or affine sections of colimits. Algebraic-space QCoh and derived
  QCoh are different categories. No theorem matches all the item's clauses.
- Searched the proposed full theorem name in both project roots, Mathlib and
  `dag/lean_names_upstream.json`: no collision. Searched this node id in upstream
  `WeilConjectures`: no occurrence.

Validation: compiled through `scompile.py`, both sandbox and library module
modes. The final explicit-universe version is also compiled before delivery.

## Second reading by Q36

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
