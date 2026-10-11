## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentFormalShortExactLevels` states
`AlgebraicGeometry.coherentFormalModule_shortExact_levels`, with proof `sorry` only.
It states exactly the two facts from the first paragraph of the proof of Stacks 0CYV,
using the category and level conventions of the recorded dependency. The local Stacks
source is absent on this machine; read the source at
https://stacks.math.columbia.edu/tag/0CYV and
https://stacks.math.columbia.edu/tag/087X instead. No node correction is required.

Hypothesis and clause correspondence:

- `X : Scheme.{u}` and `[IsNoetherian X]` give the Noetherian scheme. Mathlib's
  `IsNoetherian` extends `IsLocallyNoetherian X` and `CompactSpace X`, precisely
  the locally Noetherian and quasi-compact assumptions in the node.
- `I : X.IdealSheafData` is the shared quasi-coherent ideal-sheaf encoding used by
  the recorded formal-module definition; there is no new ideal notion.
- `S : ShortComplex (CoherentFormalModule X I)` has `S.X₁ = G`, `S.X₂ = F`,
  `S.X₃ = H`, `S.f = beta`, and `S.g = alpha`. Its zero-composite field is the
  complex condition. `hS : S.ShortExact` asserts exactness, monicity of beta,
  and epicity of alpha in the formal category, the short exact sequence hypothesis.
- Components are the natural-transformation components `S.f.hom.app (op n)` and
  `S.g.hom.app (op n)`. The existing full-subcategory inclusion followed by evaluation
  gives exactly these objects and maps, with their inherited zero-composite proof.
- Clause (a): `∀ n : ℕ, (S.map (... evaluation ... (op n))).Exact ∧
  Epi (S.g.hom.app (op n))`. Exactness is in `X.Modules`, at F, and the second
  component is an epimorphism (surjective as a sheaf, equivalently locally surjective
  on sections). It does not assert surjectivity on every open's sections.
- Clause (b): `∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ q :
  kernel (S.g.hom.app (op m)) ⟶ S.X₁.obj.obj (op n), Epi q` is exactly an
  O_X-linear surjection from the later component kernel onto G at the specified level.
- Every `op n` is positive level `n + 1`, as in the dependency. Quantification over
  all naturals therefore covers exactly all positive levels; `n ≤ m` is equivalent
  to the required inequality of positive levels. No zeroth level is imposed.
- The parenthetical warning about beta is rendered by the absence of any `Mono`
  conclusion on its component, not a claim that every component fails to be mono.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  and the bundled `AlgebraicGeometry.IsNoetherian` class.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `AlgebraicGeometry.CoherentFormalModule`
  and `AlgebraicGeometry.IsCoherentFormalModule`, their defining signatures and docstrings.
  The full-subcategory inclusion is `CategoryTheory.ObjectProperty.ι`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`:
  `AlgebraicGeometry.coherentFormalModule_abelian` was read in full; it asserts
  abelianness and the termwise cokernel universal property. This module imports the
  shared category and its preadditive functor-category machinery. The signature needs
  only the existing zero morphisms to express `ShortExact`, so it makes no additional
  assumption or choice of an Abelian structure.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `AlgebraicGeometry.Scheme.Modules`,
  the existing abelian category of sheaves of O_X-modules.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact` and `.Exact`:
  `CategoryTheory.ShortComplex.ShortExact` and `CategoryTheory.ShortComplex.Exact`,
  the recorded exact-sequence notions. `ShortComplex.map` evaluates the sequence.

Edge cases checked: `n = 0` denotes actual level 1 and is included; equality `m = n`
  is permitted. The empty scheme and zero systems are included, with epimorphic zero
  maps onto zero objects. For the zero ideal the category describes constant compatible
  systems; for the unit ideal every level vanishes, also included. Noninjective beta
  components are allowed. All universes and variables are explicitly bound; there is
  no independent test-object universe or extra Abelian instance hypothesis.

Searches performed on 2026-10-11:

- `msearch.py ... leansearch 'coherent formal module short exact sequence levelwise
  right exact'`: unavailable, Internal Server Error; no verdict from this service.
- `msearch.py ... leanfinder 'short exact sequences of coherent formal modules are
  levelwise right exact and each kernel level is a quotient of a later levelwise
  kernel'`: eight hits, including `ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`,
  `ShortComplex.moduleCat_exact_iff`, refinements, and unrelated Profinite exactness;
  none states the formal-system result.
- `msearch.py ... loogle 'ShortComplex.ShortExact, ShortComplex.Exact'`: zero hits,
  unknown identifier `ShortComplex.ShortExact`; the fully qualified declaration was
  separately read in the pinned Mathlib source.
- `msearch.py ... grep 'formal.*[Ss]hort|[Ss]hort.*formal|[Ii]nverse.*[Ss]ystem'
  AlgebraicGeometry`: three inverse-system hits, all in `AffineTransitionLimit.lean`,
  on inverse systems of schemes, not coherent formal-module exactness.
- `rg -n 'coherentFormal.*(exact|Exact)|formal.*short.*exact|lem-weil-pbc-coherent-formal-short-exact-levels'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures lean/Sheaf dag/lean_names_upstream.json`:
  no matching declaration or upstream node attachment. The module's chosen declaration
  name therefore does not duplicate an existing statement.

Server compilation: `scompile.py P1 lem-weil-pbc-coherent-formal-short-exact-levels
<module>` succeeded, exit 0, 2.1 seconds, with no warnings or errors.
No new nodes, dependency modules, or statement faults.

## Second reading by P1

I reread the node statement against the Lean declaration and the cited Stacks source (0CYV,
paragraph after the lemma statement, and 087X, kernel construction).

- Objects: `X : Scheme.{u}` with `[IsNoetherian X]` renders a Noetherian scheme; `I :
  X.IdealSheafData` renders the quasi-coherent ideal sheaf; `S : ShortComplex
  (CoherentFormalModule X I)` renders the sequence in `Coh(X,I)`; `hS : S.ShortExact`
  renders its short exactness. The components are `S.f.hom.app (op n)` and
  `S.g.hom.app (op n)`, with `S.X₁`, `S.X₂`, and `S.X₃` the three systems.
  These match the node and the source.
- Hypotheses: no extra separatedness, finiteness, characteristic, or universe hypothesis
  is introduced. `IsNoetherian` supplies exactly the Noetherian assumption, and the ideal
  is the dependency's quasi-coherent ideal-sheaf object.
- Clause (a): the first conjunct is exactness of the evaluated short complex in
  `X.Modules`, and `Epi (S.g.hom.app (op n))` is the categorical sheaf epimorphism;
  together they render exactness at `F_n` and surjectivity of `alpha_n`. `op n` is level
  `n+1`, so `n : ℕ` ranges over precisely all positive levels.
- Clause (b): `∀ n, ∃ m, n ≤ m ∧ ∃ q : kernel (S.g.hom.app (op m)) ⟶
  S.X₁.obj.obj (op n), Epi q` renders a later level kernel epimorphically mapping to
  `G_n`, with the required level inequality. The quantifier order is unchanged.
- The absence of a `Mono` conclusion for the first component preserves the source's
  warning that `beta_n` need not be injective.

Edge cases checked: `n = 0` is level 1 and is included; `m = n` is allowed; zero
objects and the empty scheme are not excluded; zero maps onto zero objects satisfy the
categorical epimorphism clauses; zero and unit ideals remain admitted. No characteristic
or independent test-object universe is imposed.

I searched the pinned source and Mathlib with `rg` for coherent-formal short exact and
levelwise exactness declarations, and ran the recorded `msearch.py` LeanFinder/Loogle
queries. Only generic `ShortComplex` and unrelated inverse-system results were found;
there is no existing declaration of this statement. The recorded searches and dependency
signatures were checked, including `CoherentFormalModule`, its full-subcategory inclusion,
and `coherentFormalModule_abelian`.

No mismatch was found. The module and node already render the source statement exactly;
no Lean or node repair was necessary. The module compiles cleanly with `scompile.py`.
