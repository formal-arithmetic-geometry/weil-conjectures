## Worker report

The module `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBoundary` states
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_boundary`. Its only proof is
`sorry`, as required in stage 2. There are no new definitions, no dependency repairs,
and no statement corrections. The already-landed node
`def-sc-module-cohomology-boundary` is added to `stmt_deps` to cite the existing canonical
boundary. The item's other fields are unchanged apart from its `lean` record.

Hypothesis and clause matching:

- A morphism of schemes f:X -> Y is `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  The universe `u` is arbitrary; the established cohomology/f-map interfaces use this
  common ambient universe. There is no finite type, separation, smoothness or flatness binder.
- The two rows of Zariski modules are `E : ShortComplex (SheafOfModules.{u}
  Y.ringCatSheaf)` and the analogous `F` over `X`. The sites and rings are precisely the
  schemes' Zariski ring sheaves. `E.X₁`, `E.X₂`, `E.X₃`, `E.f`, `E.g` encode the three
  objects and two arrows; likewise for `F`. `hE : E.ShortExact` and `hF : F.ShortExact`
  assert exactness, a monomorphic first arrow and an epimorphic second arrow, so include
  both endpoint zeros. These are categorical sheaves of modules, not a sequence of bare
  modules or a sequence assumed exact on global sections.
- Each `φⱼ : E.Xⱼ ⟶ (pushforward f).obj F.Xⱼ` is a morphism in the module-sheaf category,
  hence is O_Y-linear on sections. No extra coefficient maps or arbitrary cohomology
  maps are inputs.
- The first commutative square is `_h₁₂ : φ₁ ≫ (pushforward f).map F.f = E.f ≫ φ₂`;
  the second is `_h₂₃ : φ₂ ≫ (pushforward f).map F.g = E.g ≫ φ₃`. Lean's composition
  order is left-to-right, so these are exactly the two equations of the node.
- The degree condition is `q : ℕ`; this includes degree zero. The cohomology objects
  are the recorded `RingedSpace.moduleCohomology`, i.e. right-derived module-valued
  global sections, not Ext cohomology of the underlying abelian sheaves.
- The canonical maps T_f^(q+1)(φ₁) and T_f^q(φ₃) are specified by the two conjuncts
  `(forget₂ _ AddCommGrpCat.{u}).map T₁ = moduleCohomologyFMap f φ₁ (q+1)` and the
  analogous equation for `T₃`. Their module-linear lifts are quantified existentially
  in the conclusion, not assumed in the hypotheses. Each is uniquely determined because
  this forgetful functor is faithful. Thus these are exactly the canonical maps, with
  their asserted module structures, not arbitrary replacements. Existence is already
  the content of the recorded basic-linearity proof dependency. This formulation adds
  no mathematical strength to the node's assertion that the equality uses linear maps.
- Both delta maps are exactly `RingedSpace.moduleCohomologyBoundary`, applied to `E,hE,q`
  and `F,hF,q`. This definition applies derived global sections to the canonical
  short-exact-sequence triangle and takes the boundary under the single-object
  comparisons, which is the convention explicitly specified in proof step 5. Each
  `HasDerivedCategory.standard _` is supplied as a term using `@`; no derived-category
  existence assumption or file-local instance is introduced.
- The final conjunct is `δ_E ≫ T₁ = T₃ ≫ (ModuleCat.restrictScalars f.appTop.hom).map δ_F`.
  This is exactly T_f^(q+1)(φ₁) composed after δ_E equal to δ_F composed after
  T_f^q(φ₃), expressed in Lean's composition order. `T₁` and `T₃` target modules with
  scalars restricted along `f.appTop.hom`, and restriction is also applied to δ_F.
  The equality therefore lies in modules over O_Y(Y), as required. Forgetting yields
  the identical equality of canonical additive maps since restriction changes no
  underlying elements.
- No quasi-coherence or acyclicity binder occurs. The flat-pullback instance uses
  `F = (tensorPullback f).mapShortComplex.obj E` and the unit of the adjunction recorded
  by `exists_tensorPullbackAdjunction f`: exactness follows from the recorded flat
  pullback theorem and the two squares are unit naturality. Flatness is needed only to
  supply `hF` for that instance, not for this theorem. For an automorphism no special
  restriction occurs: any compatible coefficient maps meet the same inputs. These two
  final clauses of the node are instances of the universally quantified equality,
  rather than additional choices of the underlying map.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.Algebra.Homology.ExactSequence`: the recorded exact-sequence interface;
  the actual row predicate is `CategoryTheory.ShortComplex.ShortExact` (read in
  `Mathlib/Algebra/Homology/ShortComplex/ShortExact.lean`).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is the
  transparent abbreviation for Mathlib's `SheafOfModules`, which the statement uses
  directly at the two scheme ring sheaves. No private module category is defined.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`:
  `Scheme.Modules.moduleCohomologyFMap`, including its full construction through
  `ModuleCohomologyFMapData.map` and the fixed section comparison.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`; its cohomology is the
  `RingedSpace.moduleCohomology` of
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`. Both sources and their full
  docstrings/signatures were read. The existential delta-functor of PQFCohomology is
  not chosen arbitrarily: the boundary is the specified canonical triangle boundary.
- Added landed dependency `def-sc-module-cohomology-boundary`, whose module is
  `WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary` and declaration is
  `AlgebraicGeometry.RingedSpace.moduleCohomologyBoundary`; its full definition and
  docstring fix the boundary and sign. Its standard derived-category instances are
  real constructions, not additional mathematical hypotheses.

All stated proof dependencies have plain imports, including basic linearity, f-map
independence, both horseshoe theorems, the fixed derived-triangle comparison, the
nonnegative-complex boundary comparison, pushforward-injectives sections, pushouts,
the snake lemma, enough injectives, flat pullback and the pullback adjunction. The
module docstring carries the node's eight-step natural-language proof, including
simultaneous pushouts, exactness at both ends, comparison of the boundary convention,
the two lift computations, inverse cancellation and scalar linearity. No proof has
been substituted for `sorry`.

Edge cases checked before writing: q=0 is included, using the same canonical boundary
without truncating its first exactness position; zero rows and zero coefficient maps
are allowed; the empty scheme is allowed (no nonemptiness or nontrivial-ring instance
is imposed); identity and automorphism scheme morphisms are included; nonflat f is
allowed because the target row is assumed exact independently, never deduced from
exactness of its arbitrary pushforward; arbitrary non-quasi-coherent/nonacyclic modules
are allowed. No endpoint injectivity/surjectivity has been dropped. No statement fault
or STATEMENT-DISPUTED issue was found.

Searches for an existing statement, performed through the prescribed wrapper:

- `msearch.py ... leanfinder "Maps on cohomology of sheaves of modules over different
  schemes induced by coefficient maps to pushforward commute with connecting
  homomorphisms"`: 8 hits, all ordinary sheaf/module pushforward components and
  composition/naturality formulas (including `SheafOfModules.pushforward_map_val`,
  `pushforwardNatTrans_*`, and `Scheme.Modules.pushforwardComp`); no exact statement.
- `msearch.py ... loogle '\"moduleCohomology\", \"δ\"'`: 0 hits.
- `msearch.py ... grep 'moduleCohomology|δ_naturality'
  CategoryTheory/Sites/SheafCohomology`: 0 hits in the pinned Mathlib directory.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id, f-map boundary
  combinations and the proposed full declaration name: no exact statement. The broader
  cohomology/connecting-map search found generic same-category `rightDerivedδ_naturality`
  and `RingedSpace.moduleCohomologyBoundary`; these are reused or read, not copied.
  The former does not compare two schemes' f-maps and cannot serve as an exact match.
- `rg moduleCohomologyBoundary` in both library roots and `dag/lean_names_upstream.json`
  found the canonical existing definition and its consumers; searching `dag/nodes`
  for its fully qualified declaration/module identified
  `def-sc-module-cohomology-boundary`, which is now cited.

Sources read locally: `literature/stacks-project/cohomology.tex`, equation
cohomology-modules (lines 63ff), equation-functorial-derived and Remark explain-arrow
(lines 2359ff); `literature/stacks-project/derived.tex`,
lemma-right-derived-delta-functor (lines 5680ff). These sources construct precisely
module-valued derived sections and its canonical boundary, with no flatness assumption
on the morphism giving an f-map.

Validation: `scompile.py Q146 lem-sfb-module-cohomology-fmap-boundary <module>` compiled
both the sandbox and library forms cleanly (2.3 s and 2.2 s respectively). Every
variable and universe is explicit, with `set_option autoImplicit false`; no diagnostic
commands, local notation, private definitions or file-local instances are present.

## Second reading by Q146

This is the dispatcher-assigned single-worker delivery. As explicitly instructed, no
other agent was started; the maintainer's independent review remains separate. The
following is a final self-check, not a claim of an independent worker review.

Reopened the node and Lean file together and checked: both schemes and the common
morphism; both three-object module rows and both endpoint exactness properties; all
three coefficient maps (in particular the middle map remains present in both squares);
the two square orientations; every nonnegative degree; the specific canonical f-maps;
the canonical derived-triangle boundaries with their fixed sign; and equality in the
correct O_Y(Y)-module category after restriction along f-sharp. The existential linear
lifts are fully pinned by the forgetful-map equations, so unpacking them yields the
node's equality of the very same canonical maps. There are no flatness, quasi-coherence,
acyclicity or derived-category existence assumptions. The flat-unit and automorphism
clauses are covered as instances of these same hypotheses. No mismatch was found in
this pass and no change was required. The existing boundary node was cited explicitly
instead of introducing a second boundary definition.
