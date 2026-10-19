## Worker report

This is stage 2, following the already reviewed stage-1 split by Q81. That split
has no Lean binding and therefore does not supersede this stage-2 task. The delivered
module states `AlgebraicGeometry.Etale.nonempty_geometricPointDerivedConstantsData`,
with one `sorry`. Its conclusion packages the full normalized equivalence in
`GeometricPointDerivedConstantsData`. The auxiliary abbreviations specialize existing
constructions and supply actual data; no definition chooses data from the existence theorem.
There are no new DAG nodes, dependency repairs, or statement changes.

Hypotheses and clauses, in the order of the node:

- `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]` are exactly the algebraically closed
  field hypothesis. `Spec (.of Ω)` is the specified scheme; no scheme or point is
  independently chosen.
- Abelian groups are encoded as `ModuleCat.{u+1} (ULift.{u+1} ℤ)` and abelian sheaves
  as sheaves valued in that category. Restricting along `ULift.ringEquiv.symm` and
  forgetting the unique integer action is the canonical equivalence to abelian
  groups (`ModuleCat.restrictScalarsEquivalenceOfRingEquiv` and
  `ModuleCat.forget₂AddCommGroupIsEquivalence`). This is the integer coefficient
  convention explicitly recorded in `def-kun-derived-tensor`, not a finite or
  rational coefficient specialization. Every abelian group and sheaf in the chosen
  size universe admits this unique action; there is no extra mathematical hypothesis.
- `geometricPointStalk Ω` is `Point.sheafFiber` at the identity geometric point.
  The point is represented by `((pointSmallEtale (𝟙 _)).ulift.{u+1})`: the universe
  lift changes only the category-of-elements presentation. The existing
  `Point.uliftSheafFiberIso` identifies it canonically with the unlifted stalk;
  its source constructs the comparison from the equivalence of the indexing
  categories. This is necessary because the concrete coefficient category lives
  in `Type (u+1)`, while the small etale point initially lives in `Type u`.
  No site object/morphism universe equality is imposed.
- `geometricPointConstants Ω` is exactly `constantSheaf`, the sheafification of the
  constant presheaf. It is not another construction of the constant sheaf.
- `stalkAdditive`, `stalkEquivalence`, and `constantEquivalence` record additivity
  and quasi-inverse equivalence of the fixed functors. Constant-sheaf additivity
  and preservation of finite limits/colimits are existing instances; the stalk
  is exact as an additive equivalence. The two fixed functors are paired by
  `adjunction : geometricPointConstants Ω ⊣ geometricPointStalk Ω`.
- `geometricPointConstantGerm Ω` is the inverse of the existing
  `Point.constantSheafCompSheafFiberIso`. Its source constructs the map by the
  constant-presheaf colimit coprojection followed by sheafification, hence it
  sends an element to its constant germ. `unit_eq` fixes the adjunction unit to
  precisely this map, which is already an isomorphism.
- `counitIsIso` gives the counit isomorphism. `counit_unique G f` states the exact
  iff: the image of `f` under the actual stalk is inverse to the constant-germ
  unit at `SG` iff `f` is the displayed counit. This includes both the prescribed
  formula and uniqueness, not only some abstract inverse equivalence.
- All derived functors are `Functor.mapDerivedCategory`, so they are the
  localization of the termwise functors `mapHomologicalComplex (.up ℤ)`.
  `adjunction.mapDerivedCategoryAdjunction` is the existing termwise derived
  adjunction. `derivedUnitIsIso` and `derivedCounitIsIso` make these specified
  functors quasi-inverse, with the unit and counit descended from the specified
  underived adjunction, rather than separately chosen derived transformations.
- `constant_isGE` and `stalk_isGE` quantify over every integer `a` and every
  object of each unbounded derived category. `DerivedCategory.IsGE K a` is
  cohomology vanishing below `a`. No bounded representative is required.
- All `⊗` use the existing K-flat monoidal structure imported by
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`; its `derivedTensor` is
  `curriedTensor` of exactly this structure. On the coefficient category it is
  ordinary tensor over the lifted integer ring, hence ordinary integer tensor.
- `constantMonoidal` supplies a braided strong monoidal structure for the fixed
  constant functor. The stalk's monoidal structure is the existing canonical
  one in `Mathlib.CategoryTheory.Sites.Point.Monoidal`: its comultiplication is
  induced by the two germ coprojections, and its inverse multiplication is the
  germ-of-local-tensor map. `unit_monoidal` fixes the constant tensorator through
  this germ comparison and the canonical constant-germ unit. Consequently, on
  constant pure tensors its formula is exactly `m ⊗ n ↦ m ⊗ n`; this normalization
  also fixes the unit tensor comparison. `counit_monoidal` asserts the matching
  monoidal equations for the uniquely normalized counit.
- `derivedConstantMonoidal` and `derivedStalkMonoidal` are strong monoidal
  structures for those exact termwise derived functors. The fields
  `constant_factors_monoidal` and `stalk_factors_monoidal` require the canonical
  `mapDerivedCategoryFactors.hom` to be monoidal. The comparison on complexes
  used here is the existing `Functor.mapCochainComplexMonoidal`, induced degree
  by degree from the underived comparison and direct-sum tensor totalization.
  The localization functor has its existing canonical lax tensorator. Thus the
  equation fixes the derived tensorator to the canonical comparison on K-flat
  representatives, where the localization tensorator is invertible. This
  excludes arbitrary monoidal structures that are not the derived germ maps.
- `integerDerivedSymmetric`, `integer_symmetry_eq`, and the fully constructed
  `geometricPointIntegerDerivedSymmetry` fix the coefficient symmetry to the
  existing canonical `DerivedMonoidal.braiding` induced by Koszul symmetry.
  `sheafDerivedSymmetric` supplies a symmetry on the existing ordinary derived
  sheaf tensor. The `constant_symmetry` equation uniquely determines this
  symmetry: the specified derived constant functor is essentially surjective,
  and its tensorators are invertible and already normalized by
  `constant_factors_monoidal`. Thus the structure does not allow an arbitrary
  unrelated braiding. The usual derived sheaf Koszul symmetry has exactly this
  equation, since the termwise constant comparison preserves the Koszul signs
  and computes the specified derived comparison on K-flat representatives.
  `stalk_symmetry` asserts the corresponding compatibility for the stalk.
  This characterization avoids an expensive definitional conversion between
  equivalent library presentations of the sheaf derived monoidal structure;
  it changes no functor, tensor product, or symmetry. No definition chooses
  symmetry data from a postponed existence theorem.
- `derived_unit_monoidal` and `derived_counit_monoidal` assert both the tensor and
  unit equations (`NatTrans.IsMonoidal`) for the actual descended unit and
  counit. Invertibility is recorded in the adjacent fields.

Dependency declarations read and used:

- `def-weil-pbc-geometric-stalks`: `Point.sheafFiber` in
  `Mathlib.CategoryTheory.Sites.Point.Basic`, and `Scheme.pointSmallEtale` in
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`. The equivalent size transport is
  `Point.ulift`/`Point.uliftSheafFiberIso` in
  `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic`.
- `def-kun-constant-sheaf`: `constantSheaf` in
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`, and
  `Functor.mapHomologicalComplex` in `Mathlib.Algebra.Homology.Additive`.
- `def-weil-pbc-derived-categories`: the coefficient encoding and derived
  category described by `WeilConjectures.AlgebraicGeometry.DerivedCategories`;
  the current module was read through `scompile.py --source` because the older
  reference checkout does not contain that module.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `Q`, and the
  localization instances in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-kun-derived-tensor`: `AlgebraicGeometry.Etale.derivedTensor` in
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`, the existing K-flat
  monoidal derived structure; no second tensor is defined.
- The unit uses `Point.constantSheafCompSheafFiberIso` and
  `Point.sheafFiberConstantSheafIso` in
  `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf`.
- The existing functorial derived adjunction is
  `Adjunction.mapDerivedCategoryAdjunction` in
  `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`.
- The recorded proof-dependency modules for abelian/Galois equivalence,
  constant-germ invertibility, exact cohomology, localization, site tensor and
  K-flat resolutions are imported without `public`. The theorem docstring
  carries all seven proof steps with the unbounded K-flat argument.

Edge cases checked against the statement and its constructions: zero group,
zero sheaf, zero complex, unit `ℤ`, negative lower bounds, arbitrary shifts,
unbounded complexes, and the ordinary derived tensor of `ℤ/2` with `ℤ/2`
(which retains Tor in degree -1). The factorization normalization applies on
all complexes and computes on K-flat replacements; it never replaces derived
tensor by degreewise tensor or assumes flat coefficients. Over an algebraically
closed field the Galois action is trivial; dropping algebraic closure would
incorrectly identify nontrivial Galois representations with constant sheaves,
so that assumption is retained. No finiteness, torsion, properness or
constructibility hypothesis was introduced.

Searches made with the prescribed wrapper:

- LeanFinder: “Exact symmetric monoidal constant sheaf and geometric stalk
  equivalence on derived categories of abelian sheaves over an algebraically
  closed field”: eight hits, including `Sheaf.isConstant_iff_of_equivalence`,
  `Sheaf.H`, `Sheaf.isConstant_iff_forget`, condensed locally constant module
  equivalences, and a light condensed monoidal instance. None states this
  normalized unbounded derived point equivalence.
- Loogle: `"constantSheaf", "IsEquivalence"`: zero hits.
- Mathlib grep: `constantSheaf.*[Ee]quivalence|[Ee]quivalence.*constantSheaf|stalk.*[Ee]quivalence`:
  zero hits.
- Source `rg`: constant/stalk equivalence, derived constant/stalk, and item ID
  in the upstream `WeilConjectures` tree and project `lean/Sheaf`. The plausible
  upstream `SixFunctors/Etale/Derived/Point.lean` proves detection of
  isomorphisms and states finite-coefficient duality, not this equivalence;
  `AlgebraicGeometry/Sites/DerivedStalk.lean` proves conservativity only.
  The canonical constant-germ isomorphism is reused. A name search in
  `dag/lean_names_upstream.json`, the upstream sources and `lean/Sheaf` found
  no collision for the delivered declarations.

The source texts read were Stacks 04JQ and the geometric-point reduction in
0F0F in `etale-cohomology.tex`. The item is unchanged from the reviewed split;
there is no statement dispute. The only previous failure was a stage-1/stage-2
assignment confusion; the current node still needs the Lean binding delivered here.

Validation: the delivered module passed the prescribed `scompile.py` wrapper
both in its sandbox name (23.1 seconds) and final library name (33.7 seconds),
with no errors or warnings. All variables and universes are explicit and
`autoImplicit` is disabled. The node differs from the shared copy only in
`lean`; its recorded signature matches the module verbatim.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
