## Worker report

Item: `lem-sfb-constant-restriction-ordinary-monoidal`. Existing statement delivery:
no new Lean module, definition, theorem, or proof is written. The ordinary part of
`Sheaf.CategoryTheory.ConstantScalarRestrictionTensor` already states this node.
Its primary declaration is
`CategoryTheory.ConstantScalarRestriction.ordinary_exists`; the record also lists
its normalization structure and the existing additivity, equivalence, exactness,
and unchanged-underlying-sheaf extension assertions. The live server source was
read using `scompile.py --source Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`.
There is no repair note for this item. The live node has a stage-1 split and review
but no Lean record, so this delivery supplies a new Lean record rather than an
unchanged node packet. The sandbox initially contained only dispatcher brief markers.

### Hypotheses and objects

- An arbitrary site small in the coefficient universe is rendered by the enclosing
  `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)` and
  `(B : Type (max u v)) [CommRing B]`. Objects and morphisms have independent
  universes. This is also the universe convention of the recorded actual
  `constantRingModuleRestriction` dependency. Grothendieck topologies express the
  site through covering sieves; no global pullback, terminal object, point,
  inhabitedness, or nonzero coefficient hypothesis occurs.
- Exact abelian sheafification and the prescribed sheafified tensor are the existing
  small-site structures. `fixedSheafify` supplies `HasSheafify J (ModuleCat B)`;
  `ringAbelian` and `fixedAbelian` use the actual abelian category instances.
  `fixedMonoidal` and `fixedSymmetric` are the fields of the dependency's
  `sfbSheafTensorStructure`, rather than independently selected tensors.
- The constant commutative ring sheaf is `ConstantScalarRestriction.ring J B`, defined
  as `(constantSheaf J CommRingCat).obj (CommRingCat.of B)`. `Modules J B` is
  `SheafOfModules` over its underlying ring sheaf. Its tensor is the recorded
  `cochainModulesMonoidal` localization tensor; `ringPure` uses the actual
  `SheafOfModules.tensorObjIsoSheafification` and module sheafification unit.
  This is the balanced sheafified sectionwise tensor, with its induced constraints.
- `Fixed J B` is literally `Sheaf J (ModuleCat B)`. `fixedPure` uses the actual
  `sfbSheafTensor_comparison` and `toSheafify` of the objectwise module tensor.
  `fixedUnitIso` identifies its unit with the constant module sheaf, as asserted
  by `sfbSheafTensor_properties`. `fixedUnitScalar` is precisely the image of
  `b` under that module sheafification unit, transported back by `fixedUnitIso`.
- `restriction J B` first restricts along the canonical
  `constantCommuteCompose ... .inv.app (CommRingCat.of B)`, then applies exactly
  the dependency's `constantRingModuleRestriction J B`. This identifies the
  RingCat sheafification with the underlying ring sheaf of the CommRingCat
  sheafification. It retains the original section groups and maps and restricts
  the action along the actual constant-section unit; the canonical identification
  commutes with that unit. It introduces neither an arbitrary equivalence nor
  an arbitrary scalar map.

### Each conclusion

- The actual forward functor is additive, an equivalence, and exact by the existing
  declarations `ConstantScalarRestriction.additive`, `.isEquivalence`, and `.exact`.
  Exactness here is `CategoryTheory.exactFunctor _ _ (restriction J B)`, for the
  actual two abelian categories.
- The unchanged-abelian-sheaf inverse and its unique extended action are given by
  the existing `CategoryTheory.constant_ring_module_sheaves`. Its first conjunct
  supplies an equivalence whose forward functor equals
  `constantRingModuleRestriction J B`, both functors are additive, and its inverse
  composed with `SheafOfModules.toSheaf` equals `sheafCompose` with the forgetful
  functor to abelian groups. Its second conjunct says the compatible extended
  action exists uniquely, and its third says every fixed-ring linear sheaf map
  remains linear under any such extensions. Transport along the canonical ring
  sheaf isomorphism above retains the same sections and maps. This is exactly the
  node's G. Any inverse equivalence preserves kernels and cokernels (indeed all
  limits and colimits), giving its exactness without an extra hypothesis.
- `.ordinary_exists` asserts `Nonempty (Ordinary J B)`. `Ordinary.braided` is a
  `Functor.Braided` structure on this very restriction functor; its monoidal
  component has invertible unit and tensorator, with naturality and all coherence
  laws. Define the node's c as the inverse tensorator, equivalently the oplax
  comparison delta; define u as the inverse unit, equivalently the oplax unit eta.
  Thus c has direction F(M tensor N) to FM tensor FN, while its inverse is the lax
  tensorator mu. The unit u has direction F(unit) to unit.
- `Ordinary.tensor_hom` states for every `M N U x y` that delta carries
  `ringPure J B M N U x y` to
  `fixedPure J B (restriction.obj M) (restriction.obj N) U x y`.
  `Ordinary.tensor_inv` states the reverse formula for mu on these same pure
  tensors. Both quantify over every site object and every pair of local sections;
  these are the node's two required pure-tensor formulas, including the actual
  sheafification-unit images, not an assertion merely that some isomorphism exists.
- `Ordinary.unit_hom` states for every `U b` that eta takes
  `(toSheafify J ((Functor.const _).obj (CommRingCat.of B))).app U b`
  to `fixedUnitScalar J B U b`. The former is iota(b), and the latter is eta_B(b)
  in the specified unit, by the definitions just read. This is the required
  ordinary unit normalization, including b = 0 and b = 1.
- `Functor.Braided.toMonoidal` includes tensor naturality, associativity and the
  two separate unit equations; its braiding condition gives the symmetry equation.
  Both coefficient categories are symmetric, so this is strong symmetric
  monoidality. `Functor.Monoidal` stores mutually inverse lax and oplax maps;
  no direction of the comparison or inverse equation is omitted.
- The inverse structure on G is the inverse monoidal equivalence structure:
  Mathlib's `CategoryTheory.Equivalence.inverseMonoidal` constructs it from the
  forward structure using the equivalence unit and counit. Its comparisons are
  precisely the inverse comparisons conjugated by those identifications, as in
  the node's last proof step. The underlying equivalence identifications for the
  unchanged-section model are identities on abelian sections. Its symmetry law
  is detected by faithful F and reduces to the forward symmetry equation.
  This is a formal inverse-equivalence clause, not extra undetermined data.

These declarations together give exactly the ordinary statement. The existing
module additionally contains total-complex and derived results; those results
are not part of this node's Lean attachment. Adding a new copy of the ordinary
statement would duplicate its already normalized ordinary assertion.

### Dependency declarations read and used

- `def-weil-pbc-sites-and-cohomology`: `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`; for this topology-level
  statement the existing `GrothendieckTopology` and `Sheaf` encode its site/sheaf
  component. The sheaf cohomology part is not used by this ordinary statement.
- `def-weil-size-convention`: its record explicitly supplies a metatheoretic
  convention, with no declaration; the enclosing explicit universe parameters
  implement it.
- `sk-def-sfb-sheaf-tensor`: `Sheaf.CategoryTheory.SheafTensor`,
  `CategoryTheory.sfbSheafTensor_properties` and `.sfbSheafTensor_comparison`.
  The structure itself is `CategoryTheory.sfbSheafTensorStructure` in
  `Sheaf.CategoryTheory.SheafTensorStructure`.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`.
- `def-weil-pbc-sheafification`: `Mathlib.CategoryTheory.Sites.Sheafification`,
  `CategoryTheory.presheafToSheaf`, `.toSheafify`, `.sheafificationAdjunction`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`.
- `def-sfb-constant-ring-module-restriction`:
  `Sheaf.CategoryTheory.ConstantRingModuleSheaves`,
  `CategoryTheory.constantRingModuleRestrictionPresheaf` and
  `.constantRingModuleRestriction`. The same public module also gives
  `.constant_ring_module_sheaves`, read in full.
- `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
  `SheafOfModules.cochainModulesMonoidal` and `.cochainModulesSymmetric`.
  `SheafOfModules.tensorObjIsoSheafification` specifies its actual tensor values.
- `lem-pc-sheaf-modules-tensor-closed`:
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`,
  `SheafOfModules.tensorClosed`; read its full statement and proof docstring.
  It packages the additive symmetric monoidal closed structure. The independent
  site universes use the generalized cochain tensor instances recorded by the
  tensor dependency, which construct this same localization tensor.
- `def-sfb-strong-monoidal-functor`: the node is a Mathlib leaf;
  `Mathlib.CategoryTheory.Monoidal.Functor`,
  `CategoryTheory.Functor.CoreMonoidal`, with `Functor.Monoidal` as its equivalent
  forward/inverse-map interface. The full unit, tensorator, naturality,
  associativity, left-unit and right-unit fields were read.

### Sources and edge cases

Read `literature/stacks-project/sites-modules.tex`,
`lemma-sheafification-presheaf-modules` (03CY),
`section-tensor-product` (03EK), and `lemma-sheafification-tensor` (0GMW),
including the adjacent Bilin universal property and constraint discussion.
These are the construction used by the existing package's ordinary proof
and the newly reviewed ten-step DAG split. No statement correction is needed.

For the zero ring every module of sections is subsingleton, so the tensor and
unit equations have their unique values; no `Nontrivial B` appears. For an
empty site every section-quantified formula is vacuous and the relevant
presheaf/sheaf categories are terminal; no `Nonempty C` appears. Empty covering
sieves are allowed by `GrothendieckTopology`. The unit is sheafification of the
constant regular module, never evaluation at a terminal object. No enough-points
assumption is present: local equality and sheafification operate on covering
sieves. Tensor normalization is stated on all sections, and the unit formula
is retained independently; it is not replaced by the tensor formula at a
regular module.

### Searches

- `msearch.py`, LeanFinder: "Constant ring scalar restriction on sheaves of modules
  is an exact symmetric monoidal equivalence preserving local pure tensors and
  the sheafification unit". Eight hits: general scalar restriction and light
  condensed monoidal structures; no complete arbitrary-site normalized theorem.
- `msearch.py`, Loogle: "Functor.CoreMonoidal, SheafOfModules.restrictScalars".
  Zero hits, with an unknown-identifier diagnostic for the unqualified first
  name. The local full Mathlib declaration was then read directly, rather than
  interpreting this search diagnostic as evidence that the structure is absent.
- `msearch.py`, Mathlib grep: "constant.*(equivalence|monoidal)|
  (equivalence|monoidal).*constant" in `Algebra/Category/ModuleCat`: zero hits.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `ordinary_exists`, `structure Ordinary`, `constant_ring_module_sheaves`, and
  constant/monoidal names. Found the exact existing ordinary package in
  `Sheaf.CategoryTheory.ConstantScalarRestrictionTensor` (main ordinary
  declarations at lines 177-251) and the unchanged-sheaf equivalence in
  `Sheaf.CategoryTheory.ConstantRingModuleSheaves` (line 317).
  The item id itself occurs in neither source tree. Reading the exact
  declaration signatures and docstrings confirmed the match described above.
- `scompile.py --source Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`
  confirmed that the existing module is present in the current server sources.

No new nodes or dependency modules are needed. No source or statement fault was
found. No second agent was started; the maintainer performs the independent review.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
