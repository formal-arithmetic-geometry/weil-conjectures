## Worker report

The item is stated in `Sheaf.Paper.FiniteFieldDerivedTensorSummand`, declaration
`FiniteFieldDerivedTensor.exists_diagonal_derived_tensor_summand`. Its only proof is `sorry`.
`HasDiagonalComparison` is the full existential proposition of the canonical comparison;
`ChainComparison` packages only the representative maps and their generator equations.
The helper specializations, pure-tensor generators, comparison isomorphisms and structures
contain real data and no postponed proofs. They package this node's canonical comparison;
they do not introduce a second sheaf category, tensor product or derived category.

Hypotheses and clauses:

- The fields and extension are `[Field F] [Field B] [Finite F] [Finite B] [Algebra F B]`.
  `algebraMap F B` supplies the injective field homomorphism.
- The ordinary balanced tensor algebra is `B ⊗[F] B`, and multiplication is
  `Algebra.TensorProduct.lmul' F`.
- The existential `e` satisfies the three displayed clauses verbatim: `e * e = e`,
  `Algebra.TensorProduct.lmul' F e = 1`, and the universal annihilator equation for `b : B`.
- The arbitrary site is `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)`.
  Coefficients and module sections live in `max u v`. There is no equation `u = v`.
  The size convention allows enlargement to a common containing universe. The
  `HasSheafify J CommRingCat` and two `HasDerivedCategory` arguments supply the choices
  of sheafification and localization, not mathematical restrictions on the site or complexes.
- `coefficients J A` is the recorded `constantSheaf` evaluated at `CommRingCat.of A`;
  `rings` just forgets commutativity. The coefficient morphism is the image of
  `algebraMap F B` under those two functors.
- `Modules` is the recorded `ringedSiteModules`, transparently `SheafOfModules`;
  `Derived` is Mathlib's unbounded `DerivedCategory`. `Complexes` has index `ℤ`.
- `total` is exactly `curriedTensor` for `SheafOfModules.monoidalCategory`, extended by
  `map₂HomologicalComplex`, hence direct-sum total tensor with its signed differential.
  `representatives` is the full property of K-flat complexes with flat terms. Flatness
  is written as exactness of the existing right-tensor functor, with no new flatness notion.
- `Presentation` records the natural representative comparison of the tensor bifunctor
  from `lem-weil-pbc-site-derived-tensor-descent`, now at independent site universes.
  The theorem asserts that presentations exist for both fields, and applies to every
  presentation, so a missing presentation cannot make the result vacuous.
- `restrictComplex` applies the recorded `SheafOfModules.restrictScalars` termwise.
  the existential `res` in `HasDiagonalComparison` is pinned down by its natural `restriction` isomorphism on ALL
  complexes: `restrictComplex ⋙ Q ≅ Q ⋙ res`. Thus it is the induced exact restriction,
  not an arbitrary derived functor. `compatible` asserts that the chosen flat-term
  K-flat B-representatives are still such representatives over F.
- The existential `action` is a ring homomorphism from `B ⊗[F] B` to the endomorphisms of
  the entire source bifunctor. Consequently each action is natural in BOTH derived
  variables. `ChainComparison.chainAction` and `ChainComparison.action_generator` identify the pure tensor `a ⊗ b`
  with multiplication by `a` on the first factor and `b` on the second in EVERY
  integer bidegree. the action-localization equation transports this action through precisely
  the given representative comparisons.
- The existential `balanced` is a natural transformation from `(res.prod res) ⋙ TF.tensor`
  to `TB.tensor ⋙ res`. `ChainComparison.chainBalanced` is a natural chain map on ALL complexes;
  `ChainComparison.balanced_generator` says it sends the sheafified generator `m ⊗_F n` in bidegree
  `(i,j)` to `m ⊗_B n` in that same bidegree. the balanced-localization equation specifies the
  induced derived map, with the canonical `sourceComparison` and `targetComparison`.
  The generators use the module-sheafification adjunction unit followed by the inverse
  of `tensorObjIsoSheafification`; this accounts for sheafification rather than
  pretending every section of a constant sheaf is globally constant.
- The asserted natural isomorphism is expressed by a split retraction:
  `splitting ≫ balanced = 𝟙 target` and
  `balanced ≫ splitting = action e`. This is exactly an isomorphism
  from the split image of the e-projector to the target, induced by `balanced`.
  On compatible representatives, the action-localization equation identifies that projector
  with the termwise chain action of e. In the abelian category of complexes the
  image of an idempotent is a direct summand; localization preserves its split maps.
  Therefore this is precisely the termwise e-summand described in the node, with
  no separately chosen abstract idempotent object and no arbitrary quotient map.
- Both transformations are on the product of the FULL derived categories, so
  naturality holds for all derived morphisms, not only chain maps. Neither variable
  has a boundedness or a finite-dimensionality assumption.
- The one-point-site case is included by taking the topology on the terminal category
  whose sheaves are ordinary modules. The node presents this as a specialization;
  no additional finiteness hypothesis or second construction is used for it.

Dependency declarations read and used:

- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, with fields and finite instances.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`, its
  sheafification-of-constant-presheaf definition; the actual constant-section map uses
  `CategoryTheory.sheafificationAdjunction`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, exactly
  Mathlib's module sheaves. Its full signature and docstring were read.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` and `DerivedCategory.Q`; the categories are unbounded localizations.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`:
  `SheafOfModules.site_derived_tensor_descent`, including the full representative,
  localization-equivalence, tensor-computation and natural-transformation clauses.
  Its source was also checked through `scompile.py --source`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, whose data leaves the underlying sheaf unchanged.
- The size-convention node is metatheoretic and has no declaration; explicit universes
  and localization infrastructure render it.
- All stated proof prerequisites are imported: the finite-field cardinal-power material,
  sheaf tensor/sheafification and bilinear extension interfaces, K-flat resolutions,
  the flatness module, and the underlying-set/sheafification and exactness material.
  Proof dependencies which are Mathlib leaves are imported through their defining modules.

Edge cases checked mathematically before writing:

- `F = B`: the annihilator and multiplication equations characterize the unit projector;
  the resulting quotient is the identity tensor comparison.
- Characteristic two and `card B = 2`: the product formula in the proof remains valid,
  including exponent `q - 1 = 1`; no division by `card B` is used.
- Zero complexes and the zero/degenerate sheaf category: the ring action on a zero object
  and the retraction identities still make sense and impose no nonzero hypothesis.
- Empty sites and topologies with empty covers: all generator equations are local
  statements; the module-sheafification unit and tensor presentations remain meaningful.
- Arbitrary positive and negative cochain degrees and infinite diagonals: the existing
  direct-sum totalization is used, with no boundedness restriction.
- Separate site object/morphism universes are preserved, including a site with objects
  in `t+1` and morphisms in `t`. Both coefficient fields may be placed in a common
  containing universe as stipulated by the size-convention node.

Searches made (all before introducing these declarations):

- `msearch.py ... leanfinder`: “For sheaves of vector spaces over finite fields restriction
  of derived tensor is the separability idempotent summand of derived tensor over the
  smaller field”. Eight results about LightCondensed monoidal structures/internal
  projectivity; no match for this arbitrary-site derived comparison.
- `msearch.py ... loogle`: `Algebra.FormallyUnramified.elem,
  CategoryTheory.Idempotents.Karoubi`. Zero hits.
- `msearch.py ... grep`: `derived.*tensor.*(summand|idempotent)|
  tensor.*derived.*(summand|idempotent)`. Zero Mathlib hits.
- `msearch.py ... leansearch`: “The tensor product over a finite separable field extension
  is the diagonal idempotent summand of the tensor over the base field”. Service returned
  Internal Server Error; recorded as unavailable, not as negative evidence.
- `rg` of Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` for derived tensor,
  diagonal idempotents and the item's id. Existing general derived tensor, scalar-action
  and ordinary formally-unramified algebra APIs do not state the item. The upstream
  item-id search has no hit. Full names in namespace `FiniteFieldDerivedTensor` have no
  existing declaration in any of these trees.

Sources read: the mirrored Stacks `algebra.tex`, lemma
`lemma-separable-algebraic-diagonal` (0C2X), and `sites-cohomology.tex`, definitions
`definition-K-flat` and `definition-derived-tor`, lemmas `lemma-K-flat-resolution` and
`lemma-derived-tor-quasi-isomorphism-other-side`. The algebraic tag is motivation;
it does not itself assert the derived comparison, as the node explicitly says.

No correction to the item's natural-language statement and no new definition nodes.
No STATEMENT-DISPUTED issue was found.

## Dependency modules

`lem-weil-pbc-site-derived-tensor-descent`: the recorded signature required
`C : Type u`, `Category.{u} C`, and coefficient rings of size u. It could not be
instantiated on the item's general small site with separate object and morphism sizes.
The delivered `Sheaf.Algebra.Homology.SiteDerivedTensorDescent` retains the same
localization equivalence, natural total-tensor comparison and transformation-extension
bijection, with `C : Type u`, `Category.{v} C`, and coefficients/modules of size `max u v`.
The flat-term clause is written directly as exactness of the canonical tensor-right
functor because the compiled specialized flatness API failed to infer that general site.
This is the node's flatness condition itself, not an additional assumption or new notion.
Only the dependency node's `lean` record changes. Its theorem remains `sorry`, with its
original six-step source-based proof plan. Every delivered file is compiled through
`scompile.py`; no library or global build is run and no delivery is pushed by this worker.

Validation: both full delivered modules compiled cleanly through `scompile.py`, with no
errors or warnings. The complete comparison file compiled in 41.5 s and 37.5 s in its
sandbox and library checks after replacing the oversized comparison record with the
equivalent existential proposition. The final dry run checks the final names and metadata.

## Second reading by NU

I read the item record in `dag/nodes/sec-smooth-purity/lem-pur-finite-field-derived-tensor-summand.json`, the source place named there (Stacks Project `algebra.tex`, Tag 0C2X, `lemma-separable-algebraic-diagonal`, finite-extension proof), and the signatures of every statement dependency.

The node's objects and clauses match the Lean as follows.

- The finite-field extension is rendered by `(F B : Type (max u v))`, `[Field F] [Field B] [Finite F] [Finite B] [Algebra F B]`; the balanced tensor algebra is `B ⊗[F] B` and its multiplication map is `Algebra.TensorProduct.lmul' F`. The existential `e` has exactly `e * e = e`, `Algebra.TensorProduct.lmul' F e = 1`, and `∀ b, (b ⊗ₜ[F] 1 - 1 ⊗ₜ[F] b) * e = 0`.
- An arbitrary site is `(C : Type u) [Category.{v} C]` with `J : GrothendieckTopology C`; `[HasSheafify J CommRingCat.{max u v}]` supplies the constant coefficient sheaves. The explicit `max u v` preserves independent object and morphism universes, and there is no `u = v` or other site restriction.
- `coefficients`, `rings`, and `Modules` are respectively the recorded `constantSheaf`, its canonical forgetful ring-sheaf composite, and `ringedSiteModules`; `Complexes` is unbounded `CochainComplex ... ℤ`; `Derived` is Mathlib's `DerivedCategory` with the two required `HasDerivedCategory` instances.
- `total` is the recorded monoidal `curriedTensor` extended by `map₂HomologicalComplex`, so it is the direct-sum total tensor with the signed differential. `representatives` says precisely K-flatness plus exactness of the canonical tensor-right functor in every integer degree, which is the node's K-flat/flat-term representative condition.
- `Presentation` packages the node's representative tensor comparison. The theorem asserts `Nonempty (Presentation J F)` and `Nonempty (Presentation J B)`, then quantifies over every `TF` and `TB`, so presentations cannot make the statement vacuous.
- `restrictComplex` is termwise `SheafOfModules.restrictScalars`. In `HasDiagonalComparison`, `res` is constrained by `restrictComplex ⋙ Q ≅ Q ⋙ res` on all complexes and `compatible` preserves the representative predicate.
- `action` is a ring homomorphism from `B ⊗[F] B` to endomorphisms of the full source bifunctor. `ChainComparison.chainAction` and `action_generator` specify the two coefficient actions on every pure generator in every integer bidegree. `balanced` is a natural transformation from the restricted F tensor to the restricted B tensor, with `chainBalanced` and `balanced_generator` specifying the canonical pure-tensor quotient in every bidegree.
- The two localization equations in `HasDiagonalComparison` transport those chain maps through the stated representative comparisons. The split identities `splitting ≫ balanced = 𝟙` and `balanced ≫ splitting = action e` identify the image of the termwise idempotent with the restricted B-derived tensor. The maps are transformations on the full product derived categories, hence natural in both derived variables and for all derived morphisms.
- The theorem's final existential and universal quantifiers have the same order as the node: first `e`, then its three algebraic clauses, then both presentation nonemptiness clauses, then `∀ TF TB`. No boundedness or finite-dimensionality condition on complexes or derived objects is introduced. The one-point site is included by the arbitrary-site quantification and no special case is assumed.

Edge cases checked: `F = B` gives the unit projector; characteristic two and `|B| = 2` are covered by the same equations; zero complexes and a degenerate/empty site impose no nonzero or nonempty assumption; all positive and negative cochain degrees and unbounded total diagonals are allowed; independent site universes, including object universe `t+1` and morphism universe `t`, remain available.

I searched the Mathlib tree, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, and the project `lean/Sheaf` for the item name and for derived-tensor/idempotent/summand variants. `msearch.py` LeanFinder returned only unrelated parser and underived algebra results; Loogle had no usable match; grep found no derived tensor summand declaration. Mathlib's `Algebra.FormallyUnramified.iff_exists_tensorProduct` was read and supplies only the underived annihilator/multiplication-one algebraic input, not this sheaf-derived comparison. No existing declaration duplicates the item or its helper notions.

The dependency `lem-weil-pbc-site-derived-tensor-descent` was read against its node. Its prior recorded interface required equal site object and morphism universes and therefore could not serve this arbitrary-site statement. The delivered `Sheaf.Algebra.Homology.SiteDerivedTensorDescent` module is the authorized §1(B) repair: it preserves the localization equivalence, total-tensor comparison, and natural-transformation extension clauses with `C : Type u`, `Category.{v} C`, and coefficient/module universe `max u v`; its flat-term condition is the same exactness condition used by `representatives`. No other dependency module or node was changed.

I found no mismatch with the item statement, no edge case excluded, no hollow definition, and no statement correction was needed. The two delivered modules compile cleanly with `scompile.py` and emit no errors or warnings.
