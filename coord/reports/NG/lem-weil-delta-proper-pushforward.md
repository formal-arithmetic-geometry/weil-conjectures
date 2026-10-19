## Worker report

`Sheaf.Paper.DeltaProperPushforward` states
`AlgebraicGeometry.Etale.proper_ambient_double_dual_compatibility` with `sorry`.
The node's statement, dependency lists, and proof are unchanged. The other declarations
in this module supply actual formulas for the canonical arrows in this statement; all
are definitions with real data, and none selects an arbitrary isomorphism from a
`Nonempty` theorem. The only other postponed theorem in the delivery is Q29's unchanged
pairing dependency, described below.

Hypotheses and clauses, in the node's order:

- A field is `{k : Type u} [Field k]`. Its schemes are `X Y : Scheme.{u}`.
  We name the structure map `aY : Y ⟶ Spec (.of k)` and use `f ≫ aY` as the
  structure map of X. This is the usual presentation of a morphism over k; it
  retains every morphism of k-schemes by substituting its commuting structure map.
- Properness of `f : X ⟶ Y` is `[IsProper f]`, the recorded Mathlib definition.
- Y is separated and finite type over k by `[IsSeparated aY]`,
  `[LocallyOfFiniteType aY]`, `[QuasiCompact aY]`. X is separated and finite type
  over k because f is proper and these properties are stable under composition.
  Consequently no extra Noetherian or compactification hypotheses occur in the
  theorem. Nagata supplies the compactifications used in its expression.
- Finite commutative coefficients are `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`;
  invertibility on the field is the established convention
  `[HasInvertibleExponent Λ (Spec (.of k))]`. Neither nonzero coefficients nor a
  positive-characteristic exclusion is added.
- The ambient categories are `DerivedCategoryModule Λ X` and
  `DerivedCategoryModule Λ Y`, exactly the recorded coefficient-valued ordinary
  small-etale derived categories. K ranges over the whole unbounded category.
- The dualizing objects are the existing `dualizingComplex (ModuleCat Λ) aY`
  and `dualizingComplex (ModuleCat Λ) (f ≫ aY)`. Their source definition is the
  ambient right adjoint `rightDerivedUpperShriek` of ordinary compact support,
  evaluated at the coefficient unit, not a constructible exceptional functor.
- The duals are the existing `verdierDual (ModuleCat Λ) aY` and its analogue for
  X. Its body is `derivedHom.flip.obj (dualizingComplex ...)`, hence precisely
  RHom(-, omega). The recorded general ringed-site internal Hom module is imported;
  the existing etale tensor-Hom adjunction supplies its specialized closed-category
  presentation. No second internal Hom, tensor, coefficient category or site is defined.
- The canonical delta in the statement is `ambientDoubleDualMap`. This is a
  real construction from `derivedTensorHomAdjunction.homEquiv`, applied to
  `ambientDualEvaluation`. Evaluation is signed symmetry followed by the inverse
  transpose of the identity. These are the exact normalization equations of
  `Etale.AmbientDualityPairing` in the dependency module. The use of left tensor
  explains the factor ordering: evaluation is DK tensor K, and its transpose with
  left tensor DK is K to DDK. The signed symmetry is the already recorded
  `derivedTensorSymmetry`, not a new symmetry.
- The ambient exchange is `properAmbientVerdierExchangeMap`, oriented F DX to
  DY F, the inverse orientation to the textual isomorphism. It is explicitly the
  tensor-Hom transpose of `symmetry ≫ mu ≫ F(evaluation) ≫ trace`.
  `ambientDirectImageProduct` defines mu by the recorded direct-image projection
  map followed by F of tensoring the ordinary inverse-image counit. Thus it is
  exactly the product map in the node's proof, with no assumption on K.
- The trace is `properAmbientDualityTrace`. `properAmbientShriekStarIso` compares
  chosen compact support with direct image through the proper model `(id_X,f)`.
  It uses the existing compactification comparison, the proper/open comparison,
  the exact-functor/right-derived identification, and direct-image composition.
  `ambientShriekCompIso` exposes the existing explicit unbounded composition
  construction using `rightDerivedLowerShriekOfCompactificationCompIso` and
  `rightDerivedLowerShriekIso`. It never chooses from the upstream existential
  composition statement and never invokes the bounded-below composition functor.
  `properAmbientDualizingIso` takes the right-adjoint mate of this precise
  composition after proper coincidence. The trace transports the actual counit
  by that mate. Every stage is a functor, isomorphism or adjunction already present
  in the existing framework, assembled with its stated normalization.
- `ProperAmbientDoubleDualCompatibility` first states naturality of theta:
  F(DX h) followed by theta_K equals theta_L followed by DY(F h).
  Its second conjunct gives `IsIso (properAmbientVerdierExchangeMap ... K)`
  for every K. Together these give the ambient exchange of functors.
- Its third conjunct is exactly
  `F(delta_K) ≫ theta_(DX K) = delta_(F K) ≫ DY(theta_K)`.
  Both sides land in DY(F(DX K)). Since the exchange is invertible, composing
  with the inverse of DY(theta_K) is equivalent to the node's double-dual
  comparison carrying F(delta_K) to delta_(FK). This form does not require
  either delta to be invertible just to state the square.
- The final conjunct is `IsIso delta_(FK) → IsIso (F.map delta_K)` for every K.
  It asserts precisely invertibility of the pushed-forward arrow, without
  asserting that F reflects isomorphisms.
- No binder or predicate restricts to bounded, constructible, perfect or
  dualizable complexes. Geometric biduality and constructible exceptional-adjoint
  admissibility are absent. The theorem's only proof is `sorry`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from its imported morphism module. These render the geometric
  hypotheses without changing their meaning.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, the ordinary module-derived category.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification` and `rightDerivedLowerShriek`.
  The former is the recorded def-amb-etale-compact-support. The ordinary ambient
  adjunction is the recorded theorem in
  `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`, with upstream
  `rightDerivedUpperShriekAdjunction` and the finite-coefficient left-adjoint
  instance from `...Derived.UpperShriek`. `...Derived.Dualizing` defines the
  actual dualizing complex and Verdier functor used here.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, the recorded general model.
  The specialized adjunction and Hom used in the arrows are
  `Etale.derivedHom`, `derivedTensorHomAdjunction` from upstream `...Derived.Hom`.
- `Sheaf.Paper.DualityPairing`: `CategoryTheory.dualityDoubleFunctor`,
  `Etale.AmbientDualityPairing`, and `Etale.ambient_duality_pairing`. The actual
  arrows now have explicit formulas meeting exactly that dependency's normalization.
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`:
  `Etale.derivedTensorSymmetry`, the canonical descended Koszul symmetry.
- Upstream `...Derived.LowerStarProjection`:
  `Etale.rightDerivedLowerStarProjectionMap`; `...Derived.UpperLowerStar`:
  `derivedUpperStarLowerStarAdjunction`, `rightDerivedLowerStarComp`,
  `rightDerivedLowerStarCongr`. Their full signatures and adjunction docstrings
  were read to fix the map orientations and the ordinary counit.
- Upstream `...Derived.LowerShriekIndependenceUnbounded`:
  `rightDerivedLowerShriekIso`; `...Derived.LowerShriekComposition`:
  `rightDerivedLowerShriekOfCompactificationCompIso`. The bodies of the existing
  existential composition and proper coincidence statements were read; the helpers
  expose their explicit constructions, not a choice from their `Nonempty` results.
- Upstream `...Derived.TensorHom`:
  `Etale.derivedHomRightDerivedLowerShriekIsoOfFinite`, the recorded
  prop-asd-internal-adjunction, was read through `scompile.py --source` because
  the older local source lacks that recently added wrapper. The theorem's proof
  identifies the explicitly defined pairing transpose with this canonical mate.
- Stated proof dependencies are imported directly: `ProperProjectionFormula`,
  `CompactifiableOverField`, `RingedInternalHomExactRestriction`,
  `RhomGlobalSections`, `UpperStarMonoidal.Comparison`, and Mathlib `Noetherian`.
  The unrecorded auxiliary lem-sf-unbounded-compact-support-proper-composition has
  no importable module. Its actual canonical composition construction is already
  available upstream and is the expression assembled by `ambientShriekCompIso`;
  no new postponed theorem for this proof-only prerequisite is introduced.

Edge cases checked mathematically and in the types: K=0, the empty X or Y, f=id,
zero coefficients, characteristic zero and positive characteristic with invertible
coefficient exponent, and arbitrary unbounded K. All arrows are defined in these
cases. There is no lower or upper cohomological bound, nonempty scheme condition,
or constructibility condition. The double-dual arrows need not be invertible.
The isomorphism implication concerns F(delta), not delta on X. A proper morphism
with empty source is therefore included, as it must be.

Searches actually made:

- `msearch.py ... leanfinder` query “Proper pushforward of etale complexes commutes
  with Verdier double dual evaluation”: eight hits, mostly underived sheaf
  pushforward comparisons. None states the complete item.
- `msearch.py ... loogle 'CategoryTheory.MonoidalClosed, CategoryTheory.ihom'`:
  twelve hits concerning generic closed-category internal Hom and subcategories;
  these do not state proper etale double-dual compatibility.
- `msearch.py ... loogle 'CategoryTheory.MonoidalClosed.curry'`: twelve hits,
  including currying, its inverse laws and naturality. These supply ingredients,
  not the target statement. The source Basic.lean was opened to read the types.
- `msearch.py ... grep 'toIhomIhom|doubleDual|bidual'`: sixteen hits, additive
  characters and analytic double duals; none on the relevant etale derived categories.
- `msearch.py ... grep 'curry|ev_naturality' CategoryTheory/Monoidal/Closed`:
  twenty-five generic currying/evaluation hits; no complete matching theorem.
- `msearch.py ... leansearch` query “Proper etale direct image commutes with the
  canonical double dual evaluation morphism on arbitrary complexes”: service
  unavailable (Internal Server Error), recorded as unavailable, not absence.
- Direct `rg` in upstream WeilConjectures for bidual/doubleDual/duality and proper
  exchange found `Derived.Dualizing`, `Derived.TensorHom`, and constructible
  biduality. Their full definitions and relevant signatures/docstrings were read.
  Upstream's constructible existential biduality theorem is not this statement.
- Direct `rg` of upstream for the exact item id returned no hit. Direct `rg`
  of `lean/Sheaf` found no complete proper double-dual statement. The upstream
  declaration index and both source trees have no collision with any new name.
- The dependency's Q29 delivery was found in the second-reader/review records;
  its exact source and report were read. Server source probes for plausible
  AlgebraicGeometry modules and then the actual `Sheaf.Paper.DualityPairing`
  returned “Module source unavailable”. Its delivered source is reused below.

The blueprint source file was read in the launcher's literature mirror. The proof
docstring retains all seven expanded DAG steps, including unbounded composition,
canonical mate normalization, the two transposes, signed symmetry and the final
arrow-specific implication. No statement correction or dispute was needed.

Validation uses only `scompile.py`, with every delivered module compiled separately
in dependency order, in both sandbox and library views. The definitions and initial
statement compiled cleanly under the unchanged 60-second per-file limit. The final
naturality clause and direct proof imports are checked by the delivery dry run.
No `#check`, private declaration, file-local notation or auto-bound implicit remains.

## Dependency modules

`lem-weil-duality-pairing`: the shared node has no `lean` record, but Q29 already
provided `Sheaf.Paper.DualityPairing` in delivery `3db0236f2367`, reviewed PASS.
The current server source is still unavailable. This delivery reuses Q29's exact
unchanged module and node lean record, with `by: NG` and an explanatory `lean.note`;
no other dependency node field changes. The module packages evaluation and delta
by their exact adjunction normalizations, coherent shifts, and the full morphism
of distinguished triangles, and includes the pro-etale clause. Its five declarations
and the whole source/report were read. No independent alternate pairing interface
is substituted. The second reader may omit this duplicate delivery file/node if Q29
has landed by then; the main module imports that same module name in either case.

## Second reading by NG

I read the item record, its blueprint source place (order 2123), every recorded
statement dependency, the worker's Lean module, and the supporting node
`lem-sf-unbounded-compact-support-proper-composition`. The source statement is
unchanged and the Lean signature is checked against it clause by clause:

- The field is `{k : Type u} [Field k]`; the coefficient is
  `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` with
  `[HasInvertibleExponent Λ (Spec (.of k))]`. The theorem binds these exactly in
  `proper_ambient_double_dual_compatibility` (lines 285--290). No nonzero,
  characteristic, or boundedness assumption is added.
- `X Y : Scheme.{u}`, `f : X ⟶ Y`, and the structure map
  `aY : Y ⟶ Spec (.of k)` are the theorem binders. `[IsProper f]`,
  `[IsSeparated aY]`, `[LocallyOfFiniteType aY]`, and `[QuasiCompact aY]`
  render properness and separated finite type over the field. The source's
  structure map for X is `f ≫ aY`, as used throughout the helper definitions.
  Properness supplies the corresponding finite-type/separated facts for X;
  there is no extra Noetherian, compactification, or commutation hypothesis.
- The ambient categories are `DerivedCategoryModule Λ X` and
  `DerivedCategoryModule Λ Y`, using the recorded ordinary small-etale
  coefficient category. `K` is unrestricted and unbounded.
- The dualizing objects are
  `dualizingComplex (ModuleCat.{u + 1} Λ) aY` and the same expression at
  `f ≫ aY`; the dual functors are the recorded
  `verdierDual (ModuleCat.{u + 1} Λ)`. Thus the Lean objects render
  `ω_T = Ra_T^× A` and `D_T = RHom_A(-,ω_T)` rather than an exceptional
  constructible or geometric-duality object.
- Evaluation and the double-dual arrow are the real constructions
  `ambientDualEvaluation` and `ambientDoubleDualMap` (lines 69--83), using the
  existing signed `derivedTensorSymmetry` and tensor--Hom adjunction. No
  arbitrary isomorphism or `Nonempty` choice is used.
- The ambient exchange is the explicitly defined
  `properAmbientVerdierExchangeMap` (lines 192--211), oriented
  `F(D_X K) ⟶ D_Y(F K)`, with its trace from
  `properAmbientDualityTrace`. The product map is the canonical projection
  formula followed by the inverse-image counit. The helper composition and
  proper/open comparisons are unbounded and canonical constructions.
- `ProperAmbientDoubleDualCompatibility` (lines 219--249) has exactly the
  source conclusion: naturality of the exchange, invertibility of that exchange
  for every K, the square carrying `F.map δ_K` to `δ_(F K)`, and finally
  `IsIso (δ_(F K)) → IsIso (F.map δ_K)`. The square is well typed with target
  `D_Y(F(D_X K))`; it does not assert either delta is invertible and does not
  claim that F reflects isomorphisms. The theorem concludes this predicate with
  no additional clause.

I opened the dependency declarations rather than matching names heuristically:
`IsProper`, `LocallyOfFiniteType`, and `QuasiCompact` are the Mathlib morphism
classes; `DerivedCategoryModule`, `dualizingComplex`, `verdierDual`, and the
ordinary lower-star/lower-shriek derived functors are the recorded upstream
objects; `ambient_duality_pairing` is the Q29 pairing interface reused by this
module. The supporting node is already in the shared base and remains an
unsplit statement-only proof dependency, with its own source tags 0F7H--0F7J and 0F7B.
Its hypotheses, all-unbounded domain, proper normalization, refinement
coherence, and composition isomorphism were checked against those tags; it does
not duplicate a bounded-below composition node.

Edge cases were checked in the definitions and signature: `K = 0`, identity f,
empty X or Y, the zero coefficient ring, characteristic zero or positive
characteristic subject only to invertible exponent, arbitrary shifts (with the
signed symmetry), and arbitrary unbounded K. No index set or integer n occurs,
so no empty-index or `n = 0` case is silently excluded. The constructions still
have their unique zero/empty-category maps, and no constructibility, perfectness,
Tor-amplitude, nonempty-scheme, or cohomological bound is imposed.

Searches were repeated with `msearch.py NG lem-weil-delta-proper-pushforward`
using LeanFinder, Loogle, and grep queries for proper pushforward, Verdier
biduality, `doubleDual`, `ambientDoubleDualMap`, and tensor--Hom currying in
both the upstream source and project `lean/Sheaf`. The only matches were generic
closed-category/currying declarations, underived pushforward formulas, and the
existing dualizing/tensor-Hom ingredients; no complete theorem or duplicate
notion exists. LeanSearch was unavailable (Internal Server Error), recorded as
unavailable rather than treated as a match. The exact source blueprint and
relevant Stacks tags were read before accepting the unchanged statement.

No statement mismatch was found, so no `statement_change` or citer audit is
needed. No Lean statement repair was necessary. The initially copied supporting node
was unchanged from the shared base and was removed from the sandbox as redundant. I compiled both delivered modules separately
with the required wrapper; the successful combined command was:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NG lem-weil-delta-proper-pushforward lean/Sheaf/Paper/DualityPairing.lean lean/Sheaf/Paper/DeltaProperPushforward.lean`.
It completed the preliminary pairing, sandbox files, and library files with no
errors or warnings beyond the permitted `sorry` declaration.


Concurrent-landing repair: the first dry run passed at f7000c4f03, but the
final preflight found that Q29's exact `DualityPairing.lean` had landed while
validation ran. I opened the landed source and checked its evaluation and delta
normalization equations again. I removed the duplicate dependency module and
node from the sandbox; the main module now imports the landed Q29 module.
The earlier worker dependency section describes the state when it was written.
The supporting composition node is already in the base, has no delivered
Lean module, and is used only by the proof plan; it is not a missing statement
object. No mathematical statement or source definition was changed.

Second-reader search details: my fresh LeanFinder query was “A symmetric direct
image functor with dualizing trace preserves evaluation into the second Verdier
dual”. It returned eight generic triangulated, rigid-duality or finite-module
pairing hits; these require different objects/hypotheses and do not state this
item. My fresh Loogle query `CategoryTheory.MonoidalClosed.curry_natural_left`
returned that one generic currying naturality theorem. I read Closed/Basic.lean
lines 145--190 and the full derived Hom and dualizing signatures upstream.
Direct `rg` searches covered Mathlib category theory, upstream six-functor
modules and project Paper modules. The upstream existential constructible
biduality statement and existential Verdier/direct-image comparison were opened;
neither asserts the canonical delta square on arbitrary K. The prior report's
search list includes the first worker's searches; these two queries and the
direct source searches are the independent second-reader searches.

Documentation repair: the module had source and construction explanations but
no main-declarations list, required by brief-stage2 §3. I added the list; every
definition and theorem signature and body is unchanged. The theorem signature
was mechanically compared with `lean.statement` and is verbatim equal. All
variables/universes are explicitly bound, and all Lean lines are at most 100
characters. The only delivered postponed theorem is
`proper_ambient_double_dual_compatibility`, whose docstring retains all seven
DAG proof steps. No new definition node, dependency repair, proof, or target
statement change is delivered.
