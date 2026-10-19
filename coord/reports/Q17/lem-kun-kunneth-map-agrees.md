## Worker report

The main module is `Sheaf.AlgebraicGeometry.KunnethMapAgrees`. It states the integral
bounded-below and finite cyclic unbounded cases separately. All theorem proofs are `sorry`;
all helper definitions have actual data. The original item statement and dependency lists
are unchanged. There is no statement dispute or source correction.

The statement is written in `D(S_et, Λ)` before the evaluation equivalence explicitly
specified by the node. This retains the canonical maps, not just their object isomorphism
classes. For a separably closed field, evaluation at S is an exact monoidal equivalence
with modules, and therefore induces the stated derived equivalence. Under it `Rf(E)` is
`RΓ(X,E)`, `Rg(K)` is `RΓ(Y,K)`, and `Lg(Rf(E))` is the constant complex A. In particular
`PF_g(K,Rf(E))` becomes exactly the constant coefficient projection morphism r of the node.
The justification is the local-constant-label/counit calculation in node proof step 1.
The current upstream `Ordinary.lean` also documents this identification immediately before
`isIso_rightDerivedLowerStarProjectionMap_of_isSepClosed`.

Hypothesis and clause correspondence:

- Both theorems bind `{k : Type u} [Field k] [IsSepClosed k]`, with base `Spec (.of k)`.
- `f : X ⟶ Spec (.of k)` and `[IsProper f]` are exactly the named proper morphism.
  `g : Y ⟶ Spec (.of k)` supplies the arbitrary k-scheme, with no extra property in (a).
- `p`, `q`, and `sq : IsPullback p q f g` specify the fibre product, with an arbitrary
  chosen representative W rather than restricting its isomorphism class. We take
  `c = p ≫ f`; `sq.w.symm` is the equality `q ≫ g = c`.
- In (a), `[CompactSpace Y] [QuasiSeparatedSpace Y]` say exactly qcqs. The coefficient
  ring is `ULift.{u+1} ℤ`, the standard existing size convention for integer module
  sheaves, with its canonical ring equivalence to ℤ. `E` and `K` are objects of the
  full unbounded categories. `hE` and `hK`, each `∃ a : ℤ, DerivedCategory.IsGE _ a`,
  say exactly membership in D-plus under its full inclusion; no lower bound is fixed.
  `hEt : DerivedCategory.torsionCohomology ... X E` says every cohomology sheaf of E
  is torsion. K has no torsion hypothesis.
- In (b), `n : ℕ`, `hn : 0 < n` mean n at least one, and `hinv : IsUnit (n : k)`
  means invertibility in the field. Coefficients are `ULift.{u+1} (ZMod n)`.
  `[LocallyOfFiniteType g] [QuasiCompact g]` are the project's finite type convention.
  E and K have no boundedness or torsion-cohomology predicates.
- Every tensor is the existing `Etale.derivedTensor`, and every direct image is the
  existing full right-derived direct image. Their images under evaluation are the
  ordinary unbounded `rightDerivedGlobalSections` expressions of the node.
- F is `L((p)^*[ModuleCat Λ]).obj E` and T is its ordinary derived tensor with
  `L((q)^*[ModuleCat Λ]).obj K`. The canonical
  `leftDerivedUpperStarIsoMapDerivedCategory` identifies these with exact inverse image.
- `kunnethLerayExchange` is the recorded `exactDerivedBaseChangeMap` transported at
  its two ends by that precise canonical comparison. Thus it is the node's e.
- `kunnethLerayProjection` is exactly the recorded q-projection at F,K, hence t.
- `kunnethLerayConstantProjection` is the g-projection at K,Rf(E); the specified
  evaluation equivalence identifies it with `constantDerivedProjectionMap` at K,A.
  The definition does not choose any isomorphism or replace r by an arbitrary map.
- The Leray arrow is the inverse component of
  `rightDerivedLowerStarCompIsoOfComp ... q g c sq.w.symm`. This is the conjugate of
  the canonical left-adjoint composition comparison, hence the normalized composition
  comparison required by the node, not an unrelated isomorphism between these functors.
- The six successive factors of `kunnethLerayInverse` are precisely Leray,
  `Rg(inv t)`, `Rg((inv e) tensor 1)`, `Rg(sigma_{Lg A,K})`, `inv r`, and
  `sigma_{B,A}`. Both symmetries are components of the recorded
  `derivedTensorSymmetry`, including the signed complex symmetry.
- `KunnethLerayAgreement` existentially asserts `IsIso e`, `IsIso t`, `IsIso r`.
  These are conclusions, not hypotheses of either theorem. The proofs only allow
  the helper to form the inverses and carry no mathematical choices.
- Its next clauses assert `kunnethMap ≫ theta = 𝟙 _`, `theta ≫ kunnethMap = 𝟙 _`,
  and `IsIso kunnethMap`. The first is the displayed theta-after-kappa identity;
  the last two spell out “an isomorphism with inverse theta”. The Künneth map is
  the actual existing upstream adjunct of the two pulled-back counits.

The main module imports all already-recorded proof-dependency modules, including the
bounded-below and torsion projection formulas, finite cohomological dimension, derived
base change and normalized composition comparison. Dependencies without a recorded
module are not guessed. The canonical Künneth map and 0F0E now have landed records and are reused.
The existing delivered 0F0F module is reused as the dependency module below.

### Dependency declarations

| Node | Module and declaration used |
|---|---|
| `def-kun-separably-closed` | `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` |
| `def-weil-proper-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper` |
| `def-weil-scheme-over-base` | `Mathlib/AlgebraicGeometry/Over.lean`: `AlgebraicGeometry.Scheme.Over` |
| `def-pc-fibre-product` | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `CategoryTheory.Limits.pullback` |
| `def-weil-pbc-quasi-compact-scheme` | `Mathlib.Topology.Defs.Filter`: `CompactSpace` |
| `def-weil-quasi-separated-morphism` | `Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean`: `AlgebraicGeometry.QuasiSeparated` |
| `def-weil-pbc-torsion-etale-sheaf` | `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`: `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf` |
| `def-weil-pbc-derived-categories` | `Sheaf.AlgebraicGeometry.DerivedCategories`: `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology` |
| `def-weil-finite-type-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType` |
| `def-kun-derived-tensor` | `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `AlgebraicGeometry.Etale.derivedTensor` |
| `def-kun-rgamma-unbounded` | `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `AlgebraicGeometry.Etale.rightDerivedGlobalSections` |
| `lem-kun-tensor-sym` | `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`: `AlgebraicGeometry.Etale.derivedTensorSymmetry` |
| `def-kun-constant-sheaf` | `Mathlib.Algebra.Homology.Additive`: `CategoryTheory.Functor.mapHomologicalComplex` |
| `lem-kun-pullback-constant` | `Sheaf.AlgebraicGeometry.PullbackConstantModule`: `AlgebraicGeometry.Scheme.pullback_constantModule_isIso` |
| `def-kun-unbounded-exchange` | `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`: `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap` |
| `def-kun-projection-formula-map` | `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`: `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap` |
| `def-kun-constant-projection-morphism` | `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap`: `AlgebraicGeometry.Etale.constantDerivedProjectionMap` |
| `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` | `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`: `CategoryTheory.ringedToposDerivedPushforwardComposition` |
| `lem-kun-0f0f` | `Sheaf.AlgebraicGeometry.IntegralProperProjectionFormula`: `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_integral_of_isProper` |
| `thm-weil-pbc-bounded-below` | `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`: `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` |
| `lem-kun-0f0e` | `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormulaBoundedBelow`: `AlgebraicGeometry.Etale.isIso_constantDerivedProjectionMap_of_boundedBelow` |
| `lem-kun-0f0c` | `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN`: `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_modN` |
| `lem-kun-0f0g` | `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`: `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion` |
| `lem-kun-0f12` | `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula`: `AlgebraicGeometry.Etale.isIso_constantDerivedProjectionMap_of_finite_torsion_cd` |
| `def-kun-kunneth-map` | `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`: `AlgebraicGeometry.Etale.kunnethMap` |

### Edge cases and searches

Empty X or Y is allowed, and gives zero cohomology objects; no nonemptiness is assumed.
Zero E or K is allowed. In (a) the lower bounds can differ, can be negative, and can be
arbitrarily low; only E is required torsion. In (b), n=1 is included (the zero coefficient
ring), arbitrary unbounded inputs remain allowed, and n=0 is excluded exactly as in the
node. There is no accidental Noetherian, dimension, finite-rank, or uniform-bound
hypothesis. The scheme universe u and coefficient/module size u+1 are explicit and
follow the dependency interfaces; no equality of independent site universes is imposed.
The inverse has the right orientation in each of its six factors, and both symmetry
factors have their prescribed order.

Searches used the prescribed msearch wrapper. LeanFinder query
`compatibility Kunneth map Leray projection formula derived etale` returned only unrelated
Kähler and Dold–Kan declarations. Loogle queries `kunneth map projection formula` and
`IsIso, CategoryTheory.inv` returned unknown-identifier/no-match results, recorded in
`searches.jsonl`. Mathlib grep `kunneth|Kunneth` found no declaration. Direct rg in the
old source and `lean/Sheaf` for `kunnethMap_agrees`, the item id, bounded constant
projection, `0f0e`, and `0f0f` found no existing statement matching this item. The older attempt had supplied two bounded-below prerequisites;
the current DAG has the landed 0F0E theorem, so its duplicate has been removed. Reading the current shared upstream (and confirming
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` with `scompile.py --source`)
found the canonical `kunnethMap`, which is reused rather than redefined. Its
`kunnethMap_eq` is a different factorization, and `OrdinaryProper.nonempty_iso...` only
asserts existence of an object isomorphism in the finite case; neither states this
node's specific inverse in both cases. The main conclusion is therefore new.

Source statements were checked against the node and its full step-by-step proof and
Stacks 0F14, 0F0F, 0F0E; each theorem docstring carries the corresponding proof plan.

## Dependency modules

`lem-kun-0f0f`: the base DAG has no Lean record. A read-only server branch audit found
`deliver/Q17/lem-kun-0f0f`, whose module is
`Sheaf.AlgebraicGeometry.IntegralProperProjectionFormula`, with declaration
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_integral_of_isProper`.
The live `scompile.py --source` interface did not yet publish that module. This delivery
reuses its source and Lean signature, supplying it in the same delivery rather than
introducing a second statement. The only source adjustment is importing the now-landed
0F0E proof dependency. The node copy changes only `lean`, with a note explaining reuse.

Hypotheses match individually: `{X Y : Scheme.{u}}` and `f : X ⟶ Y` are arbitrary schemes
and the named morphism; `[IsProper f]` is properness. Both inputs are
`DerivedCategory.Plus` of module sheaves over `ULift ℤ`, exactly D-plus of abelian sheaves.
`hE : DerivedCategory.torsionCohomology ... E.obj` imposes torsion on E alone.
The two `TStructure.t.plus` conclusions put the actual source and target in the full
bounded-below subcategory. The final `IsIso` asserts invertibility of the recorded
`rightDerivedLowerStarProjectionMap` component. Full faithfulness identifies this with
invertibility in D-plus, including the canonical morphism. There is no qcqs assumption
on either X or Y. The five-step proof plan is present in the theorem docstring.
The stated proof-dependency modules are imported; unstated proof inputs are not invented.

No new definition node or mathematical statement correction is needed. The prior sandbox
copies of `def-kun-kunneth-map` and `lem-kun-0f0e` and their duplicate constant-projection
module have been removed because both dependencies now have usable landed declarations.

### Source and search refresh

The shared literature files named by the nodes are absent on this machine. The statements
and proof were checked against the full DAG text and the primary Stacks pages
[0F14](https://stacks.math.columbia.edu/tag/0F14),
[0F0F](https://stacks.math.columbia.edu/tag/0F0F), and
[0F0E](https://stacks.math.columbia.edu/tag/0F0E). No mathematical correction was needed.
The invertibility-of-n hypothesis of case (b) is retained from the node even though 0F14
works without it. Finite cohomological dimension here follows from finite type over the
separably closed field, as in the node, rather than requiring an additional bound.

The refreshed LeanFinder search `Kunneth exterior product agrees with Leray proper base
change and projection formula` returned eight LightCondensed/exterior-power results,
none concerning this canonical etale Künneth comparison. Loogle query
`CategoryTheory.Adjunction, CategoryTheory.inv` returned four generic adjunction inverse
identities, none stating the geometric comparison or its inverse. Mathlib grep
`kunneth|Kunneth|projection.*formula` in CategoryTheory returned zero hits. Direct `rg`
over the upstream source and shared `lean/Sheaf` for `kunnethMap_agrees`, `kunnethLeray`,
`KunnethLeray`, the item id, `0f0f`, and `boundedBelow_integral` found no duplicate main
statement. The server delivery-branch check found the 0F0F delivery reused above.
The current server sources for `Ordinary` and the landed bounded constant projection
were read with `scompile.py --source`, including signatures and docstrings.

### Validation

Both delivered modules were checked, separately in dependency order, using the prescribed
`scompile.py Q17 lem-kun-kunneth-map-agrees` wrapper. It returned exit code zero with no
compiler warnings or errors. The final per-file checks took 11.1 seconds for the reused
integral proper projection module and 37.6 seconds for the main module, below 60 seconds.
All helper definitions contain actual data; the three named theorem proofs are `sorry`.
The two node copies were compared with the shared DAG: only `lean` changes, and each
`lean.statement` matches its module's signature verbatim. The required `deliver2.py
--no-push` validation is the final packaging check; the independent second reader will
write the second-reading section and publish.

## Second reading by Q17

I am the independent second reader. I opened the complete current item and dependency
nodes, both sandbox modules, and the declarations below; I did not author the worker
statement. The shared blueprint Markdown and Stacks tree are absent. I read the imported
blueprint statement preserved in the DAG and the prior stage-1 source review, then fetched
upstream Stacks `etale-cohomology.tex` and `sites-cohomology.tex` into this item's
`scratchpad/sources/` only. I read `remark-define-kunneth-map` (0F1E),
`lemma-kunneth-one-proper` (0F14), `lemma-projection-formula-proper` (0F0F),
`lemma-pull-out-constant` (0F0E), `lemma-derived-pushforward-composition` (0D6E), and
`equation-projection-formula-map` (0B56). I also opened the primary Stacks pages for
0F0C, 0F0G, 0F10, and 0F12. Invertibility of n is in the blueprint and current node,
though the stronger Stacks 0F14(2) does not require it: retaining it is correct here.
There is no new mathematical statement correction in this delivery.

The following is my object/hypothesis/conclusion inventory and item-by-item match.
Every row passes; the precise map constructions, not just names, were inspected.

| Node object, hypothesis, or clause | Lean rendering and verdict |
|---|---|
| Separably closed field k and S = Spec k | Both theorems bind `{k : Type u} [Field k] [IsSepClosed k]`; the base is `Spec (.of k)`. Exact. |
| Proper structure map f of X; arbitrary structure map g of Y | `f : X ⟶ Spec (.of k)`, `g : Y ⟶ Spec (.of k)`, `[IsProper f]`. These are the explicitly named maps; no additional scheme-over instance is required. Exact. |
| W = X ×_S Y, projections p,q, c = fp = gq | Arbitrary `{W : Scheme.{u}}`, `p`, `q`, `sq : IsPullback p q f g`; `c` is `p ≫ f`, with `rfl` and `sq.w.symm` supplied to the canonical Kunneth and composition maps. `IsPullback` supplies exactly the universal property of the chosen fibre product. Exact, independent of its chosen representative. |
| Case (a): qcqs Y | `[CompactSpace Y] [QuasiSeparatedSpace Y]`. Read the CompactSpace leaf and the absolute quasi-separatedness equivalence, not relative separatedness of g. Exact. |
| Case (a): integer coefficients and D-plus inputs | `ULift.{u + 1} ℤ` uses the existing lifted-integer module convention. E,K are ambient derived objects and `hE`, `hK` are independently existential lower bounds via `DerivedCategory.IsGE`. Read `isGE_iff`: cohomology vanishes in degrees below the chosen integer. This is exactly the strictly full D-plus inclusion, with no fixed common bound. |
| Case (a): torsion cohomology of E only | `hEt : DerivedCategory.torsionCohomology ... X E`. Its opened definition forgets each homology module sheaf to an abelian sheaf and applies the recorded local torsion predicate. No torsion condition on K. Exact. |
| Case (b): positive integer invertible in k and cyclic coefficients | `n : ℕ`, `hn : 0 < n`, `hinv : IsUnit (n : k)`, coefficient ring `ULift.{u + 1} (ZMod n)`. Exact. |
| Case (b): finite type Y over k, arbitrary unbounded E,K | `[LocallyOfFiniteType g] [QuasiCompact g]` is the two-part recorded finite-type convention. E,K are unrestricted `DerivedCategoryModule` objects with no bound, constructibility, finite Tor dimension, or torsion-cohomology hypothesis. Exact. |
| Ordinary tensor, unbounded RΓ; A,B,F,T | Every tensor is the existing `derivedTensor`; every pushforward is the existing total right derived functor. In D(S_et,Λ), A and B are Rf(E) and Rg(K). The exact monoidal evaluation equivalence specified in the node sends them canonically to the unbounded RΓ(X,E), RΓ(Y,K), by Leray for sections. F is `L(p^*).obj E`, canonically exact inverse image, and T is `derivedTensor F (L(q^*).obj K)`. This is the node before applying its expressly stipulated equivalence. |
| Canonical signed symmetry | Both crossings use `derivedTensorSymmetry`. Its source module constructs the braiding by descent of the signed cochain braiding, rather than a choice from Nonempty. Exact, including shifted complexes. |
| e: g-inverse-image A → Rq F | `kunnethLerayExchange` composes the hom of `leftDerivedUpperStarIsoMapDerivedCategory` at g, the component of the recorded `exactDerivedBaseChangeMap`, and Rq of the inverse comparison at p. Directions agree. The opened comparison is the canonical exact-versus-left-derived identification, and the exchange is the recorded adjunction mate. |
| t: Rq F tensor K → Rq T | `kunnethLerayProjection` is precisely `rightDerivedLowerStarProjectionMap` for q at F,K. Read its defining adjunct: the tensor comparison followed by the q-counit tensor identity. Exact. |
| r: B tensor A → RΓ(Y,K tensor constant A) | `kunnethLerayConstantProjection` is PF_g at K,Rf(E). I checked `constantDerivedProjectionMap`, its normalized constant-sheaf tensor structure and derived constant/sections adjunction. Evaluation at S identifies the g-adjunction with this adjunction: maps from constants are maps of labels to sections. Their counits and tensor constraints are the same on labels and then on K-flat/K-injective models, as node step 1 requires. Thus this is the actual specified r before the equivalence, not an arbitrary map between equivalent objects. |
| Canonical Leray comparison ell | First factor of `kunnethLerayInverse` is the inverse component of `rightDerivedLowerStarCompIsoOfComp ... q g (p ≫ f) sq.w.symm`. Read the live upstream definition: conjugation of canonical left-adjoint composition under the derived adjunctions. Its inverse has direction Rc(T) → Rg(Rq(T)); this is the normalized comparison of 0D6E, compatible with the composite counit. |
| e,t,r are isomorphisms in either case | `KunnethLerayAgreement` existentially quantifies the three `IsIso` proofs. Neither case theorem assumes these instances. The helpers' instance parameters only allow inversion after the conclusion asserts their existence; they do not add a hypothesis to the item. Exact quantifier placement. |
| Six displayed factors of theta | In order: inverse composition comparison, Rg of inv t, Rg of `(derivedTensor.map (inv e)).app K`, Rg of symmetry at Lg(A),K, inv r, symmetry at B,A. Typed endpoints and orientations match each intermediate object of the display. There is no omitted sheaf-level symmetry. |
| theta after kappa is the identity; kappa is an iso with inverse theta | First conjunction is `kunnethMap ... ≫ kunnethLerayInverse ... = 𝟙 _`; Lean composition order gives exactly theta composed with kappa. Second conjunction is the other inverse equation and third is `IsIso kunnethMap`. The second spells out, without strengthening, the node's final inverse assertion. The Kunneth map is the existing live upstream adjunct of the two pulled-back counits with canonical composition and monoidality comparisons. Exact. |

Dependency and source checks: I opened `DerivedCategories`, `ExactUnboundedExchange`,
`EtaleDerivedTensorSymmetry`, `EtaleConstantProjectionMap`, `PullbackConstantModule`,
`ProperTorsionProjectionFormula`, `ProperUnboundedBaseChangeModN`, and
`EtaleConstantProjectionFormula`, and the upstream coefficient, tensor, upper/lower-star,
projection and global-sections declarations. I read the current `Ordinary` module using
`scompile.py --source`, including `kunnethMap`, `rightDerivedLowerStarCompIsoOfComp`,
its counit compatibility, the point equivalence, and the distinct `kunnethMap_eq`.
The comparison's conjugation formula and the point-equivalence documentation confirm
that the D(S_et,Λ) formulation preserves the specified maps. The Mathlib properness,
finite-type, fibre-product and boundedness declarations have the needed generality;
no extra coefficient/category instance leaks into either theorem.

There is one supplied dependency module and no new definition nodes. I independently
read `lem-kun-0f0f`, its five proof steps, its Stacks 0F0F source, and
`IntegralProperProjectionFormula.lean`. Its binders are arbitrary schemes, proper f,
bounded-below E,K, torsion only on E. Its two `t.plus` conclusions assert that the
actual source and target of the canonical projection belong to D-plus, and its IsIso
conclusion is invertibility of that exact map in the full ambient category. This is
precisely the node's isomorphism in the strictly full D-plus subcategory, not an extra
geometric restriction. Its docstring follows all five node steps. The dependency
record changes only `lean` and contains a note explaining reuse of the already
written delivery while its module is unavailable live. No private replacement
notion or missing helper is left.

Proof-plan/docstring check: the main integral docstring supplies node steps 1–5
(point equivalence/adjunction normalization, tensor/symmetry coherence, three
transposes, successive transpose, common-adjoint comparison), step 6 (integral
isomorphism inputs), and step 8 (inversion). The mod-n docstring reuses the shared
canonical calculation and supplies step 7 (torsion coefficients, unbounded proper
base change/projection, finite cd, constant projection) and step 8. Both case
statements and the dependency theorem have `sorry` proofs only. All five helper
definitions have real data; none chooses an undetermined object or arbitrary map.
The module and every declaration cite the source and correct blueprint id.
All Lean lines are at most 100 columns, no file-local notation/instance/private
abbreviation is introduced, and `u` and all variables are explicitly bound.

Independent edge checks: empty X, Y or W and zero E,K are allowed. There is no
Nonempty assumption. The point case X=Y=Spec k reduces to the canonical tensor
and the two inverse symmetries. Odd shifts retain the two Koszul signs; both are
supplied by the same signed braiding. Case (a) permits distinct and negative lower
bounds and imposes no uniform torsion exponent. Case (b) includes n=1 (zero ring)
and excludes n=0 exactly; the characteristic restriction is exactly IsUnit of n
in k. Empty/infinite indexing of complexes is not restricted. Scheme universe u
is arbitrary; sheaf/module universe u+1 follows the recorded small-etale-site
encoding and ULift of the two fixed coefficient rings, not a new site-universe
equality. No Noetherian, separated-Y, nonzero-ring or finite-rank premise is added.

Independent searches used different words from the worker's initial queries:
LeanFinder `derived external cup product inverse via proper exchange and two projection
morphisms` returned generic external-product composition and homological-complex
unitor/distributor lemmas; none asserts this comparison. Loogle
`CategoryTheory.Adjunction, CategoryTheory.NatIso` returned unknown identifier,
not a mathematical no-match. LeanSearch `Kunneth morphism equals projection formula
base change Leray composite` returned service unavailable (HTTP 500), so I record
no verdict for it. The msearch grep query `external product Leray cup product inverse`
returned zero. Direct rg over Mathlib external-product code, upstream Kunneth modules,
and the project's `lean/Sheaf` checked external-product, Leray and Kunneth vocabulary.
The Mathlib hits concern diagram external products; upstream `kunnethMap_eq` is the
different forward projection/tensor-base-change factorization, and the existing
finite-coefficient Kunneth isomorphism does not state this six-factor inverse or
integral case. No duplicate statement or alternative definition is needed.
Actual searches are appended to `searches.jsonl` by msearch.

Mismatches and changes: no mathematical mismatch found; no Lean or DAG statement was
rewritten. I appended this independent reading, source inventory, edge cases and
search results. The initial dry run correctly refused the as-yet absent section;
that packaging omission is now repaired. Both delivered modules were recompiled
through the prescribed scompile wrapper, exit 0, with no errors or warnings
(preliminary 7.9 s; actual library files 13.0 s and 23.4 s). I compared both node
copies with the shared DAG: only `lean` differs. I also mechanically checked that
each recorded `lean.statement` is verbatim the corresponding source signature.
The final dry run and delivery are run after this section is written.
