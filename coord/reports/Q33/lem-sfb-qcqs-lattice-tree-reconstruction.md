## Worker report

Stage 2, Q33, lem-sfb-qcqs-lattice-tree-reconstruction, repaired 2026-10-23.

The delivery states the complete item in
`Sheaf.Paper.QcqsLatticeTreeReconstruction`, declaration
`AlgebraicGeometry.ProEtale.LatticeTree.qcqs_lattice_tree_reconstruction`.
Its proof is `sorry`; it is the only postponed theorem in the delivery. Definitions
have real data. The statement, proof, proof dependencies and source of the item
are unchanged. The item gains the new tree definition and the already landed
local-freeness predicate as statement dependencies.

The theorem specializes the shared `Reconstruction` predicate twice. Its
parameters are an explicit way to state both coefficient cases without replacing
the coefficient inclusion by an arbitrary map: the theorem itself supplies the
canonical inclusion in each case. No assumption that this arbitrary generalized
predicate holds is used.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]`. |
| Fixed algebraic closure, finite subextensions | `PadicAlgCl ℓ`, and `PadicAlgCl.FiniteIntermediateField ℓ`, the existing subtype of intermediate fields with finite-dimensionality. Any chosen algebraic closure is represented by the fixed one up to its valued field isomorphism; no extra embedding is assumed. |
| Lambda is continuous E coefficients; family is {E} | First conjunct, `∀ E`, `R = Profinite.continuousMapRingObj E.1`, `I = Unit`, `F = fun _ ↦ E`. This gives exactly the singleton field family. |
| Lambda is finite-subextension-valued Omega coefficients; all finite F allowed | Second conjunct, `R = Profinite.padicAlgClRingObj ℓ`, `I = FiniteIntermediateField ℓ`, `F = id`. This is the recorded proper subsheaf of continuous Omega functions, not all continuous functions. |
| A_F is O_F with its norm topology | `Profinite.padicIntegersRingObj ℓ (F k).1`, defined using `PadicAlgCl.integers` and continuous maps with the subspace topology induced from the algebraic closure. |
| The actual maps A_F to Lambda | `padicIntegersRingObjToContinuousMapRingObj ℓ E` in the first conjunct; in the second this map followed by `Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F`. |
| Pulled-back coefficients on the small pro-etale site; module objects | `Modules R X` abbreviates precisely `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) (condensedRingObj R X)`. `coefficientMap a X` is the existing pullback of the point coefficient map. |
| Ordinary uncompleted unbounded derived categories | `DerivedCategory (Modules R X)` and the existing `Mod.extendScalars (...).leftDerivedFunctor`. `single R X M` is exactly `DerivedCategory.singleFunctor ... 0` applied to M. No completion or bounded-category substitute occurs. |
| qcqs root, qcqs vertices, finite rooted binary tree | `t : QcqsOpenClosedTree X`. Both constructors require `CompactSpace` and `QuasiSeparatedSpace` for their root; the children are themselves such trees. Inductive trees are finite. No vertex-count positivity excludes the one-vertex tree. |
| Locally closed subschemes, complementary quasi-compact open and closed children | Each split carries scheme morphisms j and i, `IsOpenImmersion j`, `IsClosedImmersion i`, `QuasiCompact j`, `QuasiCompact i`, and `Set.range j.base = (Set.range i.base)ᶜ`. Composites of these immersions are the locally closed vertex immersions; composites of quasi-compact edges are quasi-compact branch maps. This retains scheme structures, not just subsets. |
| e_W is the exact path composite | `p.extension R` recursively appends the actual `CondensedRing.openImmersionLowerShriek R j` or `CondensedRing.lowerStar R i`. `p.toRoot` is the actual composite scheme map; the root functor is the identity. The exactness is that of the existing edge interfaces. |
| Lambda flat over A_F at every vertex for every used field | The premise in `Reconstruction` is `∀ W, ∀ p : t.Path W, ∀ k : I, PreservesFiniteLimits (Mod.extendScalars (coefficientMap (a k) W))`. Extension is already right exact, so this is precisely flat scalar extension. It is imposed only at vertices, with no hypothesis on extraneous schemes. |
| Arbitrary Lambda-module M | `∀ M : Modules R X`; no constructibility, flatness, local freeness, or finite presentation is assumed of M. |
| One field, lisse lattice and scalar isomorphism on every leaf | `d : LeafModels ... t M`. `fieldIndex` can vary with the leaf; `model`, `lisse` and `scalarIso` are exactly the three supplied data. `lisse` is `IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ (F (fieldIndex w)).1) (model w)`, the predicate owned by `def-sfb-lisse-coefficient-module`: a pro-etale scheme cover on which the actual `CondensedRing.upperStar` pullbacks satisfy `Mod.IsFree`. |
| Zero models allowed, including empty leaves | No nonzero-rank or nonempty-scheme condition. The recorded `Mod.IsFree` allows rank 0. `Leaf t` includes paths to empty schemes. |
| J_W = e_W^(A_F) B_W | `branchModel d w` is exactly the path extension applied to `d.model w` using its own field `F (d.fieldIndex w)`. |
| J_W[0] belongs to D_ctf | `constantModelBoundedConstructible ... X (single ... (branchModel d w))` together with `DerivedCategory.finiteTorAmplitude ...`. These are the object predicates whose full subcategory is `ConstantModelConstructibleFiniteTor`. |
| Tor amplitude [0,0] | Separate conjunct `DerivedCategory.torAmplitudeIn _ 0 0 (single ... (branchModel d w))`, quantifying over all module sheaves as in the recorded definition. |
| Derived scalar extension of J_W[0] is e_W^Lambda(M restricted to W)[0] | The leafwise `Nonempty (... ≅ ...)` is an isomorphism in the ordinary derived category. Its left side uses the actual total left derived extension; its right side is the actual branch functor applied to the canonical `upperStar R p.toRoot` restriction, then the degree-zero functor. |
| More generally, path composites preserve finite scalar-model constructibility and flatness | `PreservesModelsAndFlat` for R, each A_F, and each continuous F coefficient. Constructibility uses `IsConstantModelConstructible`, not the weaker locally finitely presented notion. Tensor flatness is the existing `ObjectProperty.flat` in the module-object category: both tensor functors are exact. This is the internal-module rendition of the recorded `IsFlatOnSite` definition (exactness of the same sheafified balanced tensor), not a separate definition of flatness. |
| Scalar comparison is an isomorphism for every B | `∀ B, IsIso ((scalarComparison (a k) p).app B)`. `scalarComparison` recursively composes the canonical open scalar conjugate and closed scalar/direct-image mate. It is directed from Lambda tensor e(B) to e(Lambda tensor B); its inverse is the displayed comparison of the node. No flatness or local-freeness assumption is placed on B. |
| Finite distinguished-triangle extensions of the finitely many branch singles reconstruct M[0] | `∃ n, ObjectProperty.extensionProductIter P n (single R X M)` where P consists of objects isomorphic to a leaf branch single. The existing `extensionProduct` means a distinguished triangle with its first and third terms satisfying the two properties. The finite iteration is stronger information than mere membership in an arbitrary localizing closure, and exactly expresses the finite extension assertion. |
| Arbitrary Lambda-linear connecting maps, no common coefficient field | Extension products are formed in `DerivedCategory (Modules R X)` with all its morphisms. There is no scalar-field condition on any arrow, and the field may vary with each leaf. |
| Size convention | Explicit universe u, schemes in `Scheme.{u}`, pro-etale objects in universe u+1, abelian coefficients in `Ab.{u+1}`; the existing derived-category instances provide the ordinary enlarged localization. There is no equality between the site's object and morphism universes. |

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing` and its imported coefficient constructions;
  the present integral ring is the already published embedded-field condensed ring,
  so no finite quotient or alternate valuation ring is constructed.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClCondensedRing`, `padicAlgClRingObj`, `padicIntegersRingObj`;
  `...Condensed.FiniteSubextension`, `Profinite.padicSubfieldRingObjToPadicAlgCl`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint`; Mathlib's
  `CategoryTheory.Mod` in `Mathlib.CategoryTheory.Monoidal.Mod`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`, the existing total derived module
  operations and general `Functor.leftDerivedFunctor`; no new derived category.
- `Sheaf.Paper.CondensedConstantConstructibility`,
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`,
  `ConstantModelConstructibleFiniteTor`; imported `DerivedCategory.torAmplitudeIn`
  and `finiteTorAmplitude` from
  `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`.
- Mathlib `CompactSpace`, `QuasiSeparatedSpace`, and the equivalence
  `AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`; `QuasiCompact` in
  `...Morphisms.QuasiCompact`; `IsOpenImmersion` in `...OpenImmersion` and
  `IsClosedImmersion` in `...Morphisms.ClosedImmersion`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`,
  `Scheme.proEtale_ringed_open_closed`, its direct image and slice extension;
  the corresponding module-object edge functors are the recorded
  `CondensedRing.openImmersionLowerShriek` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` and
  `CondensedRing.lowerStar` / `upperStar` in `...UpperLowerStar.Defs`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`,
  `coefficientMap`, `CondensedRing.openImmersionShriekIso`,
  `CondensedRing.pushHom`; the canonical scalar map
  `padicIntegersRingObjToContinuousMapRingObj` from
  `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`,
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`, owned by
  `def-sfb-lisse-coefficient-module`. The actual definition uses a pro-etale scheme
  cover and `Mod.IsFree` on `CondensedRing.upperStar` pullbacks; the ranks may vary
  and may be zero. The unrelated pullback theorem is not a statement dependency.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`,
  `ObjectProperty.IsTriangulated`, `extensionProduct`, `extensionProductIter`.
  We use the finite extension predicate rather than falsely asserting that the
  finite extension closure is stable under all shifts.

All recorded proof-dependency modules are imported as plain `import` unless they
also supply the statement's objects. This includes the constructible-image lemmas
in `Mathlib.Topology.Constructible`; `cartesianCoefficients`;
`inverseImage_tensor_comparison`; open/closed detection; `IsFlatOnSite` and
`cochainModulesMonoidal`; `ringedSlice_extension_tensor`;
`closed_underived_projection`; `weaklyEtale_localization`;
`ringed_flat_single_tensor_cohomology`; `flat_single_scalar_conventions`; and
Mathlib's `ShortComplex.ShortExact.singleTriangle_distinguished`. Their source
signatures and docstrings were read. The theorem docstring gives all five proof
steps and their node citations. No proof import is dropped or closes a cycle.

Edge cases checked: empty root; empty open or closed child; zero/rank-zero model;
a one-vertex tree (root extension is identity, extension iteration may be zero);
mixed open/closed paths; repeated identical schemes at distinct vertices (paths
retain their positions); different finite fields at different leaves; arbitrary
nonconstructible M with only the stated leaf models; unbounded ambient derived
categories; non-Noetherian qcqs schemes and nonreduced closed subschemes. None is
excluded by a hypothesis. The identity case of scalar comparison is literally the
identity natural transformation. Complementary children cover and are disjoint
by the displayed range-complement equation; no reduced induced structure is forced.

Searches for the item's statement:

- LeanFinder, “Integral branch lattice models and reconstruction by finite
  distinguished triangle extensions on a finite qcqs open closed tree”: 8 results,
  all affine-transition limit/cover facts, no matching statement.
- Loogle, `CategoryTheory.ObjectProperty.extensionClosure,
  AlgebraicGeometry.ProEtale.IsConstantModelConstructible`: no hits; first name
  unknown. Read the actual Mathlib `extensionProduct` and `extensionProductIter`
  definitions directly instead.
- LeanSearch, “integral lattice branch models on a finite open closed tree
  reconstruction in the unbounded derived category”: 8 results, general derived
  category/localization declarations and an unrelated Z-lattice predicate; no match.
- msearch grep, `OpenClosedTree|lattice.*[Tt]ree|[Tt]ree.*[Rr]econstruct`: only
  Mathlib's abstract order-theoretic RootedTree instance.
- `rg -n` with the same expression in `lean/WeilConjectures` and `lean/Sheaf`, and
  a search for the exact item id in the upstream source: no existing statement.
  The DAG's refinement-tree existence theorems were read, including their Lean
  raw-array conclusion; they provide a refinement, not this reconstruction theorem.

No statement dispute, counterexample or statement correction was found.

Validation: both delivered files compiled individually through the prescribed
`scompile.py` wrapper in dependency order, in sandbox and library module modes.
The last clean run before packaging took about 3 seconds for the tree and 13 seconds
for the reconstruction module. No diagnostic commands or proved helper theorems
remain. The only theorem proof is the expected `sorry`.

## New nodes

`def-sfb-qcqs-open-closed-tree` introduces exactly the missing finite-tree packaging,
paths, their actual maps and their actual module-functor composites. Its module is
`Sheaf.Paper.QcqsOpenClosedTree`. The definition iterates the complementary open and
closed embeddings of Stacks Tag 09AH, which is also the item's own source. It uses
existing schemes, immersion properties, qcqs predicates, coefficient pullbacks,
module objects and both edge functors. No extension functor, coefficient ring,
constructibility predicate, derived tensor or flatness predicate is copied.

Three search kinds for this new notion are recorded verbatim in its
`mathlib_searches`: LeanSearch and LeanFinder for “finite rooted binary tree of
schemes with complementary quasi compact open and closed children”, and msearch
grep `OpenClosedTree|open.closed.tree|rooted binary tree` in Mathlib/AlgebraicGeometry.
The searches return generic covers, an abstract order tree, and constructible/affine
limit facts; none packages this scheme-valued notion. Source grep in WeilConjectures
and Sheaf found no declaration. DAG grep found the already read refinement-tree
existence theorems but no definition. `tools/blueprint_refs.py search 'open closed
tree'` returned zero matches; ancestor returned `det-sf-comp-coherence-cocycle`,
which is retained in the new node's ancestry. Both inductive constructors carry
actual data; all required proofs are constructor inputs and none is postponed.

## Second reading by Q33

This is the dispatched worker's second pass with the original node, both modules,
and dependency source signatures open. The independent review is the maintainer's,
as specified in this dispatch; no other agent was started.

I checked the complete matrix above against the expanded `Reconstruction` body,
not just the theorem's short wrapper. Both coefficient cases, their exact finite
field families and their exact inclusions match. I checked that the flatness
hypothesis is indexed by all vertices and all allowed fields, whereas the arbitrary
B in the scalar comparison has no flatness condition. I checked that every supplied
lattice is lisse, its coefficient field is leaf-dependent and its scalar
identification is with the restriction along that leaf's actual path map.

I then checked the four leaf conclusions separately: bounded scalar-model
constructibility, finite Tor amplitude, amplitude [0,0], and the ordinary derived
isomorphism. The general preservation clause covers the Lambda, integral and finite
field coefficient functors. The final finite extension product uses only the branch
objects and no shifts or coproduct closure; it leaves its distinguished-triangle
maps unrestricted in the Lambda-derived category. The usual associativity of
extension products converts the binary reconstruction into its finite-iteration
form without changing that assertion.

The new definition was checked for finite size, qcqs at every vertex, actual edge
morphisms, complementary ranges, quasi-compact branches, and one-vertex/empty cases.
Its paths retain vertices even when schemes coincide. Pattern matching was repaired
to expose all dependent indices and instance arguments; scalar comparison calls
were qualified as `Functor.whiskerLeft`/`Functor.whiskerRight`. These were elaboration
repairs only. No mathematical mismatch or item-statement change was required. The first preflight
requested separate bracketed citations for the open and closed immersion nodes in
the new definition; those citation delimiters were corrected.


## Returned delivery repair

The independent return of immutable head `a88b25593f19` identified H2/H4/H12:
the statement cited `lem-weil-pbc-continuous-locally-free-pullback` only to obtain
its plain `CondensedRing.LocallyFree` abbreviation. Its theorem conclusion was
unused. I replaced that import by
`Sheaf.Paper.CoefficientHeartStratificationDefs` and the `LeafModels.lisse` field
by the owning `IsLisseCoefficientModule` definition, exactly as requested. In the
item's `stmt_deps`, the theorem node is replaced by
`def-sfb-lisse-coefficient-module`. This is the dependency correction requested
by the return. No dependency theorem or duplicate lisse notion is introduced.

I read the definition node's complete statement, Lean record and declaration
signature/docstring. Its body is a pro-etale scheme cover whose actual pullbacks
are `Mod.IsFree`; it allows rank zero and rank variation, and adds neither
connectedness nor Noetherian hypotheses. Thus it states exactly the lisse leaf
hypothesis. The coefficient ring argument is the actual integral condensed ring,
with the site inferred from `model w`; no second coefficient pullback is passed.
I updated the hypothesis correspondence and dependency entry above. The remaining
clauses retain the canonical scalar maps, vertexwise flatness, Tor interval,
derived isomorphisms, scalar comparisons and finite extension products checked
in the return. The tree module and its new definition node are unchanged.

Before repair the saved packet passed the required initial dry run (commit
`4febbee7a52`). I compared its node with the current read clone: outside `lean`,
the only difference is its added statement dependencies. The delivered source
and report were retained; this repair changes only the identified import, lisse
field and owning dependency, and refreshes the item's Lean record date.


Repair validation: the prescribed `scompile.py` compiled both delivered modules
individually in dependency order with no errors or warnings. The tree's sandbox
compile took 4.4 seconds and the reconstruction sandbox compile 15.4 seconds;
the library-mode runs took 13.0 and 13.8 seconds. The repaired packet passed
`deliver2.py --no-push` as commit `2a686b55744`. The final self-check confirms the
stored theorem signature is verbatim, all Lean variables remain explicitly
bound with `autoImplicit false`, all Lean lines meet the 100-character limit,
and the only postponed theorem is the original reconstruction theorem. Compared
with current main, all item fields except `lean` and the authorized definition
statement dependencies are unchanged.
