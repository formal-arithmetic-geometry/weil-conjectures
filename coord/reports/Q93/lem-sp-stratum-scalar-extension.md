## Worker report

Repair of the delivery returned at immutable head `82d513216c7f`:
“H3: restore canonical module comparison and a natural complex-level tensor comparison,
including differential compatibility and naturality.” The initial retained-packet dry run
passed at `0b3e7d8400`, but the returned semantic defect was present, so this delivery
substantively changes the signature rather than re-pushing that packet.

`lean/Sheaf/Paper/StratumScalarExtension.lean` states
`AlgebraicGeometry.Scheme.stratumScalarExtension`. All definitions contain actual
constructions. Its only postponed proof is this named theorem's `sorry`; its docstring
records the six-step proof and sources.

Hypotheses and their exact rendering:

* Schemes `T`, `S` and the stratum inclusion: `i : S ⟶ T`, `[IsImmersion i]`, and
  `hi : Topology.IsConstructible (Set.range i)`. Mathlib's immersion is an embedding
  with locally closed image. No entire stratification, nonemptiness, or Noetherian
  hypothesis is required by this node.
* Finite commutative rings and a unital map: `(A B : Type u)`, `[CommRing A]`,
  `[CommRing B]`, `[Finite A]`, `[Finite B]`, `(α : A →+* B)`.
* The finite A-module: `(M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) [Finite M]`.
  This is the coefficient presentation used by the existing constant-module sheaf.
* The unbounded cochain complex `P` over the actual constant coefficient sheaf;
  `hP : CochainComplex.IsKFlat P`, and `hflat` asserting `IsFlatOnSite (P.X n)` for
  every integer n. Neither K-flatness nor flatness of the terms has been omitted.
* The unbounded derived object `K`; `hK` states, for every integer q, local constancy
  of the pullback of `homologyFunctor ... q` and finiteness of every geometric module
  stalk. Thus its restricted cohomology is finite locally constant, with no boundedness
  or local freeness hypothesis.

Conclusions, in the order of the node:

* `IsIso (proEtaleCoefficientInverseImageMap i A)` concerns the specified adjoint of
  the constant-section ring map, not an arbitrarily selected coefficient identification.
* The existential module isomorphism `e` identifies precisely
  `proEtaleConstantModulePullback i A (proEtaleConstantModuleSheaf T A M)` with the
  same constant module on S. Its adjunct under `proEtaleConstantRingAdjunction A i`
  sends `stratumConstantModuleSection T A M U m` to
  `stratumConstantModuleSection S A M ((proEtaleBaseChange i).op.obj U) m`.
  This equation at every U and m characterizes the canonical comparison: the source
  constant-module sheaf is sheafified from those constant sections, so its map to
  direct image is determined by them, and adjunction determines the original map.
  The isomorphism is a morphism of module sheaves, so addition, negation, zero and
  the A_S-action are preserved. An arbitrary module-sheaf isomorphism is insufficient
  and is no longer the statement.
* The next conclusions assert K-flatness and flatness of every term of the termwise
  functor `proEtaleConstantRingPullback A i` applied to P.
* The tensor clause gives one family `β` of B_S-module isomorphisms, indexed by all
  A_T-module sheaves N, between pullback of their sheafified scalar extension and
  scalar extension of their pullback. The naturality equation quantifies over every
  module morphism `f : N ⟶ N'` and uses the actual `changeOfRingsHom` and
  `proEtaleConstantModulePullbackMap` on the two sides. A second equation fixes the
  canonical map: its B-adjunct sends the scalar-extension unit `1 ⊗ m` to `1 ⊗`
  the A-pullback adjunction unit of m. These units generate the extension and pullback,
  so scalar automorphisms cannot replace the comparison.
* The same tensor clause supplies a family `e Q` of actual cochain-complex
  isomorphisms for every complex Q, with `(e Q).hom.f n = (β (Q.X n)).hom`.
  Its source and target use the existing `changeOfRingsComplex` (including its actual
  changed differentials) and `mapHomologicalComplex`. Thus the `comm'` field of the
  chain map is differential compatibility, not just independent termwise existence.
  Naturality for a cochain map f in degree n is exactly the displayed β-naturality
  equation specialized to `f.f n`; all the components of `e Q` are fixed by β.
  Consequently this is a single natural comparison at complex level, including at P.
  The source proof step 4 explicitly establishes this module-natural construction
  without any flatness hypothesis on B or on the input module; K-flatness and flat
  terms are used in the separate preservation conclusion.
* For every integer q the last clause identifies `homologyFunctor ... q` of
  `proEtaleConstantRingDerivedPullback A i K` with `proEtaleConstantRingPullback A i`
  of the original cohomology object. The coefficient categories on both sides are the
  ordinary intrinsic module-sheaf categories already recorded by the project.

The three helper definitions belong to this node's comparison construction:
`proEtaleConstantRingMap` applies the constant-sheaf functor to `RingHom.ulift α`;
`stratumConstantModuleSection` applies `toSheafify` to the underlying constant
module presheaf; `stratumScalarExtensionUnitSection` applies the existing module
sheafification adjunction unit to the pure tensor `1 ⊗ m`. None chooses arbitrary
data or introduces a replacement module, tensor, inverse image, or site.

Dependency interfaces used (module, declarations):

* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction` reexports the recorded
  inverse-image interface, including `proEtaleBaseChange`, `proEtaleConstantRing`,
  `proEtaleCoefficientInverseImageMap`, `proEtaleConstantModulePullback`, and its map.
* `Sheaf.AlgebraicGeometry.ProEtaleOperations`: `proEtaleRingModules` and the
  underlying ringed-site module operations.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `proEtaleConstantRingPullback`, `proEtaleConstantRingAdjunction` (with its uniquely
  normalized model-site transpose), and `proEtaleConstantRingDerivedPullback`.
* `Sheaf.Paper.ProEtaleLocallyConstantSheaf`: `proEtaleConstantModulePresheaf`,
  `proEtaleConstantModuleSheaf`, `IsLocallyConstantProEtaleModuleSheaf`.
* `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`: `proEtaleGeometricModuleStalk`.
* `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality` reexports the
  recorded tensor interface, including `changeOfRings`, `changeOfRingsHom`, and
  `changeOfRingsPresheaf` from `TensorProduct`.
* `Sheaf.Algebra.Homology.ChangeOfRingsComplex`: `SheafOfModules.changeOfRingsComplex`,
  the already landed node `def-pur-change-of-rings-complex`, added to `stmt_deps`
  under brief-stage2 §5 (landed notions may be added). Its real terms are
  `changeOfRings` and its differentials are `changeOfRingsHom` of the differentials.
* `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`; Mathlib's `constantSheaf`, `toSheafify` and
  `PresheafOfModules.sheafificationAdjunction` provide the actual units.

Edge cases checked: empty T or empty S, M=0, the zero coefficient ring or B=0,
identity immersion, α the identity, the non-flat finite map Z/4 → Z/2, and unbounded
complexes. On the empty site the canonical section equations remain meaningful and
unique; no section or tensor generator is required to be nonzero. The B_S-linearity
of β is in the type of its morphisms. The comparison has no flatness assumption on α.
The termwise equations use every integer degree and every module map, so they cover
zero differentials, arbitrary differentials and arbitrary cochain maps uniformly.

Searches retained from the original packet: `msearch.py leanfinder` for constant-module
pullback and scalar-extension comparison found only generic pullback/coherence results;
`msearch.py loogle "SheafOfModules.pullback"` found generic pullback functors;
`msearch.py grep "constant.*sheaf|pullback.*tensor"` found only generic site/constant-sheaf
files. The repaired packet additionally ran:

* `msearch.py leanfinder "canonical inverse image constant module sheaf comparison sends
  constant sections to themselves and natural tensor comparison of cochain complexes"`:
  eight generic free-module and unit-Hom-equivalence hits, no exact comparison.
* `msearch.py loogle "SheafOfModules.pullbackObjFreeIso, HomologicalComplex.isoOfComponents"`:
  zero hits (unknown `HomologicalComplex.isoOfComponents`).
* `msearch.py grep "constant.*[Mm]odule|changeOfRingsComplex" Algebra/Category/ModuleCat`:
  zero Mathlib hits. Local `rg` finds the existing project `ChangeOfRingsComplex`, which
  is reused, not reconstructed.
* `rg` for all four declared names and the item id in the named upstream, shared Sheaf,
  and Mathlib trees: no existing declaration of these names or the complete statement.
  Further searches for module constant-comparison maps found only other-site or
  fixed-coefficient interfaces, not this normalized intrinsic comparison.

No natural-language statement correction, dependency repair module, new DAG node, or
STATEMENT-DISPUTED flag is needed. Only the item's Lean record and the additional
landed statement dependency change in its JSON. The saved/current node agreed outside
`lean` before that authorized dependency addition; the delivery wrapper refreshes its
base against current newtargets-dag.

## Second reading by Q93

Self-check in the dispatcher's no-subagents workflow, with the node, full signature,
recorded dependency sources and source proof paragraph (2) open. The prior head retained
the earlier immersion/constructible-image repair but omitted the canonical normalization
of the module isomorphism and provided only `∀ n, Nonempty (...)` for tensor comparison.
The return is correct. The new constant-section adjunct equation fixes the module map;
the tensor-unit adjunct equation fixes β, its equation for every module morphism is
naturality, and the family `e Q` consists of actual complex isomorphisms with the β
components. Chain-map compatibility and naturality for cochain maps follow with precisely
the changed differentials in the imported `changeOfRingsComplex`, not differentials
chosen by an existence claim. No arbitrary scalar automorphism satisfies the specified
unit normalization. No assumption on B-flatness or boundedness was introduced.

I rechecked every original hypothesis and all six conclusions against the node as
listed above. The new helper data are composed entirely from existing functors, maps
and units. Universe arguments on change-of-rings operations are explicit: the small
site still has object universe u+1 and morphism universe u, and module/ring coefficients
live in u+1. The first compile diagnostic exposed unresolved universe inference; explicit
arguments repaired it, without raising the 60-second limit or identifying site universes.
The final module compiles both as sandbox and library path with no diagnostics (about
four seconds each). The theorem signature is copied verbatim into `lean.statement`, all
four declarations are listed, and all source lines are at most 100 characters.
