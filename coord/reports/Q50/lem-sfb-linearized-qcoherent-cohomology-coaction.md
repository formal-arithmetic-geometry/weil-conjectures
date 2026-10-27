## Worker report

The module `Sheaf.AlgebraicGeometry.LinearizedQcoherentCohomologyCoaction` states
`AlgebraicGeometry.LinearizedCohomology.exists_coaction`. Its proof alone is `sorry`.
All helpers are real constructions belonging to this node's canonical action and
comparison maps; no independent notion or postponed auxiliary theorem is introduced.
The statement, proof, and proof dependencies of the node are unchanged.

Hypothesis and conclusion correspondence:

- Field: `{k : Type u} [Field k]`.
- Group scheme: `G : Grp (Over (Spec (.of k)))`; affineness is
  `[IsAffine G.X.left]`; finite type is `[LocallyOfFiniteType G.X.hom]` and
  `[QuasiCompact G.X.hom]`.
- Scheme over k: `Y : Over (Spec (.of k)))`; quasi-compactness is
  `[CompactSpace Y.left]`; separatedness is `[IsSeparated Y.hom]`.
- Algebraic left action, with actual morphism equalities: `a : ModObj G.X Y`.
  Its `one_smul` and `mul_smul` are the identity and associativity diagrams.
- Quasi-coherent module: each `E : Y.left.Modules` with `hE : E.IsQuasicoherent`.
- Linearization: `D : GroupSchemeLinearization.Linearization a E`, the already
  recorded system of pullback isomorphisms on every test scheme. Evaluate it on
  the universal pair in G times Y to recover theta. Conversely pulling theta
  along every pair recovers this system. The unit, multiplication and naturality
  fields give equality of pulled-back sheaf maps; this is not a condition merely
  on field-valued points. `tensorComparison` is left-adjoint uniqueness for the
  SAME pushforward, so `tensorLift` transports the existing categorical pullback
  linearization into the REQUIRED explicit tensor-pullback model, preserving its
  normalized unit and composition comparisons. No new linearization is defined.
- Equivariant sheaf morphisms: `IsEquivariant a D D' f` is the commuting square of
  actual tensor-pulled-back sheaf maps on every test scheme.
- H^i with its k-vector-space structure: the EXISTING `scalarCohomology Y.hom E i`,
  whose carrier is `RingedSpace.moduleCohomology Y.left.toRingedSpace i` and whose
  scalar action restricts the global-function action along the structure map.
  Degrees are `i : ℕ`, exactly the stated nonnegative degrees.
- Coaction: the existential family `c E hE D i` has target H^i tensor k[G], where
  k[G] is exactly `Γ(G.X.left, ⊤)`. `HopfAction.Coassociative` and `Counital` are
  the existing right-comodule laws, with the canonical affine-group Hopf structure.
- Base change: `base Y A` is the actual fibre product, in the over category;
  `baseModule E A` is explicit tensor pullback by its first projection. `baseH`
  restricts the same right-derived global sections along A to Γ(Y_A,O).
  `beta A : A ⊗[k] H^i ≃ₗ[A] baseH E A i` is an A-linear isomorphism, for EVERY
  commutative k-algebra A, fixed by `beta A (b ⊗ₜ z) = b • p* z`. The pullback here
  is exactly the existing `moduleCohomologyPullback`. `@id` only names its target
  carrier to expose the A-module structure; it does not replace the map.
- Evaluation: the explicit composite `Spec.map x` followed by `isoSpec.inv`
  uses the affine Spec/global-function dictionary;
  all algebra-valued points are included, since G is affine. `evaluate` applies
  the coordinate algebra map to the coaction and flips tensor factors.
  `evaluatedAction` extends this by b tensor z mapping to b times its evaluation.
  The equality with `action a D A ...` is stated for EVERY class in A tensor H^i,
  not only for 1 tensor z.
- Cohomological action: `inverseTranslation` is (y,b) mapping to (g(b)^(-1)y,b).
  `actionCoefficient` composes canonical tensor-pullback comparisons with the
  inverse of theta_(g^(-1),y). The sheaf cocycle identifies this with
  theta_(g,g^(-1)y). `action` is the actual cohomology pullback along this morphism,
  followed by H^i of that coefficient map. No arbitrary action or comparison map
  is supplied as a hypothesis.
- Degree zero: `zeroSection` uses the canonical right-derived-zero isomorphism.
  `sectionAction` applies the actual pullback-unit sheaf map and the above q_g.
  Its value is precisely theta_(g,g^(-1)y)(s(g^(-1)y)); the theorem identifies it
  with the degree-zero cohomological action. This sheaf-map formulation retains
  nilpotents and applies on all test algebras, rather than testing residue values.
- Naturality: the third conjunction is the comodule identity for `map f i` for
  every equivariant map between linearized quasi-coherent modules.
- Short exact sequences and all LES arrows: the last conjunction quantifies an
  actual `ShortComplex`, its `ShortExact` proof, the three quasi-coherence proofs,
  three linearizations and the two commuting coefficient squares. It states the
  comodule identity for `boundary S hS i` in EVERY degree. `boundary` uses the
  existing `RingedSpace.moduleCohomologyBoundary`, with scalars restricted to k.
  The preceding naturality conjunction includes both fixed-degree maps induced
  by S.f and S.g, so together these cover every arrow of the existing LES.
  The derived-category binders quantify the usual size choices needed by the
  boundary API; there is a standard derived category at a sufficiently large
  universe for every scheme here. They add no geometric hypothesis and do not
  equate object and morphism universes.
- There is no properness, coherence, cohomology-dimension, smoothness or reductivity
  assumption. No characteristic or nonemptiness condition is imposed.

Dependencies read and used:

- Mathlib: `Field`; `CategoryTheory.GrpObj` and `Grp` from Monoidal.Grp;
  `ModObj` and its cartesian action from Monoidal.Cartesian.Mod; `Scheme`;
  `LocallyOfFiniteType`, `QuasiCompact`, `CompactSpace`, `IsSeparated` from their
  recorded modules; `SheafOfModules.IsQuasicoherent` from the public coherent
  dependency interface.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the existing quasi-coherence
  predicate is publicly exposed; its finite-type conjunction is NOT assumed.
- `Sheaf.AlgebraicGeometry.GroupSchemeLinearization`:
  `GroupSchemeLinearization.Linearization` and `act`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullbackSectionAdjunction`, `tensorPullbackSectionComp`, with the original
  `Scheme.Modules.tensorPullback` and `pushforward`.
- `Sheaf.AlgebraicGeometry.HopfCoactionLinearization`:
  `HopfAction.coordinateHopfAlgebra`; and its already public HopfActionModuleData:
  `HopfAction.Coassociative` and `Counital`.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`:
  `RationalHighestWeight.coordinateOverGroup` and `coordinateHopf`, exposing the
  given bundled group scheme to the canonical coordinate-Hopf API. No
  highest-weight or representation-finiteness property is assumed or used.
- `Mathlib.AlgebraicGeometry.Group.Affine`: the algebra-map `Spec.map` over k;
  `Scheme.isoSpec.inv` identifies the affine coordinate spectrum with G itself.
  The statement uses their explicit composite and no declaration of the
  rational-representation dictionary theorem module.
- `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`:
  `scalarCohomology`, `scalarCohomologyCarrier`, `scalarMap`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`:
  `moduleCohomologyPullback`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary`:
  `RingedSpace.moduleCohomologyBoundary`.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `sheafCohomologyAndHigherDirectImages`; this is the same recorded right-derived
  global-section cohomology and its LES, not Ext cohomology as a replacement.

The already stated proof dependencies are plain imports:
FlatCohomologySeparated (`H.baseChange_bijective_of_isSeparated`),
ModuleCohomologyExtPullbackComparison
(`exists_moduleCohomology_ext_pullback_comparison`), ModuleCohomologyFMapBasicProperties
(`moduleCohomologyFMap_basic_properties`), ModuleCohomologyFMapFunctorial
(the independence/composition/coefficient-naturality theorems),
FlatModulePullbackExact (`flat_module_pullback_exact_pushforward_injective`),
Mathlib's Flat and RingHom.Flat, and vector-space freeness. The proof dependency
`lem-sfb-module-cohomology-fmap-boundary` has no Lean record in the read DAG;
there is no module to import. It is a proof prerequisite only, not a missing
object in this statement. The canonical boundary definition is already recorded
and is used directly. The theorem docstring reproduces all eight proof steps.

Added statement dependencies are existing landed nodes for the declarations the
statement actually uses: `def-sfb-group-scheme-linearization`,
`def-sfb-coordinate-hopf-algebra`, `def-sfb-rational-highest-weight-data`,
`def-sc-field-linear-module-cohomology-operations`,
`def-sc-module-cohomology-boundary`, and
`def-sfb-hopf-action-module-data`. This is the explicit
§5 authorization to add existing landed statement dependencies. No other field
of the node changes besides `lean` and these added `stmt_deps`.

Edge cases checked before writing: A=0 is included with no Nontrivial assumption;
Y_A is empty and both sides vanish. Empty Y, zero coefficient sheaf, degree zero,
trivial G and the zero exact sequence all remain included. Infinite-dimensional
cohomology is allowed (algebraic tensors still have finite presentations).
Nonreduced G and nonreduced test algebras are retained by actual scheme maps and
test-scheme sheaf equalities. In the G_m character case, using theta_(g^(-1),y)^(-1)
gives the same sign as theta_(g,g^(-1)y), as required. No finite-dimensional
hypothesis enters. Test algebras, coefficient modules and schemes use the same u;
there is no smaller independent universe making universal tests vacuous.

Searches: msearch.py leanfinder, query "Cohomology of a linearized quasi coherent
sheaf has a rational coordinate algebra coaction": 8 hits on groupCohomology,
continuousCohomology and Sheaf.H, no exact result. Loogle query
`"Comodule", "cohomology"`: 0 hits. Mathlib grep
`lineariz.*cohomology|cohomology.*coaction|cohomology.*comodule`: 0 hits.
LeanSearch query "A linearized quasi coherent sheaf on a scheme with an affine
group scheme action induces a coordinate Hopf comodule on sheaf cohomology":
8 hits including IsQuasicoherent and QuasicoherentData, no exact result.
Project rg searches on lineariz/coaction/equivariant found the existing
GroupSchemeLinearization, RationalRepresentationComoduleDictionary,
HopfCoactionLinearization, RationalHighestWeightData, and the specialized PGL
section-ring result. These provide the reused notions, but none states the
cohomology coactions, arbitrary-algebra comparison and equivariant boundaries
of this item. Searching the node ID in WeilConjectures returned no occurrence.
Mathlib and both project roots were searched before choosing declaration names.

Source checked locally: coherent.tex `lemma-flat-base-change-cohomology`, Tag
02KH (both parts and the specified comparison in the proof), and the module
f-map/cohomology sources with their resolution-based map descriptions.
No STATEMENT-DISPUTED issue or source-based correction was found.

Validation: scompile.py compiled the full statement and its real-data helpers in
both sandbox module mode and library module mode with no errors or warnings.
The earlier expensive equality transport was repaired by applying `Over.Hom.left`
to the projection equality before applying the tensor-pullback object functor;
no timeout increase is present. The final import set is checked again by delivery.

## Second reading by Q50

Self-check against the node with the Lean file open; the maintainer's independent
review remains the independent reading, as specified by the dispatcher brief.
Checked all binders and all four main conjunctions. The original evaluation draft
only mentioned classes 1 tensor z; this was changed to `evaluatedAction` on every
class of A tensor H^i. The first draft's target scalar action was not inferable;
`@id (baseH E A i)` now explicitly supplies the existing A-module carrier without
changing the pullback. Checked inverse-translation order and the inverse theta
coefficient, canonical degree-zero normalization, both module-map squares,
and the boundary indices i and i+1. The theorem uses the explicit tensor pullback
through canonical adjoint comparisons, despite the reused linearization's
categorical pullback presentation. No extra geometric assumptions were added.
There are no new nodes or dependency-module replacements to review.
The returned F1/F2 ownership repairs are recorded below.


## Returned delivery repair: 967c938d4d59

F1: Removed `lem-sfb-rational-representation-comodule-dictionary` from `stmt_deps`
and removed its public module import. The only use was a plain definition for
an algebra-valued point. Following the reviewer's explicit second alternative,
the statement now writes that point as
`(Spec.map (CommRingCat.ofHom x.toRingHom)).asOver (Spec (.of k))` followed by
`G.X.left.isoSpec.inv.asOver (Spec (.of k))`. These are precisely the real-data
bodies of the former `coordinatePoint` and `genericPoint`, without a theorem
statement dependency or a new unowned helper. The actual point, evaluation
identity, universes and all mathematical clauses are unchanged. No dictionary
theorem was needed in the proof, so it has not been added to `proof_deps`.

F2: Added `def-sfb-hopf-action-module-data` to `stmt_deps`, and publicly imported
its recorded module `Sheaf.RingTheory.HopfActionModuleData` directly. Read its
`Coassociative` and `Counital` signatures and docstrings: they are exactly the
two right-comodule laws in `exists_coaction`. Their definition owner is now
explicitly present in the statement dependencies rather than only reachable
through another import.

Rebase comparison: the current shared main node has no Lean record and retains
the same mathematical statement, proof and original dependencies as the returned
sandbox. The repaired node starts from that current main record and reapplies
the corrected Lean record and added definition dependencies. No other node
fields or live files were edited. The return's independent mathematical review
accepted the Lean substance; this repair changes only the point expression to
its explicit body, imports, dependency ownership, and this report.
