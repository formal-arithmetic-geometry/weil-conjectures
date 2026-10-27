## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantCoherentTorCalculus` states
`AlgebraicGeometry.SchemeTor.equivariant_coherent_tor_calculus`. Its single postponed
proof has the complete eleven-step natural-language argument in its docstring.
The definitions have actual data, including the derived tensor, its Tor maps,
its signed derived connecting maps, and the K-flat resolution comparison.

The theorem concludes the existence of comparison data; none of the comparison
records is an extra hypothesis. `Space F` is a finite-type scheme over Spec F,
using `LocallyOfFiniteType` and `QuasiCompact`. `[Field F]` is the field hypothesis.
`[GrpObj G.val]`, `[IsAffine G.val.left]`, and `[ModObj G.val X.val]` express the
finite-type affine group scheme and its action, with unit and associativity.
The existing `EquivariantCoherent.Coherent D` is the full category of coherent
modules with action-groupoid descent isomorphism; its unit and cocycle use the
recorded section-normalized pullback compositors. The supplied `ActionGroupoidModel`
fixes composition on test schemes by the multiplication coordinate.

Clause-by-clause correspondence:

- `tensor P M` is the tensor of the two degree-zero objects in the published
  K-flat derived monoidal category; `obj q P M` is its homology in degree `-q`.
  The quantifier `q : ℕ` includes zero. No surrogate tensor is defined.
- `FlatCalculus.coherent` asserts coherence. `ActionCalculus.tor`, `realization`,
  and `linearization_formula` give the linearized realization and pin its
  linearization to beta for the action, Tor of the input linearizations, and
  inverse beta for the projection. `maps` realizes the actual derived Tor maps.
- `boundaryRight` and `boundaryLeft` use the actual signed tensor triangles and
  `DerivedCategory.HomologySequence.δ`. `ExactCalculus.boundary_right` and
  `boundary_left` lift them to equivariant maps. `exact` covers all three
  adjacent pairs in each variable and the epimorphic degree-zero endpoint.
  `zero` identifies degree zero with ordinary sheaf tensor.
- `HasCoherentKernelImage`, `map_subobjects`, and the two boundary fields give
  coherent linearized kernels and images, with inclusions identified with the
  actual abelian kernel and image inclusions.
- `FlatCalculus.affine` is the affine sections identification with the recorded
  `CategoryTheory.Tor'`, and `affine_naturality` gives its naturality in both
  variables. `ringResolutionIso` is the actual Mathlib augmented projective
  resolution comparison. `ResolutionCalculus`, `resolutionIso`, and
  `resolutionHomologyIso` give the finite-free sheafified resolution calculation;
  only positive cochain degrees vanish, so infinite resolution length is allowed.
- `beta`, `beta_naturality`, `beta_id`, and `beta_comp` state flat pullback
  comparison, naturality, identity, and composition using the section-normalized
  pullback compositors. `EquivariantFlatCalculus` states equivariance for every
  equivariant flat morphism and supplied realizations of its pulled-back inputs.
  Both `beta_boundary` fields express compatibility with the connecting maps.
- `AffineBaseChangeCalculus` pins the comparison to augmentation-preserving
  resolution lifts: on a cycle represented by `e tensor m`, the tensor lift is
  `c(e) tensor pullSection(m)`, and an exterior coefficient `b` multiplies the
  resulting class. This is the displayed flat base-change formula and includes
  affine restrictions. The same formula applies to action, projection, and
  any flat face map. `actionFlat` and `projectionFlat` do not assume smoothness
  or reducedness and do not assert flatness of the unit section.
- `EquivariantAlgebra` uses the existing `MonObj` algebra structure and requires
  equivariance of multiplication and unit. `AlgebraCalculus.action` supplies the
  existing `ModObj` structure on Tor; `normalization` pins it to coefficient
  multiplication on resolution cycles. `equivariant`, `maps_linear`, and
  `boundary_linear` give compatibility and P-linearity. `killed` says every
  section killing P kills Tor, hence applies to every invariant coherent ideal
  J and P = O/J without selecting an arbitrary quotient presentation.
- `LocallyFreeCalculus.exactTensor` uses `IsFiniteLocallyFree`, allowing varying
  finite local ranks. Its `tensor` field states the equivariant isomorphism and
  pins it on cycles to the actual termwise associator `reassociate`.
  `flat_input` asserts degree-zero ordinary tensor and vanishing for all `q > 0`.
  On these Noetherian schemes finite locally free modules are coherent, so the
  coherent carrier for V imposes no additional condition.

Dependency interfaces read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  `AlgebraicGeometry.schemeDerivedTensorMonoidal` and
  `schemeModule_hasFunctorialFlatResolution`.
- `Mathlib.CategoryTheory.Monoidal.Tor`: `CategoryTheory.Tor'`.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` and `.Mod`:
  `CategoryTheory.GrpObj` and `CategoryTheory.ModObj`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.RingedSpace.IsCoherent` and the associated quasi-coherent
  finite-type predicates.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullbackSectionAdjunction`, `tensorPullbackSectionId`,
  `tensorPullbackSectionComp`, and `tensorPullbackSection`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and the
  upstream tensor structure: the actual sheaf and cochain tensors.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and
  `Flat.comp`; `.FiniteType`: the finite-type predicate.
- `Sheaf.AlgebraicGeometry.EquivariantCoherentGZero`: `ActionGroupoidModel`,
  `Coherent`, `underlying`, `linearization`, `underlyingMap`, `moduleTensor`,
  `moduleTensorMap`, `tensorComparison`, `IsTensor`, and `IsPullbackMap`.
  This existing interface uses `Scheme.GroupoidModule`, not a private copy.
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`:
  `DerivedCategory.QObjTensorSingleFunctorObjIso`; Mathlib's
  `ProjectiveResolution.isoLeftDerivedObj` supplies the affine resolution map.

Edge cases checked: q = 0 and q > 0 are separated; rank zero and varying local
ranks are allowed; resolution length is not assumed finite; empty affine opens
are included; schemes need not be separated; the group need not be smooth or
reduced; the action's unit section is never assumed flat; identity pullback and
composition use the actual canonical compositors; flat comparison naturality
also covers nonequivariant input maps. There is no statement correction and no
claim that the unit is flat.

Searches actually run: msearch LeanFinder query "equivariant coherent Tor sheaves
flat base change group scheme linearization" returned Rep.Tor and unrelated
monoidal/condensed results, not this statement. Loogle "Tor, GroupScheme"
returned no hits (unknown identifier Tor). msearch grep
"Linearization|linearization|SheafTor" found representation linearization and
unrelated matches. LeanSearch "Tor sheaf derived tensor cohomology coherent"
returned Tor, Tor', their object/map formulas, and Rep.Tor, with no sheaf-level
calculus. Searches in Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` found no
existing exact declaration. Related `EquivariantTorLinearization` treats a
closed-immersion Tor comparison, not the general bifunctor calculus.
`blueprint_refs.py search "Tor sheaves"` and DAG keyword searches found no
existing general sheaf Tor definition for this item; the displayed Tor
construction is a helper of this node, whose statement itself introduces it.
The Stacks source was read in `cohomology.tex`, definition-tor and the ensuing
long exact sequence, and `algebra.tex`, lemma-flat-base-change-tor.

## Second reading by Q75

A separate sequential rereading was performed by this worker: the dispatcher
explicitly forbids starting other agents. The audit checked every quantifier
against the node and all formulas against the recorded declarations. It caught
and removed an unnecessary hypothesis of flatness of a composite (the existing
`Flat.comp` instance supplies it), repaired the sheaf tensor additivity instance,
and kept the actual K-flat comparison and signed derived boundaries. No theorem
is proved in this stage; all helper definitions are constructed in full.

## New nodes

`def-sfb-scheme-tor` defines the missing general scheme Tor construction in
`Sheaf.AlgebraicGeometry.SchemeTor`. Source: Stacks 08BP, definition-tor and its
ensuing exact sequence; 06YH for the K-flat comparison; Algebra 00LY for the
projective-resolution comparison. The LeanSearch, LeanFinder, Mathlib grep,
source-repository grep and Sheaf grep searches above found ring Tor and a
closed-immersion specialization, but no general scheme Tor construction with
the actual signed derived boundaries. The blueprint search found no duplicate.
The module defines actual data, not a substitute tensor or arbitrary comparison.
The item imports it and adds its id to stmt_deps. Splitting this construction into
its own definition node keeps each single-file compile within the server limit.
All references above to construction helpers now refer to this owning module;
all comparison/calculus records remain helpers of the item module. The sequential
second reading also checked the new node against every declaration of SchemeTor.
The item's `faceFlat` covers the three face maps of composable action arrows,
and `EquivariantPullbacks` explicitly supplies the coherent equivariant pullbacks
used by the comparison. `EquivariantFlatCalculus` includes invertibility of that
specific comparison, not just its equivariance square.

`def-sfb-equivariant-tor-calculus-data` packages the normalized comparison and
exact-sequence data, without asserting their existence. It owns `Space`, `Coh`,
`FlatCalculus`, `ActionCalculus`, `ExactCalculus`, `ResolutionCalculus`,
`EquivariantPullbacks`, `EquivariantFlatCalculus`, `AffineBaseChangeCalculus`,
`IsTensorComparison`, and `LocallyFreeCalculus` in
`Sheaf.AlgebraicGeometry.EquivariantTorCalculusData`. The final item imports this
module and supplies the algebra-action data and the existence theorem. This is
an explicit record presentation of all the node's clauses, not an assumption of
them. Its source and searches are the same actual sources and searches above;
no existing declaration packages this normalized scheme-equivariant calculus.
The second reading checked that all these records are conclusion data and that
the existence theorem quantifies over them, so no conclusion became a hypothesis.
The definitions of `Space` and `Coh` are indexing subtypes of the existing
finite-type and coherence notions, not alternate notions of scheme or coherence.

The final reading tied the two explicit tensor realization isomorphisms `eN`
and `eK` to their actual linearization squares, instead of merely asserting that
some tensor realization exists. Thus the cycle-normalized comparison and the
claimed equivariant comparison use the same realizations.
