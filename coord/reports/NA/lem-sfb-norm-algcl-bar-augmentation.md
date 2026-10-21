## Worker report

The module `Sheaf.CategoryTheory.NormAlgclBarAugmentation` states
`Profinite.NormAlgclBar.norm_algcl_bar_augmentation` and constructs the specified
augmentation. This is stage 2. The earlier NC delivery was the stage-1 split:
the live node had no `lean` record. Its stage-1 merge therefore does not complete
this stage-2 assignment, and no stage-1 proof or statement has been replaced.

The source read was
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), together with all eight steps of this node's agent-formulated
formal/analytic expansion. The blueprint paragraph is contextual, not an external
proof of the noncomplete scalar input. The node's WANTED exact external reference
remains WANTED. No mathematical statement correction is made.

### Hypotheses and objects

| Node hypothesis or object | Lean rendering |
| --- | --- |
| A prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Algebraic closure Omega/Q_ell | `(Ω : Type u) [Algebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]` |
| Extended norm topology | `[NormedField Ω]` and `hΩ : ∀ a : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] Ω a‖ = ‖a‖` |
| Common universe convention | Explicit `universe u`; site `Profinite.{u}`, coefficient abelian groups in `u+1`, ordinary derived-category morphisms in `u+2` |
| A(S)=all continuous maps C(S,Omega) | Existing `continuousScalarRing Ω`, whose underlying sheaf is `continuousMapRingObjOfUniverse.{u,u} Ω` |
| H=additive Z_ell with its profinite topology | Existing `IndUnipotent.IntegerGroup.{u} ℓ = Multiplicative (ULift.{u} (PadicInt ℓ))` |
| Trivial action on A | `scalarModule Ω ℓ` is the existing `CondensedAction.trivial` applied to `Mod.regular (continuousScalarRing Ω).X`; every section action is the identity |
| Ordinary internal A-modules | `CondensedBar.Modules (continuousScalarRing Ω)` is the recorded Mathlib `Mod` category, not solid modules or topological modules |
| Ordinary derived category | `DerivedCategory` and `DerivedCategory.Q`, using `HasDerivedCategory.standard` |

`Assertion` existentially supplies the additive action category's abelian and
Grothendieck structures and a compatible `Model`, as the recorded derived-bar
theorem does. It then requires `ModelAssertion` for EVERY compatible model.
These structures are conclusions, not new hypotheses on Omega; model and
resolution existence are not hidden behind a vacuous universal quantifier.
The model definitions contain data; this module does not choose an object
from an undetermined existence theorem.

The two additions to `stmt_deps` are already landed definitions, allowed by
brief-stage2 section 5: `def-sfb-bundled-continuous-scalar-ring` owns the exact
scalar-ring bundle, and `def-sfb-ind-unipotent-system` owns the exact existing
lifted additive integer group. Only these helpers of the latter module are used;
no nilpotence, presentation, finite stage or ind-unipotent hypothesis is imposed.
No new node or dependency repair module is needed.

### Each clause of the statement

1. **The terms U_A^q and their evaluation.** The nonnegative source is
   `(cochains M.bar).obj (scalarModule Ω ℓ)`. Its q-th term is identified by
   `M.bar.term` with the ordinary `M.functions.functor (power H q)` applied
   to the regular module. `InternalFunctions.internalHom` identifies that
   functor with `Mod.ihom (freeParameter A (power H q))`. Here
   `freeParameter` is the existing free internal module A[H^q], not a copied
   or arbitrary free object. The first conjunct of `ModelAssertion` makes
   `evaluation ℓ Ω M.bar q S` bijective onto `C(S × power H q, Ω)` for every
   q and S. This actual map evaluates the recorded natural function family
   on the first projection and tautological second coordinate over S x H^q;
   its output is a section of the actual regular coefficient sheaf, hence
   an actual continuous Omega-valued function. Additivity, A(S)-linearity
   and restriction are inherited from `InternalFunctions.add`, `.smul`,
   `.restriction` and `.evaluate` (not postulated for an arbitrary map).
2. **The displayed inhomogeneous differential.** `cochains` is the existing
   `AlgebraicTopology.alternatingCofaceMapComplex` of `M.bar.diagram`.
   `BarDiagram.face` gives the first action face, consecutive multiplication,
   and last deletion, with signs (-1)^i from the alternating coface functor.
   In `IntegerGroup`, multiplication is addition of p-adic integers; in
   `scalarModule` the first action factor is the identity. Thus these are
   exactly the displayed deletion/addition formula on continuous functions.
   The second conjunct explicitly includes `d 0 1 = 0`. Both sides of the
   derived comparison use the recorded `extend`, extension by zero from
   natural to integer degrees, so every negative term vanishes.
3. **The derived-Hom total.** The target is
   `extend ((totalCochains M.bar).obj I.cocomplex)`. This is precisely the
   recorded compatible bar model: `M.computation.forgetInjectives` makes the
   forgotten resolution injective, and `M.computation.columns` identifies
   its columns with the second-variable derived internal Hom. Its double
   complex is `doubleComplex M.bar I.cocomplex`; the outer index is bar
   degree, and its finite total has differential d_bar+(-1)^q d_res. This
   reuses the dependency's model rather than substituting an underived total.
4. **The actual map j_A.** `augmentationComponent M.bar I q` is
   `((cochains M.bar).map (I.ι.f 0)).f q` followed by the coprojection into
   total summand (q,0). `augmentation` is the chain map with exactly those
   components. `derivedAugmentation` applies `extendMap` and then the
   ordinary localization Q to THIS map. It is not an arbitrary isomorphism
   between objects with the same cohomology.
5. **j_A is an isomorphism.** The third conjunct of `ModelAssertion` is
   `∀ I : InjectiveResolution (scalarModule Ω ℓ), IsIso (derivedAugmentation M.bar I)`.
   This is a morphism in the derived category, not only a per-degree assertion.
6. **Independence of compatible resolution choices.** The fourth conjunct
   quantifies I, J and EVERY chain map f satisfying `I.ι ≫ f = J.ι`.
   The total map induced by f is required to be invertible after localization,
   and the equation is `j_I ≫ Q(Tot(f)) = j_J`. These are the canonical
   comparison maps on the same recorded bar functor. All compatible bar
   models are quantified by `Assertion`, not chosen from an unspecified
   nonempty type. For two lifts the equation and invertibility of j_I also
   force their localized total maps to coincide. Existence of comparison
   lifts is the recorded injective-resolution API.
7. **Degree-zero augmentation is identity on A.** `M.invariants.inclusion`
   at the trivial scalar module is required to be invertible. This fixes its
   identification with A by its actual invariant inclusion. The source
   invariant augmentation `M.augmentation.map.app (scalarModule Ω ℓ)` is
   required to be invertible on H^0. The final square is the equation on H^0
   between this source augmentation followed by j, and
   `invariantResolutionAugmentation M.invariants I` followed by the target's
   independently normalized `M.totalAugmentation`. The former resolution
   map is obtained by applying invariants to I.ι and the canonical
   single-complex comparison; the latter total map has its components fixed
   by `TotalAugmentation.components`. Thus both identifications with A are
   fixed before j is compared. Their equality states the identity under
   those identifications, with no arbitrary choice of an H^0 isomorphism.
8. **No stronger analytic assertion.** No completeness, solidification,
   finite-subextension-valued replacement, acyclicity of individual Hom
   terms, or separately chosen comparison map appears among the hypotheses
   or conclusions. The proof docstring follows all eight node proof steps;
   its intermediate termwise route remains a future proof obligation from
   the separately stated noncomplete Cech input, not an added assumption.

### Definition data and postponed proofs

There are two named theorem holes, both listed in `lean.declarations` and
carrying this node's blueprint tag and a full natural-language proof:

* `augmentationComponent_comm`: the well-definedness of the actual canonical
  augmentation specified by the node. Its data are fully written in
  `augmentationComponent`. The differential commutation uses naturality of
  the bar functor and the chain-map equation for I.ι. This is the named
  proof used in the `augmentation` definition, not a hole in its data.
* `norm_algcl_bar_augmentation`: the main statement, with the eight-step
  proof carried by the node and rendered in its docstring.

All definitions have real data. Prop-valued `Assertion` and `ModelAssertion`
spell out the mathematical conditions; neither has a proof hole.

### Dependency declarations read and used

* `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`,
  `Mod.Hom`, `Mod.regular`, the module category recorded by
  `sk-def-sfb-module-objects`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`.
* `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`,
  `continuousMapRingObjOfUniverse` and its canonical monoid/commutativity
  data, read in full and reused through `continuousScalarRing`.
* `Sheaf.CategoryTheory.CondensedActionModule`:
  `Profinite.CondensedAction.ActionModule`, `Modules`, `trivial`,
  `Invariants`; the latter fixes its inclusion and adjunction on sections.
* `Sheaf.CategoryTheory.CondensedDerivedInvariantBar`:
  `CategoryTheory.CondensedBar.condensed_derived_invariant_bar`;
  its public dependency `CondensedEquivariantBarData` was read in full:
  `InternalFunctions`, `BarDiagram`, `freeParameter`, `cochains`,
  `doubleComplex`, `totalCochains`, `extend`, `Augmentation`,
  `TotalAugmentation`, `Computation`, `Model`, `Assertion`.
* `Sheaf.CategoryTheory.ContinuousScalarRing`:
  `Profinite.CondensedAction.continuousScalarRing`, the exact landed bundle.
* `Sheaf.Paper.IndUnipotentSystem`:
  `Profinite.CondensedAction.IndUnipotent.IntegerGroup` and
  `integerGroupDisconnected`, read with their original-topology docstrings.
* The size-convention node explicitly has no declaration; its metatheoretic
  convention is implemented by the explicit universe levels above.

Every available recorded proof-dependency module is imported with plain
`import`; statement interfaces are public. The noncomplete analytic Cech
node currently has no recorded Lean module, so there is no import to add
for it. It is needed for the future proof, not to type this statement.

### Edge cases and searches

Checked the empty profinite test set: its continuous-function group is zero;
free-generator evaluation and all restrictions include that test object.
H^0 is the singleton profinite parameter, and the two equal trivial-action
faces give d^0=0. The lift of Z_ell preserves its original compact Hausdorff
ultrametric topology. The additive zero in H is the multiplicative identity
of `IntegerGroup`, so adjacent multiplication implements addition with the
right identity convention. All resolutions and bar degrees are nonnegative;
extension by zero handles negative degrees, and total degree n has only the
finitely many pairs q+r=n. The statement allows every prime including 2.
No assumption of completeness or finite-valuedness of Omega-valued maps is
introduced. The source bound uses one common universe containing coefficients
and profinite parameters, as in the recorded bar and scalar interfaces.

Searches actually run:

* msearch leanfinder, `Canonical augmentation from underived continuous cochains to derived internal Hom bar totalization for algebraic closure of p adic field`:
  eight hits (BDeRhamPlus, BDeRham, PadicComplex and topological continuous
  cohomology constructions), no ordinary internal condensed augmentation.
* msearch loogle, `Condensed, IsIso`: zero hits with diagnostic
  `loogle: unknown identifier 'IsIso'`; not taken as a successful negative search.
* msearch grep, `bar.*(augmentation|Augmentation)|norm.*algcl`, subdirectory
  `Condensed`: zero hits.
* msearch leansearch, `Underived continuous scalar bar complex computes ordinary internal condensed derived Hom total for noncomplete algebraic closure p adic coefficients`:
  eight hits (PadicComplex, scalar-restriction continuity and a condensed-set
  adjunction), none states the requested actual derived augmentation.
* Source `rg`/`grep` for the exact node id, underived bar, bar augmentation,
  `resolutionAugmentation`, and `norm_algcl_bar_augmentation` in
  `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`:
  no exact existing declaration. Related hits were the derived-bar model,
  the finite-complete-field `NormedScalarProfiniteHomAcyclic` (not applicable
  as a theorem to Omega), and injective-resolution helpers. The existing
  internal-function, free-module and integer-group helpers were reused.

No STATEMENT-DISPUTED flag is raised: this delivery writes the exact node
statement, whose noncomplete analytic proof input and external reference are
explicitly outstanding in the DAG. The previous worker's blocker conflated
the stage-1 merge with stage-2 completion; the live `lean` field was absent.

Validation: the prescribed scompile wrapper compiled both its sandbox check
and the delivered module. One initial commutator argument omission and one
long docstring line were repaired; the final file has no line over 100 columns.
The required dry run and delivery are run after this report is written.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
