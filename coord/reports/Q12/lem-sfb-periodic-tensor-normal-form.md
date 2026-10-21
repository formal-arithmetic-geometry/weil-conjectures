## Worker report

The module `Sheaf.Paper.PeriodicTensorNormalForm` states
`SheafOfModules.periodic_tensor_normal_form`; its only postponed proof is this named theorem.
The three real-data helpers construct the prescribed zero-differential normal form,
its nonpositive term identification, and its induced map. The repair adds a definition-node ownership record for the already landed scalar-periodic
construction; no dependency module or mathematical statement correction is introduced.

Source read: blueprint main-20261015,
`sec-proetale-coefficients/sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.proof.md`,
“The examples,” especially the infinite periodic resolution and Tor in every nonnegative degree.
The item's seven proof steps supply the explicit sheaf-level generalization and are reproduced
in the theorem docstring. Stacks 03EK supplies sheafified tensor and 06YU its K-flat interpretation,
through the recorded dependency declarations.

Hypotheses and objects, clause by clause:

- The site is `C : Type u`, `Category.{v} C`, and `J : GrothendieckTopology C`.
  `EssentiallySmall.{r} C` is the relative smallness needed for the module universe;
  it covers small sites, with independent object and morphism universes. There is no
  equality of the site universes. The ring sheaf is `R : Sheaf J CommRingCat.{r}`.
  `HasDerivedCategory.{w} (Modules R)` selects the localization/morphism universe,
  as required by the recorded abstract-derived-category interface. It imposes no
  additional algebraic property; the standard localization is always available.
- `t : (unit ...).sections` is the restriction-compatible family of ring sections.
  `unit` has the ring's own sections as its underlying module; `t.val U` is `t_U`.
  `ht : ∀ U, t_U * t_U = 0` is precisely the square-zero hypothesis. The `@id`
  annotations are type ascriptions, not chosen lifts or changed elements.
- `Modules R` is the dependency's transparent abbreviation for
  `ringedSiteModules` of the underlying ring sheaf, hence the existing `SheafOfModules`.
  The family `phi` quantifies over **every** such M killed by t. Its second argument
  is `∀ U (m : M.val.obj U), t_U • m = 0`; no flatness, nonzero condition, or
  exactness/annihilator condition on R is assumed.
- The complex P is the existing `exactScalarPeriodicComplex R t ht`.
  Its definition uses `scalarPeriodicX` (O in degrees ≤0 and zero above),
  `scalarPeriodicD` (multiplication by t in negative degrees and zero otherwise),
  and the named square-zero compatibility theorem. Despite its name this definition
  takes only t and ht; the separate resolution theorem's kernel=image hypothesis
  is never used here.
- `periodicTensorZeroComplex R M` has `X := scalarPeriodicX M` and every `d := 0`.
  `periodicTensorZeroXIso` is the literal `eqToIso (if_pos hi)` for i≤0.
  `periodicTensorZeroMap R f` is f after these identifications in nonpositive
  degrees and the zero map above zero. Its compatibility proof is the existing
  zero-composition identities, not a postponed construction.
- `M[0]` is `(HomologicalComplex.single _ (.up ℤ) 0).obj M`, with exactly one
  possibly nonzero term. `CochainComplex.mapBifunctor P M[0] (ordinaryTensor R)`
  is the recorded signed direct-sum total tensor, not an alternative termwise
  definition. `phi M hM` is an actual complex isomorphism from that tensor to Z_M.
- The first conjunct gives its degree-i map for **every** i≤0. First project to
  the surviving (i,0) summand with `mapBifunctorSingle₂Iso.hom.f i`, identify
  P^i with O using `scalarPeriodicXIso`, and use `(λ_ M).hom`. This is the existing
  sheaf-tensor unit, induced by a tensor m ↦ a*m before sheafification.
  The left side identifies the target term with M via `periodicTensorZeroXIso`.
- The second conjunct specifies the inverse in degree i≤0: start with the same
  term identification, apply `(λ_ M).inv` (m ↦ 1 tensor m), identify O with P^i,
  and use `mapBifunctorSingle₂Iso.inv.f i` to inject the surviving summand.
  The isomorphism itself also includes all positive degrees, where both terms vanish.
- The third conjunct is the full chain-map naturality square for arbitrary
  M,N killed by t and arbitrary O-linear f:M→N. Its left edge is the existing
  total tensor functor applied to the single-complex map of f; its right edge
  is `periodicTensorZeroMap R f`. Thus naturality includes positive degrees.
- The fourth conjunct states `Nonempty (T.homology (-(q : ℤ)) ≅ M)` for **every**
  `q : ℕ`, including zero, and `IsZero (T.homology i)` for every integer i>0.
  These are the actual cohomology objects in the module-sheaf category.
- The last clause quantifies over every E and every supplied
  `epsilon : P ⟶ E[0]` satisfying
  `IsKFlatResolutionIndependentCoefficients epsilon`. This is exactly a
  quasi-isomorphism with K-flat source; no new flatness or boundedness is required.
  It gives an iso e from the **published** derived tensor of E[0] and M[0] to Q(Z_M).
  Its displayed equation specifies computation from this resolution: tensor
  Q(epsilon) followed by e equals the unique recorded K-flat/single comparison,
  followed by Q of the inverse degree-zero-total comparison and phi. Since
  Q(epsilon) is invertible this determines e. No arbitrary comparison is substituted.
- The node's ordinary-module sentence is a specialization to the one-point site:
  the same formulas and quantifiers apply, with sheaves identified with modules.
  No geometric assumptions, points of a general site, or special-site data occur.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`, `unit`, `sections`,
  `unitHomEquiv`, and sectionwise linear morphisms.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex` and the full
  complex/morphism structures; `Mathlib.Algebra.Homology.Single`: `single`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal` and the existing additive sheaf tensor instances.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `IsKFlatIndependentCoefficients`, `IsKFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison`:
  `SheafOfModules.ringed_kFlat_single_tensor_comparison`, whose full normalization
  and naturality signature was read. Its uniquely determined comparison family is
  used by `.choose`; this does not choose unspecified data from bare existence.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`:
  `CochainComplex.mapBifunctorSingle₂Iso`, including its actual projection/inclusion
  construction. `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` provides the
  reused transparent `Modules`, `ordinaryTensor`, `totalTensor`, `derivedTensor`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` and its adjunction, imported as a proof dependency.
- `def-sfb-scalar-periodic-complex` now owns the reused plain definitions and named
  compatibility proofs in the unchanged landed `Sheaf.Paper.ExactScalarPeriodicResolution`.
  The item cites that definition node instead of `lem-sfb-exact-scalar-periodic-resolution`.
  The resolution theorem is neither applied nor chosen to produce these objects.

Edge cases checked mathematically before drafting: M=0 gives zero everywhere; t=0
allows arbitrary M and makes P itself zero-differential (without forcing R=0);
the zero ring sheaf is allowed; q=0 gives the expected H^0=M; n=0 has zero outgoing
differential and n>0 has zero source. For Z/8 and t=4, the annihilator differs from
(t), but the normal-form conclusion remains valid for every killed M: no accidental
kernel=image premise occurs. The optional resolution clause is conditional and makes
no claim that P resolves a nonzero E in this example. The one-point site yields the
usual unit tensor formula for ordinary modules; an empty site is not excluded.
No STATEMENT-DISPUTED issue or node fault was found.

Searches actually run:

- msearch leanfinder, query “Tensoring a square zero periodic scalar cochain complex
  with a sheaf of modules killed by that scalar gives the zero differential complex”:
  eight results, including `HomologicalComplex.tensor_unit_d₂`, `unit_tensor_d₁`,
  generic tensor-unit existence, and `CochainComplex.cm5b.I_d`; none is this statement.
- msearch loogle, query `HomologicalComplex.leftUnitor, CochainComplex.mapBifunctorSingle₂Iso`:
  unknown identifier for the latter (it is a project declaration); not used as evidence
  of absence. Replaced with the successful query `"HomologicalComplex", "tensor"`:
  twelve generic tensor-unit/good-tensor declarations, no normal-form result.
- msearch grep, query `periodic|Periodic|mapBifunctorSingle₂Iso`, subdirectory
  `Algebra/Homology`: two hits in `AlternatingConst.lean`, which concern alternating
  differentials rather than this arbitrary ringed-site tensor normal form.
- msearch leansearch, query “The total tensor of a square zero scalar complex with
  an annihilated module sheaf is the zero differential complex”: eight results,
  including `TensorProduct.zero_smul`, `HomologicalComplex.zero`,
  `CochainComplex.cochainComplex_d_succ_succ_zero` and generic tensor identities;
  none states this theorem.
- rg over `lean/WeilConjectures` and `lean/Sheaf` for
  `periodic|Periodic|zeroDifferential|ZeroDifferential`: found the reusable
  `ExactScalarPeriodicResolution` and the specialized `SquareZeroPeriodicTensor`
  result; the latter is about the exact ordinary quotient and its constant sheaf,
  not arbitrary killed M on an arbitrary ringed site. `CompletedScalarChainShift`
  has a private all-integer zero-differential functor, with different support.
- rg for `lem-sfb-periodic-tensor-normal-form` in `lean/WeilConjectures`: no match.
  rg for the four proposed declaration names across Mathlib, WeilConjectures and
  Sheaf: no existing name. The generic `BifunctorSingle` declaration is reused.

Validation: scompile compiled the module separately under both its sandbox name and
`Sheaf.Paper.PeriodicTensorNormalForm`, cleanly (16.1 and 17.4 seconds). Every universe
and binder is explicit with `set_option autoImplicit false`; all lines are at most
100 characters; no file-local notation, instance, or private declaration is introduced.
The node statement and proof are unchanged; only lean and the added definition stmt_dep
change. No dependency modules are needed.


## New nodes

`def-sfb-scalar-periodic-complex` records ownership of the existing definitions in
`Sheaf.Paper.ExactScalarPeriodicResolution` (existing: true); it adds no Lean file.
Its primary declaration is `SheafOfModules.exactScalarPeriodicComplex`. It owns
`CochainComplex.scalarPeriodicX`, `scalarPeriodicD`, `scalarPeriodic`,
`scalarPeriodicXIso`, `SheafOfModules.exactScalarMultiplication`, and the two named
square-zero compatibility theorems used to assemble the complex. All remain in their
landed module. The generic zero-object construction specializes to module sheaves.
The definition takes only the compatible scalar t and its square-zero proof; it does
not take the kernel=image hypothesis of the separate resolution theorem.

Source: the current blueprint's ctf-equals-bc proof, “The examples,” the periodic
resolution immediately before the Tor computation. For every nonpositive degree the
term is O, with scalar differential below zero and zero differential at and above
zero. The canonical term iso is `eqToIso (if_pos hi)`. Multiplication is the existing
`unitHomEquiv.symm t`, whose sectionwise action is multiplication by t. Thus each
part of the definition is actual data, with only the existing named compatibility
proofs postponed. For t=0 this is the zero-differential sequence of copies of O;
the zero ring is allowed; for Z/8 with t=4 the complex is still defined without any
exactness assertion.

Searches for this ownership node were run again during repair. LeanSearch query
“Cochain complex with the same object in every nonpositive degree and square zero
endomorphism as differential” returned eight generic constructors and identities,
including `CochainComplex.of`, with no scalar-periodic definition. LeanFinder query
“The nonpositive periodic cochain complex of multiplication by a square zero global
scalar on a sheaf of rings” returned eight generic or unrelated complexes. msearch
grep query `scalarPeriodic|exactScalarPeriodic|periodic` in `Algebra/Homology` returned
only the two descriptions in `AlternatingConst.lean`. rg over WeilConjectures and
Sheaf found the exact definitions only in the landed module, so these are reused.
The new node records these actual queries and results. DAG rg for scalarPeriodic,
exactScalarPeriodic, scalar-periodic and scalar periodic found the existing resolution
and two consumer theorem nodes, but no definition node. `blueprint_refs.py search
'periodic'` returned only unrelated cyclic-group and Frobenius nodes; `ancestor`
confirmed `det-def-localizing-closure-ctf-equals-bc`. The new blueprint via begins with
this item and continues with its original via.

## Repair self-check by Q12

Return H2 at immutable head d6c1817873d6: repaired by the new definition node above
and replacing the delivery-added theorem dependency with its id. No declarations
were moved, renamed, copied, or modified. The item still imports the same landed
module, now justified by the definition node's existing:true attachment. Comparison
against the current live item confirms that all original stmt_deps remain, the
statement and proof are identical, and the sole added stmt_dep is the definition node.
The new node has exactly the §5/H12 fields and its statement cites exactly its two
definition dependencies. Its `lean.statement` is extracted verbatim from the landed
definition header. The item signature still matches its own unchanged module verbatim.
The earlier full clause-by-clause reading above remains applicable: iso and inverse
formulas, chain-map naturality, H^{-q} for every q≥0, positive vanishing, and the
canonical K-flat comparison equation are unchanged. This is the worker's self-check;
the maintainer supplies the independent review, as required by the repair brief.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
