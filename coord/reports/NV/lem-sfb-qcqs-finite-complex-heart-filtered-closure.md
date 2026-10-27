## Worker report

Module `Sheaf.Paper.NoetherianFiniteComplexHeartFilteredClosure` states
`AlgebraicGeometry.ProEtale.noetherian_finite_complex_heart_filtered_closure`
with one whole-proof `sorry`. No definition or theorem is reproved, and no
statement correction is made. The live node already contains the reviewed NY
Noetherian correction. The inherited stage-1 refusal is inapplicable: the
2026-10-22 stage handoff in brief-stage2 explicitly allows this stage-2 work,
and coord/queue.tsv lists the item at stage 2 with no Lean record.

### Hypotheses and clauses

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The fixed algebraic closure is the
  existing `PadicAlgCl ℓ`; finite subextensions are
  `PadicAlgCl.FiniteIntermediateField ℓ`. No new choice of closure is made.
- The commutative condensed coefficient ring is
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})`
  with `[MonObj Λ] [IsCommMonObj Λ]`. The hypothesis `hΛ` explicitly lists the
  node's six cases, up to ring-object isomorphism: finite discrete commutative
  A annihilated by ell^n; Z_ell; O_E; Q_ell; E; and Omega. `Finite A` and
  `∃ n, ∀ a, (ℓ ^ n) • a = 0` impose exactly the finite coefficient conditions.
  The finite discrete ring can be represented in `Type 0` without changing
  its isomorphism classes. `Mon.mk` isomorphisms preserve addition and
  multiplication. A and E are quantified only in their applicable cases;
  they have no role in the other cases, just as in the node.
- The topological objects are `Profinite.continuousMapRingObj` of the specified
  topological rings and `Profinite.padicIntegersRingObj ℓ E` for O_E. The final
  disjunct uses `continuousMapRingObj (PadicAlgCl ℓ)`, meaning ALL continuous
  Omega-valued functions. It does not use `Profinite.padicAlgClRingObj`.
  The recorded `IsLocalizingAdmissibleCoefficient` now also includes that
  different finite-subextension-valued ring, so using that predicate would
  add an unwanted coefficient case. Its module supplies the existing
  coefficient constructions; the six cases are stated explicitly.
- The scheme is `(X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]`.
  These are exactly locally Noetherian and quasi-compact. Quasi-separatedness
  is a consequence of local Noetherianity, not an extra assumption. No
  affineness, dimension, characteristic, invertibility of ell, completeness,
  or absolute cohomological-dimension hypothesis is added.
- The ambient category underlying `indFiniteConstructibleComplexHearts Λ X`
  is exactly `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (condensedRingObj Λ X)`: ordinary internal modules over the pulled-back
  coefficient ring. It has no module completeness restriction. Derived
  pushpull and global sections are the recorded ordinary module-derived
  constructions; neither introduces an extra hypothesis in this heart result.
- C_X is `IsConstantModelConstructible Λ X`. Its existing definition uses
  finite constant scalar models on finite constructible locally closed
  stratifications in the qcqs case, and the affine-local convention otherwise.
  On this Noetherian scheme it is the first case. The models use finitely
  presented scalar modules and include integral torsion models.
- Finite complexes are the existing `IsFiniteConstantConstructibleComplex`:
  a cochain complex over this ambient module category, a finite set of
  possible nonzero terms (`IsZero` off a `Finset ℤ`), and constructibility
  of every term. Its differentials have only the cochain complex conditions.
  `finiteConstructibleComplexHearts` is the replete class of modules
  isomorphic to `K.homology 0`, namely the categorical kernel/image quotient
  in the node. No constructibility assumption on that quotient is built in.
- I_X is the existing `indFiniteConstructibleComplexHearts Λ X`, defined by
  `ObjectProperty.ind.{u + 1}` of those hearts. Mathlib's `ind` quantifies over
  `J : Type (u + 1)`, `SmallCategory J`, `IsFiltered J`, and a genuine ambient
  `ColimitPresentation J N`. Its diagram lives in the module category,
  not in the category of complexes. Thus arrows are arbitrary module maps,
  with no chain-map lift. `ind` is replete by its existing isomorphism instance.
- Zero containment is the first conjunct `.ContainsZero`. It applies to every
  zero object because I_X is replete.
- Containment of C_X is the second conjunct
  `IsConstantModelConstructible Λ X ≤ indFiniteConstructibleComplexHearts Λ X`.
- Kernel closure is `.IsClosedUnderKernels`, for all morphisms whose source
  and target satisfy I_X, with no restrictions on those morphisms.
- Cokernel closure is `.IsClosedUnderCokernels`, with the same ambient maps.
- Extension closure is `.IsClosedUnderExtensions`. Its Mathlib field
  quantifies over EVERY ambient short complex `S` with `S.ShortExact` and
  I_X on S.X1 and S.X3, yielding I_X on S.X2. It assumes no filtered
  presentation or finite-stage lift for the middle term or the extension.
- Small ambient coproduct closure is the last conjunct:
  `∀ I : Type (u + 1), ...IsClosedUnderColimitsOfShape (Discrete I)`.
  This uses all ambient colimit cocones of discrete diagrams. The bound
  u+1 is exactly the bound already used in every filtered presentation,
  so resulting presentations use the same indexing universe.

### Dependencies and existing definitions

Read each statement dependency node and its recorded declaration/docstring.
The following recorded modules and declarations supply the notions used:

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`, and its
  publicly imported continuous coefficient objects. The predicate has the
  additional case explained above and is intentionally not used as hΛ.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`,
  `moduleObjectDerivedPullback`; these name the ordinary total derived
  functors of the recorded composites, not a completed module category.
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`:
  `AlgebraicGeometry.ProEtale.condensedModuleSections`, the existing forgetful
  functor followed by evaluation at `op (Scheme.ProEt.mk (𝟙 X))`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology` (background convention).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`.
- The size node and scheme-conventions node are metatheoretic convention
  records. Their signatures are represented by explicit u/u+1 universes
  and the recorded Mathlib classes; neither has a declaration to import.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`, through the
  public import in the finite-heart presentation module.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit`
  and its cocone/IsColimit interfaces, used through `ColimitPresentation`.
  The definition of `ObjectProperty.ind` uses `IsFiltered` explicitly.
- `Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- Added the already-landed definition node
  `def-sfb-finite-constructible-complex-heart-presentations` to stmt_deps.
  Its module `Sheaf.Paper.FiniteConstructibleComplexHeartPresentations`
  supplies `IsFiniteConstantConstructibleComplex`,
  `finiteConstructibleComplexHearts`, and
  `indFiniteConstructibleComplexHearts`. No new node or duplicate definition
  is necessary. This is an allowed addition of a landed statement dependency.

The stated proof dependencies are imported without `public`:
`Sheaf.CategoryTheory.SheafTensor` and
`WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`.
The sieve-module Grothendieck, Noetherian scalar heart, scalar FP2, and
abstract FP2 realization nodes currently have no Lean record, so there
is no recorded proof module to import. They are used only by the docstring's
four-step proof plan, not as missing statement prerequisites. They are not
stated anew in this delivery. The docstring reproduces the node's four steps.

### Edge cases and statement review

Checked the empty scheme, zero finite coefficient ring (including an exponent
n=0, which simply forces the zero ring), the zero complex, arbitrary finite
supports containing or omitting degree zero, arbitrary module differentials,
and arbitrary module maps between hearts. Filtered categories are nonempty
by `IsFiltered`; the empty coproduct is still included by `I := PEmpty`.
`ContainsZero` and repleteness handle the zero presentation. The finite-stage
predicate does not assert constructibility of H^0, even though the Noetherian
proof plan derives it. There is no Tor-amplitude or finite projective dimension
condition on finite A or on the terms. Non-affine Noetherian X is included.

The nearby theorem `finite_complex_heart_filtered_approximation` in
`Sheaf.Paper.FiniteComplexHeartFilteredApproximation` requires `[IsAffine X]`
and a supplied local derived cohomology bound. It therefore does not state this
node and cannot be recorded as an existing match. The upstream ind-heart API
in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible`
uses its own arbitrary-presentation constructibility and a heart-closure
hypothesis; it is not this theorem or this finite scalar-model class.

No new STATEMENT-DISPUTED flag: the live accepted Noetherian statement and
its four-step proof are preserved. The source still labels the exact
full-generality literature reference WANTED, and the proof depends on the
recorded scalar-heart/FP2 obligations. These are not silently discharged here.
The earlier NY counterexample to the arbitrary-qcqs version and its affected
parent are already recorded by the accepted stage-1 review; this delivery
neither reverts that correction nor edits any citer.

### Searches

All searches used msearch.py for group NV and this item unless specified.

- LeanFinder: "On a Noetherian scheme filtered colimits of degree zero
  cohomology of finite constructible complexes form a class closed under
  kernels cokernels extensions and coproducts". Eight hits, including
  LightCondensed Grothendieckness, Scheme.Modules colimits/abelianness and
  condensed AB axioms; no exact statement.
- LeanSearch: "Filtered colimits of cohomology of bounded constructible
  complexes on Noetherian schemes closed under kernels cokernels extensions
  and coproducts". Eight hits on complex filtered colimits, module/group
  colimit constructions and colimit/limit interchange; no exact statement.
- Loogle: "ObjectProperty.IsClosedUnderKernels,
  ObjectProperty.IsClosedUnderExtensions, ObjectProperty.ind". No hits;
  service reported unknown identifier ObjectProperty.IsClosedUnderKernels.
  Read the pinned Mathlib source for these declarations instead.
- Mathlib grep: "finite.*[Cc]onstructible.*[Hh]eart|[Ii]nd.*[Cc]onstructible".
  Nine unrelated hits on constructible topology/set induction; no match.
- rg across lean/WeilConjectures and lean/Sheaf for this item id,
  `qcqs_finite_complex_heart_filtered_closure`, and
  `indFiniteConstructibleComplexHearts`: found the existing finite-heart
  definitions, the stronger-hypothesis approximation theorem, and a source
  citation in ClosedTorsionRigiditySerreTransfer; no exact theorem.
- rg of dag/nodes for the finite-heart declarations identified their owning
  definition node, which is reused and added to stmt_deps. Read its full
  module. Read the recorded coefficient, module-derived, global-sections,
  site, constructibility, cochain, colimit, scheme and Noetherian signatures.

### Validation

`scompile.py NV lem-sfb-qcqs-finite-complex-heart-filtered-closure` compiled
both the sandbox file (9.1 seconds) and its library module (4.6 seconds)
against the live server build, with no errors or unexpected warnings.
All variables/universes are explicit (`set_option autoImplicit false`),
all lines have at most 95 characters, and the only new proof is `sorry`.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
