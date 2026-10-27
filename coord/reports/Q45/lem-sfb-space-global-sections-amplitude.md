## Worker report

The new module Sheaf.AlgebraicGeometry.AlgebraicSpaceGlobalSectionsAmplitude states
AlgebraicGeometry.AlgebraicSpace.globalSections_finiteAmplitude, with the entire
proof `sorry`. It introduces no definitions and makes no mathematical correction.
The previous ending concerned a stage-1 re-split. The current assignment is stage 2:
the live item is split, independently reviewed, and has no Lean record. The explicit
stage handoff in brief-stage2 §0 authorizes recording its Lean statement. Its accepted
proof split is preserved.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The size convention is explicit `universe u w`, `Scheme.{u}`, and
  `[HasDerivedCategory.{w} X.SmallModules]`. The localization morphism universe is
  arbitrary. This binder selects the derived localization, not a mathematical
  finiteness or geometric hypothesis.
- The scheme S and algebraic space X over S are `{S : Scheme.{u}}` and
  `(X : AlgebraicSpace S)`, using the recorded definitions without a replacement.
- The small étale structure sheaf and its modules are the actual restriction
  `X.smallStructureSheaf`, `X.smallStructureRings` and `X.SmallModules`. The landed
  `X.smallModuleEquivalence : X.Modules ≌ X.SmallModules` is restriction to the
  small affine étale model, with its inverse determined by that equivalence.
  Thus no module universe is enlarged and no site-object/morphism universe
  equality is imposed on the original site. This is the source's module topos
  expressed on the permitted small model.
- The unbounded derived category is `X.DerivedModules = DerivedCategory X.SmallModules`.
  `E : X.DerivedQCoh` is the full subcategory defined by
  `X.derivedQCohProperty`: for every integer n, transport the nth cohomology back by
  `X.smallModuleEquivalence.inverse` and require Mathlib `IsQuasicoherent`. It is
  D_QCoh of modules, not the derived category of the abelian category QCoh.
- Quasi-compactness is `[CompactSpace (Point X.obj.obj)]` for the recorded point
  topology. Its content is exactly finite subcovers of every open cover.
  `(hqs : X.IsAbsolutelyQuasiSeparated)` is the landed affine-test criterion for
  quasi-compactness of the absolute diagonal (Stacks 0AHR), so it does not require
  the base S to be quasi-separated.
- The functor used in each conclusion is the recorded
  `ringedSiteZerothHypercohomologyOfUniverses.{u,u,u,w}` on
  `X.smallEtaleModelTopology` and `X.smallStructureSheaf`. Its actual body is
  H0 composed with the K-injective right derived functor of
  `preadditiveCoyoneda.obj (op (SheafOfModules.unit ...))`, hence Γ=Hom(O_X,-).
  Evaluating at `E.obj⟦m⟧` expresses H0 RΓ(E[m]) = Hm RΓ(E), with the usual
  cohomological shift sign. It uses no arbitrary substitute for RΓ. The small
  model ring is commutative, and the general-universe API specializes to u,u,u
  here because this already constructed model really is u-small.
- `∃ N : ℤ, 0 ≤ N ∧ ∀ (E : X.DerivedQCoh) (t : ℤ), ...` puts the single
  nonnegative integer outside both E and t, so it depends only on X and the
  ambient size convention.
- The first antecedent is `∀ i : ℤ, t < i → IsZero (H_i.obj E.obj)`;
  its conclusion quantifies every integer m with `t + N < m` and asserts
  `IsZero (H0RΓ.obj (E.obj⟦m⟧))`.
- The second antecedent is `∀ i : ℤ, i < t → IsZero (H_i.obj E.obj)`;
  its conclusion quantifies every m with `m < t` and asserts the same vanishing.
  The two implications are conjoined. No lower bound is assumed in the first,
  no upper bound in the second, and no Krull-dimension or Noetherian assumption
  is present anywhere.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, IsAlgebraicSpace,
  EtaleSite, etaleTopology, structureSheaf, Modules; this is the recorded
  fppf-sheaf/representable-diagonal/étale-atlas construction.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  transparently Mathlib SheafOfModules; inherited via the model imports.
- Mathlib.Algebra.Homology.DerivedCategory.Basic and HomologySequence:
  HasDerivedCategory, DerivedCategory and DerivedCategory.homologyFunctor;
  inherited through the public statement imports.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and its
  underlying Mathlib SheafOfModules.IsQuasicoherent predicate; inherited via
  the model and calculus. Its slice sheafification declarations retain universe u.
- Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses:
  CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses, explicitly imported.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules: DerivedModules,
  derivedQCohProperty and DerivedQCoh, explicitly imported; these use the
  SmallModules and smallModuleEquivalence of AlgebraicSpaceSmallRingedModel.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated:
  IsAbsolutelyQuasiSeparated, explicitly imported.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: pointTopologicalSpace,
  inherited from the absolute-quasi-separatedness import.

The last three definition nodes already have landed Lean records and are added
as statement dependencies under the existing-landed-node rule of brief-stage2 §5.
No new node or dependency interface repair is necessary.

Proof dependencies with recorded modules are imported without `public`:
Sheaf.CategoryTheory.KInjectiveComputes (Functor.kInjective_computes),
WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
(SheafOfModules.exists_boundedBelow_injective_resolution), and
WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
(Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE).
The ringed-site K-injective resolution module is already publicly inherited through
the zeroth-hypercohomology module. Mathlib proof imports provide the standard
t-structure, left exact additive functors, and Grothendieck module categories.
The three unrecorded geometric proof prerequisites are named in the proof docstring;
they need no interface to state this theorem and no replacement lemmas are invented.

Sources read locally: spaces-perfect.tex lemma-application-nice-K-injective (08F7),
spaces-cohomology.tex lemma-vanishing-quasi-separated (072C), and derived.tex
lemma-negative-vanishing (05TC). They agree with the accepted item statement:
choose C≥1, use N=C-1, and keep the unbounded sides of both implications.

Edge cases checked mathematically before writing:
empty X permits N=0; affine X permits N=0; the zero derived object satisfies both
clauses for every t. A module in degree d has Hm after shifting by m in degree zero,
so the shift sign and strict inequalities are correct (degree d remains allowed).
Negative t and m are allowed. Neither implication imposes an opposite truncation.
A non-quasi-separated base is allowed because absolute quasi-separatedness is
on X, not a relative diagonal assumption. The existing small-model equivalence
preserves the original coefficient universe; the unrelated large-site maximum
universe restriction of the general zeroth functor is avoided by its actual
small-site specialization, not by adding a hypothesis.

Searches performed using msearch.py (raw records in the sandbox searches.jsonl):

- LeanFinder: "Derived global sections on a quasi compact quasi separated algebraic
  space have finite amplitude on unbounded complexes with quasi coherent cohomology".
  Eight hits, all generic derived t-structure/vanishing or bounded representatives;
  none states the geometric uniform amplitude theorem.
- Loogle: `"rightDerivedFunctor", "IsLE"`. Three hits about Kan extensions and
  abstract right derivation; none states an amplitude bound.
- grep Mathlib: `rightDerivedFunctor.*[Ii]sLE|[Ii]sLE.*rightDerivedFunctor|AlgebraicSpace`.
  Nine hits on abstract right derivation/adjunction, no algebraic-space assertion.
- LeanSearch: "Uniform finite upper cohomological amplitude of derived global sections
  on qcqs algebraic spaces for unbounded quasi coherent complexes". Eight hits on
  t-structure bounded representatives, local presentations, shifted Hom and scheme
  sections of affine limits; no matching theorem.
- rg of both live WeilConjectures and Sheaf for the item id, amplitude wording and
  `globalSections_finiteAmplitude`: no matching declaration. The only nearby amplitude
  text concerns étale coefficient modules on a point, a different statement.
- Inspection of AlgebraicSpace*.lean found the already landed small ringed model,
  derived QCoh and absolute-quasi-separatedness interfaces; those are reused.

Validation: scompile.py compiled this module in both its isolated sandbox name
and its intended library name, cleanly with no errors or unexpected warnings.
The only postponed theorem in this delivery is the item's named theorem.
There is no STATEMENT-DISPUTED finding and no correction to the accepted split.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
