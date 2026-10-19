## Worker report

The module Sheaf.RingTheory.PseudoCoherentMaximalFibrePerfect states
DerivedCategory.isPerfect_and_tensor_homology_vanish_of_maximal_fibres, with sorry.
The statement is unchanged. Source read locally: literature/stacks-project/more-algebra.tex,
lemma-check-perfect-pointwise (Tag 068V), implication (3) to (1).
The declaration docstring includes all six DAG proof steps.

Hypothesis and conclusion correspondence:

- A commutative ring R: {R : Type u} [CommRing R].
- C in D(R): C : DerivedCategory (ModuleCat.{u} R), with
  [HasDerivedCategory.{u} (ModuleCat.{u} R)] for the chosen localization.
  This is the same module/derived-category size convention as upstream IsPerfect;
  u is arbitrary and may be enlarged to accommodate any given module.
- Pseudo-coherence: hC : C.IsPseudoCoherent, the dependency's existing definition.
- Integers a ≤ b: (a b : ℤ) (hab : a ≤ b).
- Every maximal ideal: ∀ (m : Ideal R), m.IsMaximal → ...
  Maximality is a proposition here since taking the quotient as a module needs no
  field instance. No ideals or rings are excluded by a Nontrivial assumption.
- κ(m) = R/m: ModuleCat.of R (R ⧸ m), placed in degree zero by
  (singleFunctor (ModuleCat.{u} R) 0).obj.
- Derived tensor: C ⊗ that degree-zero module, using the existing derived monoidal
  structure imported by Perfect. This is not ordinary tensor on arbitrary complexes.
- Cohomology vanishes outside [a,b]: for every integer i, i < a ∨ b < i implies
  IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj ...).
- First conclusion, perfectness: C.IsPerfect, the upstream dependency definition.
- Second conclusion: ∀ (M : ModuleCat.{u} R) (i : ℤ), i < a ∨ b < i implies
  IsZero of H^i(C ⊗ (singleFunctor ... 0).obj M). M is arbitrary: no finite,
  flat, free, projective, or nonzero hypothesis.

The fibre cohomology is read as an R-module. This is precisely the vanishing
asserted for scalar extension, not a different hypothesis: on a K-flat representative
P, the derived tensor in D(R) is Q(P ⊗_R (R/m)[0]) by
DerivedCategory.QObjTensorQObjIsoOfKFlatLeft. The termwise scalar extension computes
the same complex with its extra R/m-action by the dependency
SheafOfModules.derivedChangeOfRings specialized to the identity-cover one-object site.
Restriction of scalars is exact and reflects zero objects, so its cohomology is zero
if and only if the R/m-module cohomology is zero. The item only asserts vanishing,
not an equality or isomorphism retaining the extra action. No substitute scalar
extension object or private definition has been introduced.

Statement dependencies read in full and imported:

- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory,
  HasDerivedCategory, Q, singleFunctor; Basic is transitively public-imported.
- Sheaf.RingTheory.RingPseudoCoherent: DerivedCategory.IsPseudoCoherent.
- Sheaf.Algebra.Homology.DerivedChangeOfRings:
  SheafOfModules.derivedChangeOfRings (the existential derived scalar extension
  theorem, retained as a public statement-dependency import).
- WeilConjectures.CategoryTheory.DerivedCategory.Perfect:
  DerivedCategory.IsPerfect. Its actual signature fixes the module and localization
  universes to u; its definition is a bounded finite projective representative.
- Mathlib.Algebra.Homology.DerivedCategory.HomologySequence:
  DerivedCategory.homologyFunctor, transitively public-imported.

Stated proof dependencies are imported without public:

- Sheaf.Algebra.Homology.BoundedFlatKFlat:
  CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat.
- WeilConjectures.CategoryTheory.DerivedCategory.FlatModel:
  DerivedCategory.QObjTensorQObjIsoOfKFlatLeft.
- WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat:
  CategoryTheory.MorphismProperty.kFlat.
- Mathlib.RingTheory.LocalProperties.Exactness: bijective_of_localized_maximal.
- Mathlib.RingTheory.Ideal.Maximal: Ideal.exists_le_maximal.

The cancellation and principal-cover glue proof nodes have no Lean record or
mathlib_match; consequently no import is possible or required for them yet.
There are no new nodes, dependency repairs, statement corrections, or disputes.

Edge cases checked before writing: the zero ring has no maximal ideals and only zero
unital modules, so the fibre condition is vacuous and both conclusions true; C = 0
works for every interval; a = b gives concentration in exactly one degree; arbitrary
negative endpoints are allowed; endpoint degrees are not required to vanish. No
bounded-below or Noetherian condition has been introduced. R/m has the stated module
structure even for nonmaximal m, but the hypothesis tests exactly maximal ideals.

Searches for an existing statement:

- msearch.py leanfinder: "A pseudo coherent ring complex is perfect if its derived
  tensors with all maximal residue fields vanish outside a fixed interval".
  Eight hits: projective Tor vanishing, Ext/projective or injective dimension,
  and K-projectivity; none states this residue-fibre criterion.
- msearch.py loogle: "DerivedCategory.IsPerfect, DerivedCategory.IsPseudoCoherent".
  Zero hits, unknown identifier DerivedCategory.IsPerfect in Mathlib.
- msearch.py grep: "pseudo.?coherent|perfect.*residue|residue.*perfect".
  Six hits, all about perfect fields in ramification or finite quotient files.
- rg of the read-only upstream WeilConjectures and project lean/Sheaf for
  pseudo-coherence, isPerfect with pseudo-coherence, and maximal/fibre combinations:
  no existing ring statement; project RingPseudoCoherent supplies the notion.
  Upstream Perfect supplies perfectness and tensor infrastructure, not this theorem.
- rg for the item id in upstream WeilConjectures: no existing declaration.
  Checked the new full declaration name against both source trees: no collision.

Validation: scompile.py compiled the delivered file cleanly on the server (1.5 seconds,
nice 19, two threads, 60-second per-file limit). No local compiler was run.

## Second reading by NV

Independent reading of the sandbox node, its source in more-algebra.tex at
lemma-check-perfect-pointwise (Tag 068V), and the delivered Lean file. The source
states (3) implies (1) for a pseudo-coherent complex over an arbitrary ring;
the surrounding Perfect complexes section adds no Noetherian, local, domain,
characteristic, or bounded-below assumption. The node explicitly chooses a ≤ b;
Lean follows that node rather than adding any further source hypotheses.

Object/hypothesis/conclusion inventory and verdicts:

1. A commutative ring R: `{R : Type u} [CommRing R]`. Exact; neither `Nontrivial`
   nor any finiteness instance is assumed.
2. An object C of D(R): `(C : DerivedCategory (ModuleCat.{u} R))`, with
   `[HasDerivedCategory.{u} (ModuleCat.{u} R)]`. Read Mathlib's Basic definition
   and localization-size documentation. This is the dependency's localization
   of integer cochain complexes at quasi-isomorphisms. The common universe is
   the convention required by the actual upstream `IsPerfect` signature, not
   a restriction to finite or countable modules: u is arbitrary, and any ring
   and any test module can be placed together in a sufficiently large universe.
3. Pseudo-coherence of that same C: `(hC : C.IsPseudoCoherent)`. Read
   `Sheaf.RingTheory.RingPseudoCoherent`: it requires a bounded-above finite-free
   complex E with `Nonempty (Q.obj E ≅ C)`. This is precisely the node's
   definition, with no cohomological bounded-below assumption. Exact.
4. Fixed integers a ≤ b: `(a b : ℤ) (hab : a ≤ b)`. Exact; the same endpoints
   are used in both vanishing assertions, uniformly over all maximal ideals
   and all test modules.
5. Every maximal ideal m and its residue field R/m: the fibre hypothesis begins
   `∀ (m : Ideal R), m.IsMaximal →`. Its tensor factor is
   `(singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R (R ⧸ m))`.
   Read Basic's `singleFunctor` and `singleFunctorIsoCompQ`: this is the quotient
   module placed in degree zero in D(R). Using a Prop implication for maximality
   suffices because the statement only needs its R-module structure. Exact.
6. Derived scalar extension and fibre vanishing: `hfibres` quantifies over every
   `i : ℤ`, with `(i < a ∨ b < i) → IsZero ((homologyFunctor ... i).obj (...))`.
   The tensor is the existing derived monoidal tensor imported by Perfect.
   Read `QObjTensorQObjIsoOfKFlatLeft` in FlatModel and the full signature of
   `SheafOfModules.derivedChangeOfRings`, the recorded dependency. On a
   bounded-above finite-free representative P, the former computes the tensor
   by P tensor (R/m)[0]. The latter computes scalar extension by the same
   termwise complex with its R/m-action. Restriction of scalars is exact and
   reflects zero modules, so its cohomology vanishes exactly when the
   R/m-cohomology vanishes. Thus no extra action is discarded that matters to
   this predicate, and no replacement scalar-extension definition is introduced.
   The order of quantifiers and both strict endpoint inequalities are exact.
7. Perfectness conclusion: `C.IsPerfect`. Read the upstream Perfect definition
   and its surrounding variables: a bounded integer complex of finite projective
   R-modules whose derived image is isomorphic to C. It is defined for arbitrary
   commutative R; Noetherian assumptions on later theorems do not enter this
   definition. This is exactly def-pc-perfect-ring-complex.
8. Uniform tensor conclusion for every R-module M:
   `∀ (M : ModuleCat.{u} R) (i : ℤ), (i < a ∨ b < i) → IsZero ...`, with
   `C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj M`. Exact. No flatness,
   projectivity, finite generation, nonzero condition, or field assumption on M.
   This is the source's Tor amplitude in [a,b], expressed without a new predicate.

Edge cases: R may be the zero ring, where the maximal-ideal quantifier is empty
and all unital modules are zero; C = 0 and M = 0 are included. For a = b,
including a = b = 0, only that one degree may have nonzero cohomology. Negative
endpoints are unrestricted; the two endpoint degrees are not made to vanish.
No scheme or family index is introduced, so empty-scheme and empty-index
conditions are inapplicable beyond the empty maximal spectrum just checked.
No characteristic is excluded. All variables and the universe u are explicitly
bound; no independent smaller test-module universe makes a quantifier vacuous.

Independent searches (different wording from the worker):

- msearch.py leanfinder: "A bounded above finite free complex is perfect if tensor
  cohomology with every simple quotient module vanishes uniformly outside an
  interval". Eight hits: projective Tor vanishing, projective dimension/Ext
  criteria, and maps from projective single complexes. None states this result.
- msearch.py loogle: `"IsPseudoCoherent"`. Zero hits.
- msearch.py grep: `finiteTorAmplitude|torAmplitudeIn|IsPseudoCoherent`. Zero hits.
- Direct rg in Mathlib's homological algebra and ring theory, upstream
  WeilConjectures, and the project's lean/Sheaf, using pseudo-coherence,
  maximal/Tor-amplitude, and perfect/fibre combinations. Opened the candidate
  signatures in MinimalFreeModel, MinimalFreeComparison,
  PseudoCoherentBoundedFiniteFreeModel, upstream Perfect and TorAmplitude, and
  upstream DirectImage/FiniteFreeComplex. These give local minimal models,
  finite-free approximations, a Noetherian perfectness criterion, or scheme
  finite-free-complex results, not this arbitrary-ring uniform maximal-fibre
  criterion. The existing pseudo-coherence and perfectness notions are reused.

No new definition nodes, dependency modules, or statement correction occur in
this delivery; H12/H13 and corrected-citer checks therefore have no additional
objects to review. Read all four statement-dependency nodes and their actual
recorded signatures, and checked the proof-dependency records against imports.
Unstated cancellation and principal-cover-gluing nodes have no module to import.
The declaration docstring follows all six proof steps in order, including
ordinary cohomology detection, the two cuts, finite principal cover, and arbitrary
module tensors. There is one theorem with proof `sorry`, no proved assertion,
no hollow definition, private notion, file-local notation, or local instance.

Mismatches found: none. Kept the correct Lean file and node unchanged; appended
this independent review only. Checked programmatically that `lean.statement`
is verbatim the file signature before `:=`; no unbound variable was found by eye.
Independent validation: scompile.py compiled the only delivered file on the server
in 1.5 seconds (nice 19, two threads, 60-second limit), with no errors or warnings.
