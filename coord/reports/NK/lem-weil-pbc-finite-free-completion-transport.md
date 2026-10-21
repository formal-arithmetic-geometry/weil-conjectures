## Worker report

The module `Sheaf.CategoryTheory.FiniteFreeCompletionTransport` states the entire node,
with four named theorems and only `sorry` proofs. The repair adds two definition
nodes recording existing declarations; it introduces no Lean definitions, dependency
modules, or natural-language statement corrections.

The primary theorem `CategoryTheory.finiteFreeCompletionTransport` gives the unique
unit-normalized natural isomorphism and preservation of local derived completeness.
The three remaining declarations give its integer-shift, identity, and coefficient-tower
equations. They quantify over any isomorphisms with that normalization: by the primary
uniqueness clause these are precisely the comparison whose existence is asserted there.
These formulations express the coherence clauses without choosing any isomorphism from a
bare existence claim. The equations require no stronger finite-free or parameter
hypotheses: once the normalized comparisons exist, their coherence follows from reflection.

Clause-by-clause correspondence:

- The small site is `{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}`.
  Ring sheaves are `R S : Sheaf J CommRingCat.{u}` and their map is `a : R ⟶ S`.
- Finite freeness is `hfree : ∃ d : ℕ, Nonempty (...)`, where the left object is the
  regular S-module restricted along a and the right object is the categorical coproduct
  of `Fin d` copies of the regular R-module. Finite coproducts in this abelian category
  are finite direct sums. No basis is a parameter of the isomorphism.
- `A : SheafOfModules.SystemScalarModel a` exposes the recorded
  `DerivedChangeOfRingsCochainModel` as `A.model`. In particular `A.model.T` is the
  universal derived functor of the prescribed sheafified ordinary scalar extension,
  with its actual K-flat computations. It is not an arbitrary functor or ring action.
- `t`, `v`, and `w` are compatible global section families. `hw` requires each value of
  w to be a unit; uniqueness of inverses makes this exactly a global unit, also over
  the zero ring. `he : 1 ≤ e` is the positive-exponent condition, and `hparam` is
  the pointwise equality `a.hom.app U (t.val U) = w.val U * v.val U ^ e`.
- `D` and `E` are the recorded `RingedKoszulLimitPresentation` for the singleton
  lists `(fun _ ↦ t)` and `(fun _ ↦ v)`. These retain the strict towers, total derived
  inverse limit, and augmentation units. `D.completion` and `E.completion` are the
  actual completion functors and `D.unit` and `E.unit` are the specified units.
- The natural isomorphism has type `D.completion ⋙ A.model.T ≅ A.model.T ⋙ E.completion`.
  Its equation `A.model.T.map (D.unit M) ≫ κ.hom.app M = E.unit (A.model.T.obj M)`
  is exactly the node's displayed unit equation, in Lean's composition order.
  `∃!` gives canonicity and basis independence: every construction preserving the
  unit gives this same natural isomorphism, regardless of basis or unit-power witness.
- The final universal implication uses `IsLocallyDerivedRingedIdealComplete` for
  `image (ringedKoszulScalar R t)` and its `image.ι`, and likewise for v. The image
  is the principal ideal subsheaf, including coefficients that exist only locally.
  This is exactly the recorded local, slice-wise derived internal-Hom condition.
- `finiteFreeCompletionTransport_shift` concludes `NatTrans.CommShift κ.hom ℤ`.
  The completion shift structures are normalized by natural transformations whose
  components are exactly `D.unit` and `E.unit`, with their `CommShift` instances.
  These are the shift-compatible units supplied by `ringedCompleteTriangulated`.
  Quantification over these structures covers the canonical shifts and all integer
  degrees; there is no choice of an unrelated shift comparison or weakened degree range.
- `finiteFreeCompletionTransport_id` uses `SystemScalarModel (𝟙 R)`, the same parameter
  and same completion on both sides. The formula is `u_(Lambda M)` followed by
  `Lambda(u_M^-1)`, using the published `systemScalarModelDerivedUnit rfl A`.
  Its representative formula is ordinary scalar multiplication, not an arbitrary
  automorphism of the identity derived functor.
- `finiteFreeCompletionTransport_comp` compares `C_b(κ_a)` followed by `κ_b` and
  `Lambda_T(alpha_M)` with `alpha_(Lambda_R M)` followed by `κ_ab`.
  `alpha` is the published `systemScalarModelDerivedComposition rfl A B F`, whose
  cochain normalization and formula on local pure tensors are already fixed.
  The equation quantifies over arbitrary R,S,T, with all three normalized comparisons.
  For finite-free maps the composite is finite free; the parameter relation composes
  as `ba(t)=b(w)*u^e*z^(ef)`. Applying this binary equation inductively is precisely
  the claimed agreement for every finite tower, including identity steps.

Dependencies read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings` (reexported by SystemScalarModel);
  topology and sheaf conventions are Mathlib's `GrothendieckTopology` and `Sheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  the exact abbreviation of Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, and `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `Sheaf.CategoryTheory.SystemScalarModel`, `SheafOfModules.SystemScalarModel`,
  and `SheafOfModules.systemModelTmul`; its normalized adjunctions extend
  the preceding existing universal model without changing its tensor functor.
- `Sheaf.CategoryTheory.SystemScalarCoherence`,
  `SheafOfModules.systemScalarModelDerivedUnit` and
  `SheafOfModules.systemScalarModelDerivedComposition`, including their representative
  theorems and ordinary pure-tensor formulas.
- `Sheaf.Paper.WeilCompletedTensorReflector` publicly retains
  `Sheaf.CategoryTheory.RingedKoszulCompletionReflector` and
  `CategoryTheory.ringedKoszulCompletionReflector`. This is a proof input and the
  original node statement explicitly cites its reflector notion. The inherited
  `stmt_deps` entry is retained; its theorem is not invoked in a signature.
  The wf specialization in the dependency record is not duplicated or rebound.
- `Sheaf.CategoryTheory.RingedKoszulSystem`,
  `CategoryTheory.RingedKoszulLimitPresentation`, its `completion` and `unit`, and
  `CategoryTheory.ringedKoszulScalar`.
- `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`,
  `CategoryTheory.IsLocallyDerivedRingedIdealComplete`.
- `Sheaf.CategoryTheory.RingedCompleteTriangulated`,
  `CategoryTheory.ringedCompleteTriangulated`; supplies normalized exact completion
  shifts and closure of completeness under all shifts.
- Proof-only imports include `Sheaf.CategoryTheory.RingedCechKoszulDualLimit`,
  `Sheaf.CategoryTheory.UnitPowerCompleteness`, and Mathlib's total tensor
  `Mathlib.Algebra.Homology.BifunctorShift` (the recorded tensor-complex dependency).
  The strict-tower transport proof dependency currently has no Lean record/module,
  so there is no existing module to import for it. It is not needed to type this item.

The Koszul-system and local-completeness definition nodes are added to `stmt_deps`.
The two new definition nodes record the plain scalar-model structure and the plain
scalar-coherence maps used by the signatures. The existence/coherence theorem nodes
are removed from the saved packet's added `stmt_deps`: neither theorem supplies
chosen data here. `lem-sfb-ringed-complete-triangulated` is removed from the saved
packet's added `stmt_deps` and remains in `proof_deps` with its proof import.
No dependency from the live base is removed, and no source/proof field changes.

Edge cases checked mathematically before writing: d=0 (S is the zero ring sheaf), d=1,
t=v=0, unit parameters, zero divisors, nilpotent parameters, e=1, empty sites and slices,
unbounded complexes, zero objects, identity maps, and towers with repeated rings.
Zero parameters give identity completion, unit parameters give zero completion, and
all maps and equations remain well typed in these cases. No nontrivial-ring, flatness,
Noetherian, exact-countable-product, regularity, or boundedness hypothesis is added.
Standard coefficient derived-category instances are the ones fixed by SystemScalarModel;
strict-tower localization instances select the same standard morphism size and are always
available from `HasDerivedCategory.standard`.

Searches for existing statements (2026-10-21):

- `msearch.py ... leanfinder "Finite free extension of scalars on a ringed site commutes
  with derived Koszul completion preserving the unit"`: eight hits on differentials and
  Kaehler smoothness; none treats derived sheaf completion.
- `msearch.py ... leansearch "Derived completion for module sheaves commutes with finite
  free change of rings"`: eight free-sheaf/pullback and sheafification hits; no comparison
  with derived completion or its unit.
- `msearch.py ... loogle "AdicCompletion.ofTensorProductEquivOfFiniteNoetherian"`:
  five ordinary adic-completion results. Their Noetherian finite-module comparison is
  not the unbounded ringed-site completion theorem.
- `msearch.py ... grep "derived.*[Cc]omplet|[Cc]omplet.*derived|ofTensorProductEquivOfFiniteNoetherian"`:
  five hits in Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean; no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for finite-free scalar maps,
  change-of-rings units/associators, and completion transport: existing SystemScalarModel
  and SystemScalarCoherence are reused; the completion comparison itself is absent.
  The blueprint-id search in `lean/WeilConjectures` gives no matching declaration.
- Read local Stacks algebraization.tex, lemmas derived-completion and
  derived-completion-koszul (Tags 099B, 0A0E), and all recorded dependency interfaces.

The initial compiler mismatch was repaired by explicitly instantiating the three scalar-model
universes and the canonical scalar unit/associator universes with u. This directs elaboration
to the original ringed site and coefficient universe; no site or coefficient size was changed.
No STATEMENT-DISPUTED flag or mathematical node fault was found.

Validation: the prescribed server compiler checked the sandbox and library module.
After repairing universe elaboration and the single long-line warning, `deliver2.py
--no-push` reported OK: final module compiles cleanly and the maintainer preflight passes.
The packet contains the unchanged item module, item JSON, two new existing-definition
node records, and this report. All four theorem proofs remain `sorry`, as stage 2 requires.


## Repair of independent return on 34d6bea90465

H2 is repaired in the DAG metadata. `lem-pur-system-scalar-model` is an existence
statement, whereas every `A` in this module is an explicit `SystemScalarModel` binder.
Its replacement is `def-weil-pbc-system-scalar-model`, recorded on the unchanged
`Sheaf.CategoryTheory.SystemScalarModel` module, with `SystemScalarModel` and
`systemModelTmul` listed. Likewise, the identity and composition signatures call
`systemScalarModelDerivedUnit` and `systemScalarModelDerivedComposition` directly;
they never use `.choose` or the representative theorems. Their replacement is
`def-weil-pbc-system-scalar-coherence`, recorded on the unchanged
`Sheaf.CategoryTheory.SystemScalarCoherence` module, with the two derived maps and
`systemScalarRestrictionUnit` / `systemScalarRestrictionComposition` listed.
The statement-only use of unit-pinned `CommShift` structures needs no
`ringedCompleteTriangulated` theorem, so its added statement dependency is dropped.
The theorem remains a proof dependency and retains its import.

The advisory about the inherited reflector theorem was checked: it is not used by
any signature. It remains an original statement dependency because the natural-language
node explicitly names the canonical reflector through it; the requested repair does
not alter that original source clause. All four Lean signatures and docstrings are
retained byte for byte. The item differs from the live base only in `lean` and
`stmt_deps`. No `statement_change` is needed because no mathematical statement changes.

Self-check with the item node and Lean file open: finite freeness is still the finite
coproduct isomorphism `hfree`; `A.model.T` is still the recorded derived scalar functor;
`hw`, `he`, and `hparam` still say global unit, positive exponent, and the parameter
equality. `D`/`E` retain the Koszul presentations and units. The `∃!` unit equation and
principal-image local completeness implication are unchanged. The shift clause still
uses unit-pinned completion shifts for all integers; identity and composition still
use the actual canonical derived unit and associator. Edge cases from the first
report remain covered. No new hypothesis or conclusion is introduced by the repair.

## New nodes

`def-weil-pbc-system-scalar-model` records existing structure data, rather than the
existence theorem in `lem-pur-system-scalar-model`. Its definition matches the five
fields `model`, `ordinaryAdj`, `unit_normalized`, `adjunction`, and `transpose` (the
first is the underlying model, followed by its two normalized adjunctions). The local
pure tensor is the existing sheafification image in `systemModelTmul`. Sources read:
Stacks sites-modules.tex, Tag 03D7, lemma-adjoint-pullback-pushforward-modules,
lines 1197 onward; Tag 03EK, section-tensor-product, lines 3551 onward;
sites-cohomology.tex, Tag 06YY, lemma-derived-base-change, lines 3585 onward;
derived.tex, Tag 0FND, lemma-pre-derived-adjoint-functors-general, lines 9517 onward.
The definition node does not assert existence or choose a model. It reuses
`Sheaf.CategoryTheory.SystemScalarModel` without adding or modifying a module.

`def-weil-pbc-system-scalar-coherence` records the four existing restriction and
derived scalar comparison definitions. Restriction is identity on sections with the
specified coefficient-map equality. Derived unit and composition are the published
`Adjunction.leftAdjointUniq` constructions from these actual restriction comparisons.
The definition node asserts no representative formula theorem. The sources are the
ordinary tensor unit/associativity conventions in Stacks 03EK and the derived
adjunction in 0FND, applied in the retained scalar-extension steps 6-7. It reuses
`Sheaf.CategoryTheory.SystemScalarCoherence` without modifying its module.

For both nodes, DAG `rg -l` searches for the actual declaration names found only the
existing scalar theorem nodes and their consumers; no definition node records these
notions. `tools/blueprint_refs.py search 'scalar model'` and `search 'scalar coherence'`
each returned zero blueprint nodes; `ancestor` gave `prop-weil-pbc-scalar-extension`.
The two new node ids are absent on the live base. The existing theorem modules are
reused through `existing: true` records, as the return explicitly requests.

The six new `msearch.py` searches are recorded with their exact queries and actual
results in the nodes' `mathlib_searches`. For the model, LeanSearch returned ordinary
module adjunction and restriction declarations; LeanFinder returned sheafification,
pure-tensor unit and sheaf pullback facts; Mathlib grep for
`SystemScalarModel|systemModelTmul` returned zero hits. For coherence, LeanSearch
returned general left-adjoint uniqueness and derived-adjunction results, LeanFinder
returned general derived-adjunction units and counits, and Mathlib grep for the four
specific map names returned zero hits. The same regexes were run with `rg` in
`lean/WeilConjectures` and `lean/Sheaf`: no upstream declaration duplicates them,
and the exact existing definitions are in the two unchanged project modules.
These searches justify adding DAG definition records, not duplicate Lean definitions.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
