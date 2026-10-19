## Worker report

Repair of the return on immutable head f07053729877. This delivery is stage 2 and
contains the new module `Sheaf.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect`,
its theorem `DerivedCategory.dualizable_iff_isPerfectRingComplex`, and the item's Lean
record. The theorem's whole proof is `sorry`; no theorem has been proved and no new
definition is needed.

The node was copied afresh from the current shared newtargets-dag source. Only `lean`
was added. In particular, proof Steps 3 and 6 retain `lem-weil-pbc-flat-tensor-exact`,
`proof_deps` retains that node, and `reviewed` is unchanged. The obsolete stage-1 report
is replaced by this stage-2 report. No split, proof plan, or reviewed note is reverted.

Source read: `literature/stacks-project/more-algebra.tex`, lemma-have-dual-derived,
Tag 0FNS, including both directions of the proof. The theorem matches the node's
explicit evaluation/coevaluation convention. The source's converse has a typographical
order error in its initial epsilon arrow; its displayed triangle diagram and the node
both use evaluation from the dual tensor Q, which is the convention stated here.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Arbitrary commutative ring A | `{A : Type u} [CommRing A]` |
| Ordinary unbounded D(A) | `[HasDerivedCategory.{w} (ModuleCat.{u} A)]`, `Q : DerivedCategory (ModuleCat.{u} A)` |
| Derived tensor | The existing K-flat monoidal instance, written `⊗`, with no extra monoidal-structure hypothesis |
| Unit A[0] | `𝟙_ (DerivedCategory (ModuleCat.{u} A))`, canonically identified by `DerivedCategory.singleFunctorObjUnitIso` with the degree-zero embedding of the module unit A |
| Some dual Q^vee | `∃ (D : DerivedCategory (ModuleCat.{u} A))` |
| Evaluation Q^vee tensor Q to A[0] | `ev : D ⊗ Q ⟶ 𝟙_ (DerivedCategory (ModuleCat.{u} A))` |
| Coevaluation A[0] to Q tensor Q^vee | `coev : 𝟙_ (DerivedCategory (ModuleCat.{u} A)) ⟶ Q ⊗ D` |
| Triangle on Q | `(λ_ Q).inv ≫ coev ▷ Q ≫ (α_ Q D Q).hom ≫ Q ◁ ev ≫ (ρ_ Q).hom = 𝟙 Q` |
| Triangle on Q^vee | `(ρ_ D).inv ≫ D ◁ coev ≫ (α_ D Q D).inv ≫ ev ▷ D ≫ (λ_ D).hom = 𝟙 D` |
| If and only if Q is perfect | `↔ IsPerfectRingComplex Q` |
| Bounded finite-projective representative | The recorded predicate expands as a complex P, integer bounds a,b, strict lower/upper support, projective and finite terms in every degree, and `Nonempty (Q ≅ DerivedCategory.Q.obj P)` |
| No Noetherian or nonzero-ring hypothesis | Neither `IsNoetherianRing` nor `Nontrivial` occurs in the signature |

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`. This is the recorded ordinary derived
  category, not the condensed or a bounded derived category.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, the
  recorded signed total tensor of `def-pc-tensor-complex-sheaves`; it is imported publicly.
  The module tensor is its one-object-site specialization.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, imported publicly and used without a copy.
  Its full definition was read, including the independent localization universe w.
- The transitive public upstream interface
  `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`:
  `DerivedCategory.hasDerivedMonoidalCategory`; and
  `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`:
  its `MonoidalCategory (DerivedCategory C)` instance. These derive the homotopy
  tensor via K-flat resolutions for arbitrary localization universe w. Thus this is
  the derived total tensor required by the node, not ordinary tensor of arbitrary
  representatives. The homotopy tensor comes from the signed total tensor of complexes.
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`:
  `DerivedCategory.singleFunctorObjUnitIso`, whose full signature identifies the image
  of the module tensor unit in degree zero with the derived tensor unit. It has
  independent localization universe, as read in its containing General section.

All recorded proof dependencies with published side modules are imported without
`public`: `DerivedFreeModuleHomology`, `DerivedTensorSecondFactorFunctor`,
`KFlatResolutionIndependentCoefficients`, `BoundedFlatKFlat`, `PerfectRingSummand`, and
`SiteDerivedTensorDescentIndependentCoefficients`. The Mathlib proof leaves are already
available transitively. The nodes `lem-sfb-subcategory-left-resolution`,
`lem-zl-bounded-free-finite-subcomplex`, and
`lem-zl-bounded-projective-complex-dual-pairing` have no recorded published modules to
import. They are proof prerequisites only, not missing statement objects. The theorem
docstring carries all seven current proof steps, including the reviewed flat-tensor
citations and the split-triangle argument.

Edge cases checked by reading the complete signature and predicate: the zero ring is
included (`CommRing` allows 1=0); Q=0 has a zero dual and a bounded zero model; A[0]
and shifts of finite projective modules have the usual duals. Rings with no Noetherian
hypothesis, including polynomial rings in infinitely many variables, remain allowed.
No boundedness is assumed of Q or D on the left. The existentially quantified bounded
model appears only on the right. The universes u and w are separately bound, so the
standard larger-universe localization is included. Both triangle composites have the
correct source and target, checked by Lean without additional assumptions.

Searches made (2026-10-18):

- `msearch.py ... leanfinder`, query: "An object in the unbounded derived category of
  modules over any commutative ring is dualizable if and only if it is isomorphic to a
  bounded complex of finitely generated projective modules". Eight hits, about
  t-structure bounds and K-projectivity; no characterization matching this node.
- `msearch.py ... leansearch`, query: "An object in the derived category of modules
  over a commutative ring has a dual for derived tensor if and only if it is perfect".
  Eight hits on module duals and perfect pairings, not the derived equivalence.
- `msearch.py ... loogle`, query: `ExactPairing, DerivedCategory`. Zero hits; the remote
  index reported unknown identifier ExactPairing. Its actual Mathlib declaration was
  read locally in `CategoryTheory/Monoidal/Rigid/Basic.lean` instead.
- `msearch.py ... grep`, regex `isPerfect.*[Dd]ual|[Dd]ual.*[Pp]erfect`. Five Mathlib hits
  about topological/perfect pairings; none about this derived characterization.
- `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for
  `IsPerfectRingComplex|isPerfect_iff_isDualizable|ringDerivedTensor|moduleDerivedTensor`,
  and for the exact node id. The existing upstream
  `DerivedCategory.isPerfect_iff_isDualizable` in Perfect/Dualizable.lean requires
  `IsNoetherianRing` and fixes the localization universe to u. Its signature and
  docstring were read; it cannot serve as an existing match and is not used.
- `rg` over `/home/ubuntu/weil-newtargets-shared/lean/Sheaf` for those predicates and
  tensor names found the recorded general predicate and perfect-object consumers,
  but no arbitrary-ring equivalence. Searches for the new declaration name in both
  trees found no collision. The existing perfect trace only constructs a dual from
  perfectness and uses the specialized universe; it does not state the converse.

Validation: prescribed `scompile.py NQ lem-zl-ring-derived-dualizable-perfect` on the
module succeeded, compiling both sandbox and actual module paths, with no errors or
warnings (4.3 and 7.3 seconds respectively). No direct Lean/Lake/global build was run.
There are no statement disputes, corrections, new nodes, or dependency-module repairs.

## Second reading by NQ

A separate reading pass by this worker compared the current node, source, Lean file,
and recorded signature after compilation. No second agent was started, as the dispatch
brief explicitly prohibits that; the maintainer's independent review remains external.

A is arbitrary `CommRing A`, with no Noetherian or nonzero-ring binder. Q is in the
ordinary unbounded module derived category and w is independent of u, matching the
recorded perfect predicate. The tensor instance is the existing derived K-flat tensor,
not a new arbitrary monoidal datum. Its unit is canonically A[0]. D is existential,
evaluation has the exact order D tensor Q, and coevaluation has the order Q tensor D.
The first composite starts at Q, passes through (Q tensor D) tensor Q and then
Q tensor (D tensor Q), and returns to Q. The second starts at D, passes through
D tensor (Q tensor D) and then (D tensor Q) tensor D, and returns to D. Each is required
to equal its identity. The right side is precisely the dependency's
`IsPerfectRingComplex Q`, so it says bounded finite projective model, without a
cohomological finiteness substitution. The explicit maps avoid any ambiguity between
Mathlib's left/right dual naming conventions and the node's specified map order.

No mismatch was found in that reading. The return's H1/H11 defects are repaired by the
new compiling Lean module, Lean record, and both stage-2 report sections. A6/A7+H2 are
repaired by taking the current merged node verbatim outside `lean`, in particular
preserving the Step 3 and Step 6 fix and the associated reviewed note. Only the theorem
proof is postponed, and the docstring gives the complete seven-step DAG proof plan.
