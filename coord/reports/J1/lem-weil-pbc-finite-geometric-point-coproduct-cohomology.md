## Worker report

The module states `AlgebraicGeometry.finite_geometric_point_coproduct_cohomology`.
It uses an algebraically closed field `k`, a finite index type `I`, the scheme coproduct
`∐ fun _ : I => Spec (.of k)`, an abelian étale sheaf `F`, and chosen geometric points
`c i` equal to the canonical coprojections. The first conjunct renders the clause
`H^q(C,F)=0` for every natural `q > 0` as `IsZero` of
`AlgebraicGeometry.Etale.cohomology` applied to `F` in degree zero. The second conjunct
renders the degree-zero canonical identification with the finite product of geometric
stalks as a `Nonempty` categorical isomorphism to the limit of the discrete stalk family.
The `hc` hypothesis records that each chosen point is the point on its corresponding
summand.

Dependency declarations used: `CategoryTheory.Sheaf` and
`AlgebraicGeometry.Scheme.smallEtaleTopology` (Mathlib record for
`def-weil-pbc-abelian-etale-sheaves`); `CategoryTheory.GrothendieckTopology.Point.sheafFiber`
and `AlgebraicGeometry.Scheme.pointSmallEtale` (Mathlib record for
`def-weil-pbc-geometric-stalks`); `AlgebraicGeometry.Etale.cohomology` (record for
`def-weil-pbc-etale-cohomology`); Mathlib's scheme coproduct instance and
`Sigma.ι` (record for `lem-weil-pbc-scheme-coproduct-family`); and
`AlgebraicGeometry.AlgebraicClosure`/`IsAlgClosed` (record for
`def-weil-algebraic-closure`).

Edge cases checked: `I` may be empty (the coproduct and discrete limit are empty),
`I` may be a singleton (the statement specializes to the geometric-point result), and
positive degree is restricted by `q > 0` exactly as in the node. The finite index is
represented by `[Finite I]`, while the categorical limit exists for the discrete family.

Searches made: `msearch.py J1 lem-weil-pbc-finite-geometric-point-coproduct-cohomology
leanfinder "etale cohomology of finite disjoint union of spectra of algebraically closed
fields is product of stalks and vanishes in positive degrees"` found only coproduct
presheaf and stalk declarations; `msearch.py ... loogle "CategoryTheory.Sheaf.H"` found
no matching cohomology theorem; grep of Mathlib for finite coproduct/cohomology and grep
of `WeilConjectures/` found no exact declaration. No `STATEMENT-DISPUTED` issues.

## Earlier second reading (a previous round; superseded)

Read the node statement, all five statement dependencies, and each recorded declaration.
The Lean binders match the algebraically closed field, finite index, coproduct scheme,
etale sheaf, chosen geometric points, and their canonical-summand equations. The two
conclusion clauses match positive-degree vanishing and the degree-zero finite product of
geometric stalks. The edge cases and source proof dependencies are recorded above.

## Second reading by J1

Independent second reading on 2026-10-11. I opened the item node, its Lean module,
all five statement-dependency nodes, and the recorded source declarations. The Stacks
source was absent from the read-only clone, so I fetched the upstream
`etale-cohomology.tex` into `scratchpad/etale-cohomology.tex` and read the labels for
03QT, 03QU, 03QQ and 0A5B. The point calculation assumes a field and a geometric point;
for algebraically closed k the absolute Galois group is trivial. The first paragraph
of 0A5B reduces a finite disjoint union componentwise. Its later prime-coefficient
and smooth-curve hypotheses are not hypotheses of the point calculation used here.

Objects, hypotheses and conclusions, matched independently:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
  Verdict: exact. Read `IsAlgClosed` in Mathlib/FieldTheory/IsAlgClosed/Basic.lean:
  all polynomials split, equivalently every nonconstant polynomial has a root.
  No algebraic extension of another field is required by this item.
- Finite set I: `(I : Type u) [Finite I]`. Verdict: exact, with no nonemptiness
  assumption or chosen enumeration. The scheme coproduct dependency records indices
  small in the universe of the schemes; any finite set can be represented here.
- Scheme C, the coproduct of copies of Spec k: `∐ fun _ : I => Spec (.of k)`.
  Verdict: exact. Read Mathlib/AlgebraicGeometry/Limits.lean's discrete-colimit
  instance, `Sigma.ι`, and disjointness of coprojection ranges. No auxiliary scheme
  with an unverified coproduct property is substituted.
- Abelian etale sheaf F: `Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}`.
  Verdict: exact. Read Mathlib's `smallEtaleTopology`, `Sheaf`, and the dependency
  record; these encode the small etale site and the abelian sheaf condition.
  No torsion, constructibility or finite-generation assumption is imposed.
- Geometric point on summand i: `c i : Spec (.of k) ⟶ C` and
  `hc : ∀ i, c i = Sigma.ι (fun _ : I => Spec (.of k)) i`.
  Verdict: these fix the chosen geometric point to the indicated summand, as required.
  Since k is already algebraically closed, its spectrum is a geometric point.
- Stalk at that point: `(pointSmallEtale (c i)).sheafFiber.obj F`.
  Verdict: exact. Read `pointSmallEtale` in EtalePoint.lean and `sheafFiber` and
  `toPresheafFiber` in Point/Basic.lean. The point's fibre consists of lifts of c i,
  and the sheaf fibre is the colimit over their opposite category of elements.
- Vanishing for every positive q: the first conjunct quantifies `q : ℕ`, `q > 0`
  and states `IsZero` of `Etale.cohomology ... (q : ℤ)` on
  `(DerivedCategory.singleFunctor _ 0).obj F`. Verdict: exact. I read the dependency's
  `Etale.cohomology`: it is homology of total right derived global sections.
  Only the input sheaf is placed in degree zero; the cohomology degree is q.
- The canonical map H^0(C,F) to the finite product of the stalks is invertible:
  the repaired second conjunct states `IsIso` of the explicit composite.
  `Functor.homologyRightDerivedFunctorObjSingleFunctorIso (Sheaf.Γ ...) F 0`
  identifies total derived degree-zero cohomology with classical R^0Γ;
  `Functor.rightDerivedZeroIsoSelf` identifies R^0Γ with Γ;
  `F.ΓRes (op (Scheme.Etale.mk (𝟙 C)))` gives sections at C; and
  `Pi.lift` of `(pointSmallEtale (c i)).toPresheafFiber` gives the canonical germs.
  The pointed neighbourhood has lift `Over.homMk (c i) (Category.comp_id (c i))`.
  Verdict: exact map, with target the categorical finite product of the recorded
  geometric stalks. I opened both derived-comparison declarations in
  PlusCompatibility.lean and Mathlib/CategoryTheory/Abelian/RightDerived.lean, and
  the global-section restriction declaration in Sites/GlobalSections.lean.

Mismatch found and repaired: the previous `Nonempty (H^0 ≅ product)` asserted only
existence of an unspecified isomorphism. It did not say that the canonical map is
invertible. Replaced it by the explicit `IsIso` composite above; imported the existing
PlusCompatibility module; qualified `Scheme.Etale.mk` to avoid confusion with the
scheme-morphism property `AlgebraicGeometry.Etale`. Added the standard file header. Extended the proof docstring to
explain the degree-zero comparison. Updated `lean.statement` verbatim from the file.
The informal node is correct and was not changed. The earlier worker report's claim
that unspecified isomorphism renders canonicity is superseded by this repair.

Edge cases: I empty gives the empty scheme and empty product, the zero abelian group;
no `[Nonempty I]` binder excludes it. I singleton is the point calculation. The zero
sheaf is allowed and all terms remain defined. q = 0 is covered by the second conjunct
and is deliberately excluded from positive-degree vanishing. No characteristic or
prime is fixed. Universe u is explicit and can be enlarged to contain k and the finite
index; coefficients are in the dependency's recorded universe u+1. There are no
unbound variables or universes, file-local instances, private notions, hidden let
binders, hollow definitions or additional theorem proofs. The only theorem proof is
`sorry`, with the original two-step natural-language proof and its dependency IDs.
There are no new nodes or dependency modules to review, and no statement correction.

Independent searches (different wording from the worker):

- `msearch.py ... leanfinder "canonical map from global sections of an etale sheaf to
  product of geometric stalks is isomorphism for finite union of points"`: scheme
  gluing and topological stalk-detection results; no exact theorem.
- `msearch.py ... leanfinder "cohomology of finite coproduct of spectra of algebraically
  closed fields vanishes in positive degrees"`: singular homology of disconnected
  spaces, finite sigmaSpec, and cotangent cohomology; no exact theorem.
- Loogle `GrothendieckTopology.Point.toPresheafFiber` and
  `IsIso (CategoryTheory.Limits.Pi.lift _)` were not recognized by its index;
  the fully qualified `CategoryTheory.IsIso` query returned the general IsIso API,
  no finite geometric-point cohomology result. The needed germ declaration was
  instead verified directly in the pinned Mathlib source.
- `rg` over pinned Mathlib/AlgebraicGeometry, WeilConjectures and repository lean/Sheaf
  for `finite_geometric_point`, `finite.*(stalk|cohomology)` and
  `cohomology.*coproduct`: no existing declaration of this statement. The related
  `zeroDimensional_sections_stalks` has separated finite-type zero-dimensional
  k-scheme hypotheses and only a sections calculation; it is not this theorem.
  Searches of the source's right-derived-functor modules found the existing canonical
  comparison maps used in the repair, so no definition was duplicated.

Validation: the repaired module passed `scompile.py` under the default time limit,
with no errors or warnings. All lines are at most 100 characters.

Further search checks: LeanSearch for "The canonical map from zeroth etale cohomology
of a finite union of geometric points to the product of stalks is an isomorphism" was
unavailable (Internal Server Error), recorded by msearch; no negative verdict is inferred
from that outage. msearch grep in Mathlib/AlgebraicGeometry for
`finite.*coproduct.*cohomology|cohomology.*coproduct|geometric.*point.*cohomology`
returned zero hits. The LeanFinder and direct source searches above provide the
fallback. The initial delivery dry run passed preflight and server compilation.
