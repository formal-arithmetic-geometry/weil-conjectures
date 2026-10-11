## Worker report

The module `Sheaf.AlgebraicGeometry.RationalFunctionsGenericStalks` states
`AlgebraicGeometry.Scheme.rationalFunctions_generic_stalks`, with `sorry` as its only proof.
The item introduces no definition. There is no statement correction. A dependency module
repairs the recorded rational-function ring declaration under rule (B), as detailed below.

Hypotheses and clauses, in the order of the node:

- A scheme X: `X : Scheme.{u}`, with an explicitly bound arbitrary universe `u`.
- Finitely many irreducible components X_1,...,X_n: `n : ℕ` and
  `components : Fin n ≃ {Z : Set X // Z ∈ irreducibleComponents X}`.
  The equivalence expresses an exhaustive enumeration without repetitions, as assumed in
  the node's proof; it imposes no extra geometric hypothesis. Components are underlying
  subsets, not subschemes.
- Their generic points: `η : Fin n → X` and
  `hη : ∀ i : Fin n, IsGenericPoint (η i) (components i).val`.
  This is closure of the singleton equal to that component. Membership and uniqueness
  follow from Mathlib's generic-point definition and the scheme's sobriety and T0 instances.
- Every dense open contains every η_i: the witness
  `hDense : ∀ (U : DenseOpens X) (i : Fin n), η i ∈ U.val`.
  The existential packages a proof of this universal clause, which then supplies the
  membership arguments needed by the germ maps.
- The map R(X) to the product of generic stalks is a well-defined ring isomorphism:
  the witness `e : (X.rationalFunctionRing : Type u) ≃+*
  ((i : Fin n) → X.presheaf.stalk (η i))`.
  The dependent function ring is exactly the finite product of the component stalks.
- The stated formula on representatives: for every dense open U, section f and index i,
  `e ((colimit.ι (denseOpenSections X) (op U)) f) i =
  X.presheaf.germ U.val (η i) (hDense U i) f`.
  The colimit coprojection is the class [(U,f)] from the dependency's definition.
  Thus e is the germ map, not an unspecified abstract isomorphism. An isomorphism on
  the colimit with these values states well-definedness and the ring laws together with
  injectivity and surjectivity; no data definition or extra well-definedness theorem is needed.
- If X is integral: the implication `IsIntegral X → ...`.
- Then n=1: `n = 1`.
- Then X_1=X: `∀ i : Fin n, (components i).val = Set.univ`.
  With n=1 this is exactly the sole component equaling the whole underlying space.
- R(X) and O_{X,η} are fields: `IsField (X.rationalFunctionRing : Type u)` and
  `∀ i : Fin n, IsField (X.presheaf.stalk (η i))`.
  `IsField` records the field property of the already specified rings without selecting
  new field structures or replacing their ring operations.
- R(X) ≅ O_{X,η}: for each index, the witness
  `ei : (X.rationalFunctionRing : Type u) ≃+* X.presheaf.stalk (η i)` and
  `∀ r : X.rationalFunctionRing, ei r = e r i`.
  This explicitly identifies the single-stalk equivalence with the same germ map.

Dependencies read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; read their full definitions and docstrings.
- `def-weil-irreducible-components`: `irreducibleComponents`,
  `Mathlib.Topology.Irreducible`, the maximal irreducible subsets (read definition/docstring).
- `def-sc-generic-point`: `IsGenericPoint`, `Mathlib.Topology.Sober`,
  closure of a singleton (read definition/docstring).
- `lem-sc-scheme-sober`: the scheme T0 and QuasiSober instances,
  `Mathlib.AlgebraicGeometry.Properties`, and `IsGenericPoint.eq`,
  `Mathlib.Topology.Sober`. These explain why supplied generic points need no uniqueness binder.
- `def-sc-rational-functions`: `AlgebraicGeometry.Scheme.rationalFunctionRing`,
  `Sheaf.AlgebraicGeometry.RationalFunctionRing` (the dependency module delivered here).
  It imports `Sheaf.AlgebraicGeometry.RationalFunctions` to reuse its `DenseOpens` and
  `denseOpenSections`. The full original module was read. Its recorded ring declaration
  was unusable at arbitrary universes; see the dependency-module section.
- `def-weil-pbc-module-stalk`: `TopCat.Presheaf.stalk` and `germ`,
  `Mathlib.Topology.Sheaves.Stalks`, used for the ring-valued structure presheaf.
  Read their full signatures and docstrings, and `exists_germ_eq` and `germ_eq`.
  Also inspected `PresheafOfModules.germ_ringCat_smul` and the module-stalk instance
  in `Mathlib.Algebra.Category.ModuleCat.Stalk`. The module part of this dependency
  is not needed here: this statement uses only the explicitly recorded ring-stalk clause.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`; read full definition/docstring. Imported directly.

Edge cases checked before writing:

- Empty scheme: n=0, no generic-point obligations, and the target product is the zero ring
  (functions on the empty index type). The rational-function ring is likewise the zero ring.
  The integral implication is vacuous, since an integral scheme is nonempty.
- Integral schemes: there is exactly one component, equal to the whole space. No positivity
  hypothesis on n is added to the general case.
- Reducible schemes with nilpotents: no reducedness is assumed and no residue fields replace
  the stalks; the generic stalks need not be fields outside the integral implication.
- Intersecting components are allowed. Finite enumeration, not disjointness of components,
  is the hypothesis; disjoint opens arise only in the natural-language proof.
- Arbitrary characteristic and arbitrary universe u: no field, Noetherian, separation,
  dimension or finite-type hypothesis is introduced. Fin n indexes any finite enumeration.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leansearch "ring rational functions scheme isomorphic product stalks generic points"`:
  service unavailable (Internal Server Error), no verdict inferred from the outage.
- `msearch.py ... leanfinder "rational functions on scheme with finitely many irreducible components product of generic stalks"`:
  eight hits, all about `Scheme.functionField`, `germToFunctionField`, its field instance,
  or fraction-ring properties for integral schemes. No product/rational-functions statement.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.functionField, IsGenericPoint"`:
  zero hits.
- `msearch.py ... grep "rationalFunctions|rational.functions|Pi.*stalk" AlgebraicGeometry`:
  five unrelated Mathlib hits (residue-field compositions, elliptic curves, flatness).
- `rg` for `rationalFunctions|lem-sc-rational-functions-generic-stalks` in the source project's
  `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  only the project's definition module `RationalFunctions.lean` (lines 53 and 59).
  Wider generic/stalk searches were also inspected; no product-of-generic-stalks statement.
- Read all of `Mathlib.AlgebraicGeometry.FunctionField`: it defines only the stalk at
  the generic point of an irreducible scheme. Its integral field instance covers the
  field property of that stalk, but does not identify the project's colimit ring with it.

Source checked: the local `literature/stacks-project/morphisms.tex` is absent on this machine,
so opened https://stacks.math.columbia.edu/tag/01RV instead. Its first and third assertions
and displayed colimit computation agree with the node. The reduced/residue-field assertion
is deliberately not part of this node and is not added. No STATEMENT-DISPUTED or node fault.

Validation: `scompile.py` compiled the two modules together in dependency order on the
server in 1.9 seconds, exit code 0, with no warnings.
`deliver2.py M1 lem-sc-rational-functions-generic-stalks --no-push` printed
`OK (dry run)`: the commit compiles and passes preflight except for the second reading,
which is reserved for the independent second reader. Nothing was pushed.

## Dependency modules

`def-sc-rational-functions`: the recorded declaration `Scheme.rationalFunctions` has
`X : Scheme.{0}` because its result was annotated simply `CommRingCat` without a universe
binder. The first server compile rejected `Scheme.{u}` in every occurrence of that ring.
Restricting the item to small schemes would exclude cases of the node. Therefore rule (B)
applies: `Sheaf.AlgebraicGeometry.RationalFunctionRing` defines
`rationalFunctionRing (X : Scheme.{v}) : CommRingCat.{v}` as
`colimit (denseOpenSections X)`. This is the exact same node's colimit of section rings
on dense opens, with restriction maps, so it includes the stated equivalence-class ring
operations. All previous auxiliary notions (`DenseOpens`, their dense intersection,
and `denseOpenSections`) are reused by importing the previous module, not copied.
The dependency node copy changes only its `lean` record and explains the universe issue
in `lean.note`. The dependency definition contains no sorry or new proof.

The earlier search results also apply to this dependency: the only ring of rational
functions for arbitrary schemes found was the recorded project definition, whose universe
limitation caused the compile failure. The new declaration names `rationalFunctionRing` and
`rationalFunctions_generic_stalks` were searched with `rg` across Mathlib, upstream
WeilConjectures, project Sheaf and `dag/lean_names_upstream.json`, with no existing matches.

## Second reading by M1

Independent reading on 2026-10-11: opened the delivered node, both delivered modules,
all seven statement-dependency nodes and their recorded declarations, and the original
`Sheaf.AlgebraicGeometry.RationalFunctions` module. The statement says exactly what the
node says. No Lean or node repair was needed; this reading adds the independent review.

Source: the repository has no local Stacks .tex files. Obtained the upstream Stacks
`morphisms.tex` into this sandbox's `scratchpad/morphisms.tex` and read the section opening
at `section-rational-maps`, definitions `definition-rational-map`,
`definition-rational-function`, `definition-ring-of-rational-functions`, and the complete
statement and proof of `lemma-integral-scheme-rational-functions` (lines 12705-12740).
Also opened [01RV](https://stacks.math.columbia.edu/tag/01RV),
[01RT](https://stacks.math.columbia.edu/tag/01RT), and
[01RU](https://stacks.math.columbia.edu/tag/01RU). The section begins with an arbitrary
scheme: no base field, reducedness, Noetherian, separation, dimension or finite-type
hypothesis is assumed throughout. The reduced/residue-field assertion of 01RV is outside
this node. There is no statement correction and no new definition node to review.

My object/hypothesis/conclusion checklist, matched against the Lean:

1. Arbitrary scheme X: `(X : Scheme.{u})`, with `universe u` explicitly bound. PASS.
   Opened `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` extends `LocallyRingedSpace` with
   the local affine-neighbourhood condition, exactly `def-pc-scheme`.
2. Finitely many irreducible components X_1,...,X_n: `(n : ℕ)` and
   `(components : Fin n ≃ {Z : Set X // Z ∈ irreducibleComponents X})`. PASS.
   Read `irreducibleComponents := {s | Maximal IsIrreducible s}` and `IsIrreducible`
   in `Mathlib.Topology.Irreducible`; the components are precisely those of
   `def-weil-irreducible-components`, rather than affine charts or component subschemes.
   The equivalence records all distinct components, in the enumeration of the node and
   its proof, and permits n=0. It adds neither disjointness nor geometric finiteness.
3. Generic points η_i of those components: `(η : Fin n → X)` and
   `(hη : ∀ i : Fin n, IsGenericPoint (η i) (components i).val)`. PASS.
   Opened `Mathlib.Topology.Sober`: `IsGenericPoint` means closure of the singleton equals
   the given subset; `IsGenericPoint.mem` entails the node's η_i ∈ X_i. Read the scheme
   T0 and QuasiSober instances in `Mathlib.AlgebraicGeometry.Properties` and
   `IsGenericPoint.eq`: the uniqueness cited in the node follows from those instances,
   without an additional hypothesis. Generic-point existence is available from sobriety.
4. Every dense open contains every η_i: the conclusion starts
   `∃ hDense : ∀ (U : DenseOpens X) (i : Fin n), η i ∈ U.val`. PASS.
   Opened the reused `DenseOpens` definition: it is the subtype of `X.Opens` satisfying
   `Dense (U : Set X)`. Its proof is a conclusion, not an assumption. Packaging it as
   an existential supplies the dependent membership argument in the germ formula.
5. R(X) is the rational-function ring of the dependency: `X.rationalFunctionRing`. PASS.
   Read both the dependency node and its entire replacement module, as discussed below.
6. Product of structure-sheaf stalks: `((i : Fin n) → X.presheaf.stalk (η i))`. PASS.
   Opened `TopCat.Presheaf.stalk` and `germ` in `Mathlib.Topology.Sheaves.Stalks`:
   they are the ring-valued colimit over open neighbourhoods and its coprojections.
   This is the ring-stalk clause explicitly carried by `def-weil-pbc-module-stalk`;
   no module stalk, residue field or étale stalk is substituted. The Pi ring is the
   finite product of these same rings.
7. The specified map is well defined and a ring isomorphism:
   `∃ e : (X.rationalFunctionRing : Type u) ≃+* ...`, together with
   `∀ (U : DenseOpens X) (f : Γ(X, U.val)) (i : Fin n),
   e ((colimit.ι (denseOpenSections X) (op U)) f) i =
   X.presheaf.germ U.val (η i) (hDense U i) f`. PASS.
   Read `denseOpenSections`: it restricts `X.presheaf` along the opposite dense-open
   inclusion, so the coprojection is precisely [(U,f)]. The ring equivalence and its
   values on every representative assert the node's germ map, its well-definedness,
   ring laws and bijectivity; an arbitrary unrelated isomorphism would not satisfy
   this clause. All opens, sections and indices are universally quantified after e.
8. Additional integral hypothesis only for the last clause: `(IsIntegral X → ...)`.
   PASS. Opened the recorded `IsIntegral` class and
   `isIntegral_iff_irreducibleSpace_and_isReduced`; its nonempty/domain formulation
   is the exact notion of `def-pc-integral-scheme`.
9. In the integral case there is one component and it equals X:
   `n = 1 ∧ (∀ i : Fin n, (components i).val = Set.univ)`. PASS.
   Given n=1 the universal equality names precisely X_1=X; it asserts no extra clause.
10. In that case R(X) and the generic local ring are fields:
    `IsField (X.rationalFunctionRing : Type u)` and
    `∀ i : Fin n, IsField (X.presheaf.stalk (η i))`. PASS.
    These assert a property of the existing rings, preserving their operations.
11. The same germ map identifies R(X) with the single generic stalk:
    for each i, `∃ ei : ... ≃+* X.presheaf.stalk (η i),
    ∀ r : X.rationalFunctionRing, ei r = e r i`. PASS.
    With n=1 this is the node's R(X) ≅ O_{X,η}; the agreement with e preserves the
    specified identification. Its witnesses exist under precisely the integral hypothesis.

Dependency-module reading (H13): `def-sc-rational-functions` changes only its `lean`
record. The replacement `rationalFunctionRing (X : Scheme.{v}) : CommRingCat.{v}` is
`colimit (denseOpenSections X)` without a hole or a proof. That is the dependency's
section-equivalence ring with restriction operations, as explicitly given in the second
colimit equality of 01RV; it needs no assumption on X. It reuses `DenseOpens`,
`denseOpensInclusion` and `denseOpenSections` from the old module rather than duplicating
those notions. Independently compiled `scratchpad/UniverseCheck.lean` on the server with
`pp.universes`: the old `Scheme.rationalFunctions` indeed takes `Scheme.{0}` and returns
`CommRingCat.{0}`, whereas `DenseOpens` and `denseOpenSections` are universe polymorphic.
Thus the recorded old ring is unusable for the arbitrary-universe node, and rule (B)
justifies this dependency module. The new record's `note` explains precisely that fault.

Edge cases: n=0 and the empty scheme are admitted. The empty Pi is the zero ring,
and the section-colimit ring of the empty scheme is the zero ring; no dense-open/generic
point obligations become an illicit nonemptiness assumption. A nonempty scheme has a
component, so an empty enumeration cannot satisfy the component equivalence. Integral
schemes are nonempty, making the integral implication vacuous for the empty scheme and
ensuring the single component in the integral case. Nonreduced reducible schemes remain
allowed; their generic local rings are not asserted to be fields. Intersecting components
are allowed. No characteristic or base field restriction appears. The explicit scheme/ring
universes u and v are arbitrary, and the use of Fin n covers every finite enumeration.
No extra variable or universe is left unbound.

Independent searches, using different queries from the first worker (2026-10-11):

- `msearch.py ... leanfinder "finite irreducible components rational sections dense opens ring equivalence generic local rings"`:
  eight hits: `Scheme.functionField`, its field instance and affine fraction-ring
  statements, a scheme sobriety instance, an affine-spectrum irreducibility instance,
  an algebra instance, and an unrelated quasi-finite basic-open statement. Opened
  `Mathlib.AlgebraicGeometry.FunctionField`: its definition is only the stalk at the
  generic point for an irreducible scheme; none supplies R(X) or the product equivalence.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme, RingEquiv"`: zero hits.
- `msearch.py ... leansearch "scheme rational section ring dense open subsets product generic local rings"`:
  service unavailable (Internal Server Error). Recorded as an outage, not as evidence
  that no declaration exists.
- `rg` across all upstream `WeilConjectures`, all Mathlib, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `rationalFunctionRing`, `rationalFunctions_generic_stalks`,
  `denseOpenSections`, `rationalFunctions`, `01RV`, and this item id: only the old project's
  rational-functions definition module, no existing statement or usable replacement ring.
- Independently searched `colimit.*stalk|stalk.*colimit|[Pp]roduct.*stalk|stalk.*[Pp]roduct`
  in upstream `WeilConjectures`, Mathlib algebraic geometry and project algebraic geometry.
  Hits concern geometric/étale stalks, finite pushforwards, tensor products, or the
  irreducible function field. Opened upstream `AlgebraicGeometry/FunctionFieldLimit.lean`:
  its diagram is nonempty affine opens of an integral scheme and its result is a limit
  cone in schemes, not this rational-function ring or product-of-generic-stalks assertion.

H5/H6/H8/H9: the replacement definition has no sorry; the item's single theorem has
exactly `by sorry` and nothing was proved. Both module and declaration docstrings name
sources and the correct blueprint ids. The theorem docstring follows all six node proof
steps, including disjoint opens, dense membership, the induced germ map, locality for
injectivity, gluing for surjectivity, and the integral field step. Imports are used and
line widths are within 100. Node signatures agree with the file signatures; no node field
or Lean statement was changed in this reading. No mismatch or disputed statement found.

Second-reader validation: the server compiled both delivery modules together in dependency
order in 1.9 seconds, exit code 0, with no warnings or errors. The separate universe-check
scratch file compiled in 1.5 seconds. `deliver2.py M1 lem-sc-rational-functions-generic-stalks
--no-push` printed `OK (dry run)`: preflight passed and the delivery compiled.
