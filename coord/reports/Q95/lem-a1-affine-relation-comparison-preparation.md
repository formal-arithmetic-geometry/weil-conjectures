## Worker report

The module `Sheaf.AlgebraicGeometry.AffineRelationComparisonPreparation` states
`AlgebraicGeometry.affineRelation_comparison_preparation`, with `sorry` as its only
theorem proof. The eight small helpers in `AlgebraicGeometry.AffineRelationComparison`
construct the canonical invariant action, the two invariant-linear maps, tensor
comparison, scalar extensions and their projection to the original spectra. All
helper data and compatibility proofs are actual terms; no choice of an arbitrary
map, additional algebra structure, or hollow definition is used.

The node statement and all nine statement dependencies were read, including their
recorded declarations and source docstrings. The Stacks sources read are
`groupoids.tex`, lemma-equivalence-groupoid, Tags 03BK (1),(3), 03BM first two proof
paragraphs, and the integrality/orbit arguments carried by 03BJ and 03BL. The
finite locally free definition and standard free cover were checked in their
recorded source modules. No statement correction or dependency repair is needed.

Hypotheses and clauses, in the order of the node:

- Scheme S and affine S-schemes U=Spec A, R=Spec B: `{S : Scheme.{u}}`,
  `{A B : CommRingCat.{u}}`, `a : Spec A ⟶ S`, `b : Spec B ⟶ S`.
- The coordinate maps are `σ τ : A →+* B`; source and target are their `Spec.map`s.
  This parametrizes exactly all affine scheme morphisms, by `Spec.homEquiv`.
  `hs` and `ht` assert that they are S-morphisms. The two instance binders use
  the recorded `Scheme.Hom.IsFiniteLocallyFree`, without a degree/rank assumption.
- Identifying R(H) with an equivalence relation on U(H), for every S-scheme H:
  `hrel : ∀ H : Over S, Function.Injective (...) ∧ Equivalence (...)`.
  The injection is the endpoint map; the equivalence relation is its image.
  H-points are morphisms in `Over S`, so the S-structure is retained.
- Invariants C: exactly Mathlib's `σ.eqLocus τ`, not a new invariant definition.
  Inclusion is `(σ.eqLocus τ).subtype`; M is its spectrum; q is `Spec.map` of
  this inclusion throughout the signature. No separate arbitrary q is introduced.
- Identity, inverse and composition: the existential `e`, `i`, `c`, followed by
  `IsGroupoidScheme ... e i c`, uses the dependency's absolute laws verbatim.
  The next three equations say e, i and c are over S. The universal clause in
  `e'`, `i'`, `c'` says that any groupoid operations with these endpoints coincide.
- qs=qt: the existential proof `hq`. In diagrammatic Lean order this is
  `s ≫ q = t ≫ q`.
- Canonical affine fibre-product identification: the equation with
  `(pullbackSpecIso (σ.eqLocus τ) A A).hom` identifies `pullback.lift s t hq`
  with `Spec.map` of the constructed `comparison σ τ`. The following pure-tensor
  formula is `comparison σ τ (x ⊗ₜ y) = σ x * τ y`. Thus neither the comparison
  nor its coordinate map is an unconstrained existential.
- Finite monomorphism and closed immersion: the three conjuncts `IsFinite`,
  `Mono`, `IsClosedImmersion` of this same `pullback.lift`. Surjectivity is
  `Function.Surjective (comparison σ τ)`.
- Integral inclusion C⊂A: for each `x : A`, a polynomial `P : Polynomial C`,
  with `P.Monic` and `P.eval₂ C.subtype x = 0`, exactly the stipulated monic
  annihilator rather than merely integrality of another map.
- Surjectivity of q: `Surjective (Spec.map (CommRingCat.ofHom C.subtype))`.
  Orbit fibres: for all underlying points x,y of Spec A, equality of their
  q-images iff `∃ r : Spec B, s r = x ∧ t r = y`. These are ordinary points,
  with one arrow, not generated equivalence classes of field-valued points.
- Two finite principal-open free covers: `n : Bool → ℕ` and
  `f : (p : Bool) → Fin (n p) → A`; true selects σ, false τ. Each family
  generates the unit ideal. For every chart, the localized module is both
  `Module.Finite` and `Module.Free`. `ModuleCat.restrictScalars` selects exactly
  the σ- or τ-module structure on B. `LocalizedModule.Away (f p j)` expresses
  the module on D(f p j), equivalently the coordinate localization at σ(f p j)
  or τ(f p j). Source and target may have different covers and different ranks.
- Every flat C-algebra D: the universal binder has `[CommRing D]`, `[Algebra C D]`,
  `[Module.Flat C D]`, with no nonzero, faithful-flatness or finite-type condition.
  Rings and schemes are placed in a common arbitrary universe u; there are no
  auto-bound universe or term variables (`set_option autoImplicit false`).
- Tensor convention: the Lean types are `D ⊗[C] A` and `D ⊗[C] B`. The canonical
  commutative-algebra tensor symmetry identifies them with the node's `A ⊗[C] D`
  and `B ⊗[C] D`. This is solely the order of factors, allowing Mathlib's standard
  left-factor D-algebra instance. Thus σ_D is `d ⊗ a ↦ d ⊗ σ(a)`, and similarly
  for τ_D, constructed by `Algebra.TensorProduct.map` in `extend`/`extendedMap`.
- The new projections remain finite locally free: the first two D-conjuncts.
- The base-changed operations form a groupoid: existential `eD`, `iD`, `cD` and
  `IsGroupoidScheme` on exactly the spectra of these two tensor rings. The eD
  and iD squares and the pointwise cD square commute with `extensionProjection`.
  The cD square is stated on every composable pair, including every compatible
  proof. Naturality comes from the represented morphisms. These conditions
  specify the base-changed operations, rather than just some groupoid.
  Their D-linearity follows from the endpoint laws and the D-linear projections.
- D is the equalizer: injectivity of `algebraMap D (D ⊗[C] A)` together with
  `σ_D z = τ_D z ↔ ∃ d, algebraMap D _ d = z`. Since the canonical map is a
  ring homomorphism, this specifies exactly the equalizer as a ring, including
  its canonical inclusion, not merely an abstract isomorphism of modules.
- The comparison after base change is φ_D: the `hD` equation uses
  `pullbackSpecIso D ... ...` and the constructed `extendedComparison`.
  Its following formula on `(d ⊗ x) ⊗ (d' ⊗ y)` is
  `(d*d') ⊗ comparison σ τ (x ⊗ y)`, explicitly identifying it with φ⊗1
  under tensor symmetry and the canonical tensor rearrangement.
- The original finite free covers base change: the final conjunct uses the
  *same* `n` and `f` chosen outside the D binder. Their images under
  `Algebra.TensorProduct.includeRight` generate the unit ideal of A_D, and
  each localized B_D is finite free for the corresponding `extendedMap` action.
  No replacement or freshly chosen cover is substituted after base change.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.homEquiv` / `Spec.preimage`
  justify the coordinate-map parametrization (definitions in the signature use
  `Spec.map` directly, so no second coordinate-map definition is introduced).
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree` (finite, flat, locally finitely presented).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` and
  `Mathlib.AlgebraicGeometry.Pullbacks`: `pullback`, `pullback.lift`,
  `pullback.fst`, `pullbackSpecIso`.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, Basic and Map: `TensorProduct`,
  the pure tensors, universal map `TensorProduct.lift`, `LinearMap.rTensor`.
- `Mathlib.RingTheory.TensorProduct.Maps`: `Algebra.TensorProduct.productMap`,
  `Algebra.TensorProduct.map`, the standard `includeRight` map and its algebra.
- `Mathlib.Algebra.Ring.Subring.Basic`: `RingHom.eqLocus` and `Subring.subtype`.
- `Mathlib.RingTheory.RingHom.Flat` / `Mathlib.RingTheory.Flat.Basic`:
  `RingHom.Flat`, `Module.Flat`; the algebra-map form is the latter.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite` / Integral:
  `AlgebraicGeometry.IsFinite`, `AlgebraicGeometry.IsIntegralHom` (the ring-level
  integral conclusion is deliberately rendered by the required monic polynomials).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`: `ModuleCat.restrictScalars`;
  `Mathlib.RingTheory.Localization.Finiteness`: the finite/free localized modules.

Proof-only imports include the recorded integral-invariant and orbit-fibre modules,
finite presentation and flat projectivity, and
`WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover` with
`Module.exists_standardFreeCover_of_finite_projective`. The polynomial-norm
base-change dependency has no recorded Lean interface, so its module is not imported;
no declaration from it is needed to state this item. Every proof step, including its
base-change argument, is carried in the main theorem docstring. The neighboring
`FiniteFlatAffineRelationQuotient` was read to identify its existing helpers; it is
not imported, because it is the downstream consumer and would create an import cycle.
Its `affineRelationInvariants` is precisely Mathlib's `eqLocus`, which is used directly.

Edge cases checked before drafting and in the final reading: A=0 (then B=C=0 and
all spectra are empty), the diagonal relation, B of varying finite locally free rank,
nonreduced rings, empty finite cover when Spec A is empty, and D=0. No `Nontrivial`,
positive rank, nonempty index, reducedness, or faithful flatness assumption excludes
any of these cases. The original hypotheses force source and target to have an
identity section, but this was not added as a hypothesis.

Searches (the prescribed msearch tool logged each query):

- LeanFinder: "A finite locally free affine equivalence relation gives a unique
  groupoid with integral invariants, surjective tensor comparison and invariants
  commute with flat base change". Eight hits, affine morphism-property and generic
  category infrastructure; no matching theorem.
- Loogle: `RingHom.eqLocus, Algebra.TensorProduct.productMap,
  AlgebraicGeometry.IsGroupoidScheme`. Zero hits, with the project-only groupoid
  identifier unknown to Loogle. The first two notions were then read in Mathlib
  source; the groupoid declaration was read in its recorded project module.
- LeanSearch: "Invariants of affine finite locally free groupoid schemes commute
  with flat base change". Eight hits, including stability of flatness, finiteness,
  integrality and affineness under base change; no invariant-equalizer theorem.
- msearch grep: `groupoid.*invariant|invariant.*groupoid|affineRelation`. Nineteen
  unrelated manifold groupoid hits; no affine-relation theorem in Mathlib.
- `rg` of `lean/WeilConjectures/AlgebraicGeometry` for
  `affineRelation|affineGroupoid|eqLocus`: only unrelated unramified equalizer loci.
  The item id has no occurrence in the upstream Lean sources.
- `rg` of `lean/Sheaf/AlgebraicGeometry` for affine groupoid/relation declarations:
  read the invariant, orbit, basis-descent, polynomial-norm and parent quotient
  modules. No theorem contains this entire preparation statement. The parent is
  stronger in its final quotient assertion but does not state these preparation
  clauses as a reusable theorem.
- Exact-name grep in Mathlib, `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: no collision for the main declaration or helper
  namespace. The helpers are applications of existing constructions, all owned
  by this node under the brief's helper authorization, not independent notions.

Validation: `scompile.py Q95 lem-a1-affine-relation-comparison-preparation` compiled
both sandbox and final module namespaces successfully (4.1 s and 3.7 s), without
errors or warnings. One earlier probe required `noncomputable` on the helper
containing `Spec.map`; this was fixed. The main theorem remains entirely `sorry`.
No node fields other than `lean` are changed; there are no new nodes, statement
corrections, disputed statements, or dependency modules.

## Second reading by Q95

A separate final pass by the dispatched worker re-opened the DAG statement and the
completed Lean file. The dispatch explicitly prohibits starting other agents, so
this is a second pass by the author; the maintainer's independent delivery review
remains the independent reading. The checklist above was checked against both
files: it includes every hypothesis and every conclusion, including the uniqueness
of all three operations, S-compatibility of composition, the actual pullback
comparison, ordinary-point orbit fibres, both module structures, and the same
finite chart families after all flat base changes.

The final pass checked that the ring-map parametrization covers all given affine
morphisms, that injectivity of the endpoint map is present separately from
reflexivity/symmetry/transitivity, and that scalar extension retains the canonical
maps. It checked the cD square on all composable H-points and the formula relating
φ_D to φ, rather than merely accepting an existential groupoid or comparison. The
only presentation difference is the explicitly documented tensor symmetry
D⊗A instead of A⊗D; it changes no mathematical clause. No remaining mismatch was
found. Helper data are fully constructed and all variables/universes are bound.
