## Worker report

The module `Sheaf.AlgebraicGeometry.TangentVectorsVectorSpace` states
`AlgebraicGeometry.exists_tangentVectors_vectorSpace`, with its only proof `sorry`.
It states all clauses of the node, using existential group/module structures to express
that the displayed operations make the specified set into a vector space. There is no
new definition and no statement correction.

Hypotheses and constructions, matched individually:
- A field k: `(k : Type u) [Field k]`.
- A scheme X over k: `(X : Scheme.{u}) (p : X ⟶ Spec (.of k))`.
  No finite-type, rational-point, separatedness or characteristic hypothesis is imposed.
- A point x: `(x : X)`; its residue field κ: `let K := X.residueField x`.
- Dual numbers: `D := Spec (.of (DualNumber K))`.
- The algebra with basis 1, ε₁, ε₂ and all infinitesimal products zero:
  `TrivSqZeroExt K (Fin 2 → K)`, whose spectrum is `E`.
- The canonical point map: `b := X.fromSpecResidueField x`.
- The closed-point inclusion c induced by ε ↦ 0: `Spec.map` of `fstHom K K K`.
- The j_i induced by ε_i ↦ ε and the other ε ↦ 0: `j i` is `Spec.map` of
  `TrivSqZeroExt.map (LinearMap.proj i)`; Lean indices 0 and 1 correspond to 1 and 2.
- The sum map s: `Spec.map` of `TrivSqZeroExt.map (proj 0 + proj 1)`.
- The scaling map m_t: `Spec.map` of `TrivSqZeroExt.map (t • LinearMap.id)`.
- The canonical projection D → Spec κ: `q`, induced by `inlHom K K`.
  The corresponding projection for E is `r`.
- The set T: the subtype of `D ⟶ X` with `c ≫ θ = b` and
  `θ ≫ p = q ≫ b ≫ p`. The second equality expresses precisely being a k-morphism;
  the structure map of D is the canonical κ-projection followed by b and p.

Conclusions, matched individually:
- Clause (a), the commutative square is a scheme pushout:
  `IsPushout c c (j 0) (j 1)` (its `CommSq` component includes commutativity).
- Clause (a), existence and uniqueness for every pair: the `∀ θ₁ θ₂ : T, ∃! Θ`
  conjunct, with both restriction equalities, in the category of all schemes.
- Clause (a), the extension is a k-morphism: the next universal conjunct says any
  extension satisfies `Θ ≫ p = r ≫ b ≫ p`.
- Clause (b), closure and vector-space axioms: `∃ a : AddCommGroup T` and, after
  installing a, `∃ v : Module K T`. Since K is a field this is a vector space.
  Addition and scalar multiplication return elements of T, so closure is included.
- Clause (b), the specified zero: `(0 : T).val = q ≫ b`.
- Clause (b), the specified sum: for every extension Θ with both restriction equalities,
  `(θ₁ + θ₂).val = s ≫ Θ`. Existence of such Θ was stated separately, so this is
  not a vacuous characterization.
- Clause (b), the specified scaling: `(t • θ).val = m t ≫ θ.val` for all t and θ.

Dependencies and source signatures read:
- `def-weil-pbc-scheme-conventions` has a convention-only record and fixes no new
  notion. Its scheme notion is Mathlib `AlgebraicGeometry.Scheme`, and an arbitrary
  map p to `Spec k` supplies exactly the required base structure.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField`, from
  `Mathlib.AlgebraicGeometry.ResidueField`. Its definition is the residue field of the
  stalk, and the same module's `fromSpecResidueField` gives b. The `Field` instance
  is supplied by Mathlib, without an additional assumption.
- `def-sc-dual-numbers`: `DualNumber`, from `Mathlib.Algebra.DualNumber`, the
  abbreviation `TrivSqZeroExt R R`; epsilon is `TrivSqZeroExt.inr 1`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, from
  `Mathlib.AlgebraicGeometry.Scheme`, imported through ResidueField.
- Added existing landed dependency `def-sc-trivial-square-zero-extension`, with recorded
  declaration `TrivSqZeroExt` in `Mathlib.Algebra.TrivSqZeroExt.Basic`. Read its full
  construction and the docstrings/signatures of `map`, `fstHom`, `inlHom`.
  No copy of that node or construction is delivered.
- `IsPushout` is Mathlib's scheme-category pushout predicate, from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`.

Edge cases: no assumption x is k-rational, closed, or has finite residue extension.
An empty scheme has no x, so no spurious inhabited tangent space is asserted.
For X = Spec k the relative tangent space is the zero vector space; the existential
structures permit that. Scalars 0, 1, and -1 have the stated formulas, including in
characteristic 2. The two projections and their sum work in every characteristic.
Scheme, field and residue field universes are explicit; no variables auto-bind.

Searches:
- msearch leanfinder, “tangent vectors of a scheme as morphisms from dual numbers form
  a vector space”: eight hits, including manifold tangent modules and formally unramified
  schemes, none the requested theorem.
- msearch loogle, `DualNumber, TrivSqZeroExt.lift`: zero hits.
- msearch grep, `TangentSpace|tangentSpace|dualNumbers`, AlgebraicGeometry: zero hits.
- msearch leansearch, “dual-number tangent vectors of a scheme form a vector space”:
  unavailable (Internal Server Error).
- rg in WeilConjectures and lean/Sheaf for tangent, tangentSpaceAt, DualNumber,
  dualNumbers: general dual-number scheme constructions and group tangent spaces,
  no theorem with this statement. RiemannRoch only has tangent-separation results.
- rg of the item id in WeilConjectures and lean_names_upstream: no existing declaration.
- rg in DAG definition nodes for square-zero/TrivSqZeroExt found the already-landed
  `def-sc-trivial-square-zero-extension`; it is cited instead of duplicated.
- rg of the chosen declaration name across Mathlib, WeilConjectures, lean/Sheaf and
  lean_names_upstream: no collision.

Source checked directly: https://stacks.math.columbia.edu/tag/0B2B, including the
pushout algebra and the addition and scaling maps in its proof. The local Stacks
checkout is absent on this machine. The node agrees with that source; no fault or
STATEMENT-DISPUTED claim.

Validation: server single-file compilation and delivery dry run; the second reader
will add the independent reading and deliver. Nothing is proved in this stage.

## Second reading by C1

I independently opened the sandbox node and module, all five statement-dependency
nodes, the recorded Mathlib definitions, and the landed pushout theorem. I also read
Stacks `varieties.tex` directly from the Stacks source repository, from
`section-tangent-spaces` through `lemma-tangent-space` and its proof, and checked Tags
0B28 and 0B2B. The preceding setup is an arbitrary morphism X → S and a point x,
without finite-type, Noetherian, separation or rationality assumptions. The node
specializes S to Spec k. The Lean has exactly that specialization.

The node's objects, hypotheses and conclusions, listed independently and matched:

- Field k: `(k : Type u) [Field k]`. Correct; a field, without characteristic or
  algebraic-closure assumptions.
- Scheme X over k and point x: `(X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (x : X)`.
  Correct. An arbitrary structure morphism gives the required k-scheme; the node's
  proof explicitly calls this morphism p. There are no extra geometric instances.
- Residue field κ(x) and canonical point morphism: `K := X.residueField x` and
  `b := X.fromSpecResidueField x`. Correct. In `ResidueField.lean`, the former is
  `IsLocalRing.ResidueField (X.presheaf.stalk x)` and has its Field instance;
  the latter is `Spec.map (X.residue x) ≫ X.fromSpecStalk x`.
- Dual numbers and the two-coordinate square-zero algebra: `DualNumber K` and
  `TrivSqZeroExt K (Fin 2 → K)`, with spectra D and E. Correct. The recorded
  `DualNumber` is literally `TrivSqZeroExt K K`. The existing square-zero extension
  has multiplication `(a,v)(b,w) = (ab, a • w + b • v)`, so the two coordinate
  infinitesimals and all their products have exactly the node's meaning.
- Closed-point inclusion c: `Spec.map` of `(TrivSqZeroExt.fstHom K K K).toRingHom`.
  Correct: the algebra projection kills epsilon and fixes constants; Spec reverses it.
- Maps j₁ and j₂: `j 0` and `j 1`, formed using `TrivSqZeroExt.map (LinearMap.proj i)`.
  Correct: the selected coordinate maps to epsilon and the other to zero. Fin's
  zero-based labels are just a relabelling of the node's two indices.
- Addition map s: `TrivSqZeroExt.map (LinearMap.proj 0 + LinearMap.proj 1)` under
  `Spec.map`. Correct: both coordinate infinitesimals map to epsilon.
- Scaling maps: `m t`, induced by `TrivSqZeroExt.map (t • LinearMap.id)`.
  Correct: epsilon maps to t epsilon and constants are fixed.
- Canonical projections to Spec κ: q and r use `TrivSqZeroExt.inlHom`.
  Correct; `inlHom` is the constants ring inclusion, with the required reversed
  direction under Spec.
- Set T of k-morphisms with fixed closed point:
  `{θ : D ⟶ X // c ≫ θ = b ∧ θ ≫ p = q ≫ b ≫ p}`. Correct. The second equality
  is precisely the over-k condition with D's canonical structure morphism; the
  first is the curved-arrow condition in the source diagram. Composition with
  b and p is the induced map Spec κ(x) → Spec k.
- Conclusion (a), commutative scheme pushout: `IsPushout c c (j 0) (j 1)`.
  Correct. I read `IsPushout`: its `CommSq` field includes the commutativity
  equation, and its colimit field is in the whole scheme category.
- Conclusion (a), unique extension of each pair: `∀ θ₁ θ₂ : T, ∃! Θ : E ⟶ X, ...`
  with `j 0 ≫ Θ = θ₁.val ∧ j 1 ≫ Θ = θ₂.val`. Correct, with the same quantifier
  order and uniqueness among all scheme morphisms, not merely k-morphisms.
- Conclusion (a), extension is over k: the following universal conjunct concludes
  `Θ ≫ p = r ≫ b ≫ p` from those two restriction equalities. Correct; quantifying
  over any such extension is equivalent to asserting this for the unique extension.
- Conclusion (b), closure and vector-space structure: `∃ a : AddCommGroup T` followed
  by `∃ v : Module K T`, with each structure installed by `letI`. Correct. A module
  over the residue field is precisely a vector space. Its operations return subtype
  elements, so both closure assertions are included rather than assumed.
- Conclusion (b), prescribed addition: `(θ₁ + θ₂).val = s ≫ Θ` for every extension
  satisfying the restrictions. Correct. The earlier existential extension prevents
  vacuity and fixes the operation uniquely.
- Conclusion (b), prescribed scalar action: `(t • θ).val = m t ≫ θ.val` for all
  t and θ. Correct, including zero scalars.
- Conclusion (b), prescribed zero: `(0 : T).val = q ≫ b`. Correct: this is the
  constant tangent vector in the node, not an arbitrarily chosen base point.

Dependency and definition review: the scheme-conventions node fixes no additional
notion or declaration; its scheme dependency is Mathlib's Scheme. Residue field,
DualNumber and Spec/Spec.map have the exact recorded signatures and meanings above.
The added dependency `def-sc-trivial-square-zero-extension` is already landed and
records the existing Mathlib construction, not a new node of this delivery.
I read the map, fstHom and inlHom definitions and their docstrings. The proof-only
node `lem-sc-dual-number-scheme-pushout` has its actual landed signature for arbitrary
positive n, arbitrary target X, compatible restrictions and unique extension, so
its n = 2 and n = 3 uses in the proof docstring are justified. No new node or
replacement dependency module is needed. `def-sc-scheme-tangent-space` has no Lean
record and itself depends on this item, so it cannot supply a pre-existing definition.
The local `let T` states the set on which this lemma establishes the structure; it
introduces no parallel named tangent-space definition.

Edge cases: an empty scheme has no x, so the binder makes the assertion vacuous.
For the identity structure map on X = Spec k, T consists of its constant tangent
vector and the structures allow the zero vector space. No residue-field equality
κ = k, closedness of x, or finiteness of κ/k is imposed. Every characteristic is
covered, including characteristic 2, where coordinate sum and negative scalar
formulas still make sense. There is no variable n or variable index set in this
statement: Fin 2 is the source's specified two-element set, so an empty index set
or n = 0 is not a case of this node. The declaration is polymorphic in arbitrary
u, uses the common universe of the category Scheme.{u}, and imposes no fixed small
universe bound. All variables and the sole universe are explicitly bound.

Independent searches, using wording different from the first worker:

- LeanFinder through msearch: “scheme morphisms from infinitesimal dual number
  thickening with fixed residue point admit additive group and residue field module”.
  Eight hits, principally formally unramified morphisms and ring extensions;
  none states this vector-space theorem.
- Loogle through msearch: `TrivSqZeroExt, Module`. Twelve hits for the square-zero
  ring's own structures and inclusions; none for fixed-point scheme morphisms.
- LeanSearch through msearch: “The set of scheme morphisms from the spectrum of
  dual numbers to a scheme fixing a point is a vector space over its residue field”.
  Service unavailable (Internal Server Error); recorded as unavailable.
- Direct rg across Mathlib/AlgebraicGeometry, all WeilConjectures and lean/Sheaf,
  for tangentSpace, TangentSpace, tangentGroup, infPoints, dual numbers and square
  zero. Mathlib has no scheme tangent-space declaration. I opened the close upstream
  `GrpObj.infPoints` and `tangentGroup`: both assume a group object and fix its identity,
  so they are special cases and not the present arbitrary scheme/point. The other
  hits concern cotangent modules, tangent sheaves or dual-number thickenings.
  No matching statement or declaration-name collision was found.

No mismatch was found and no Lean or node changes were made. The module contains
one named theorem with proof `sorry` and no data definition with a hole. Both
module and declaration docstrings cite the correct source and blueprint id, and
the theorem's three proof steps reproduce all node steps, including three-copy
associativity, the base-morphism uniqueness argument and additive inverses.
All lines are at most 100 characters; each import supplies declarations used here.
The node's `lean.statement` is byte-for-byte the theorem signature before `:=`.
Server scompile completed cleanly (exit 0, 2.2 seconds), with no diagnostics.
