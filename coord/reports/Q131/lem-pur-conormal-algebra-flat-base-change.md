## Worker report

The module `Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange` states
`AlgebraicGeometry.ConormalGradedAlgebra.existsUnique_baseChangeMap` with proof `sorry`.
The only additional declarations are the concrete composite `adjointPiece` and the
Prop-valued specification `IsBaseChangeMap` of this same node's canonical comparison.
Neither introduces a second conormal algebra or a second tensor pullback. No theorem
is proved, no additional DAG node is needed, and the original node changes only in `lean`.

I read Stacks `divisors.tex`, the passages labelled
`lemma-conormal-algebra-functorial` and `lemma-conormal-algebra-functorial-flat`
(Tags 0634 and 0635), including their affine formula and proof. They agree with the node.
I read the full recorded conormal presentation, its homogeneous inclusions, affine
and stalk formulas, representative construction, and existence/uniqueness theorem.
I obtained the current published tensor-pullback, structure-sheaf comparison and
conormal-functorial source modules through `scompile.py --source` as well as consulting
the local copies. There is no repair note for this item.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Schemes X, Z, X', Z' and morphisms i, i', g, f | Explicit variables `{X Z X' Z' : Scheme.{u}}`, `(i : Z ⟶ X)`, `(i' : Z' ⟶ X')`, `(g : X ⟶ X')`, `(f : Z ⟶ Z')` |
| i' is a closed immersion, and its base change i is a closed immersion | `[IsClosedImmersion i']` and `[IsClosedImmersion i]`; the latter is the explicitly mentioned property of the given Cartesian immersion, rather than a restriction on allowable base changes |
| Cartesian square, with g composed with i equal to i' composed with f | `(h : i ≫ g = f ≫ i')` and `(hc : IsLimit (PullbackCone.mk i f h))`; this allows every chosen fibre-product presentation, not just Mathlib's chosen object |
| The ideal sheaves I and I' | The existing `i.ker` and `i'.ker` and their `toModulesι`; no ideals are supplied independently |
| G and G' are the conormal graded algebras | `(A : Presentation i)` and `(A' : Presentation i')` from the recorded dependency; their `algebra`, `inclusion`, `coproduct`, `powerIdentification`, and `affineChart` supply exactly the canonical graded objects and identifications |
| f*G' is the pulled-back module/algebra | The underlying module is `(tensorPullback f).obj A'.algebra.toModule`. Its algebra-map universal property is encoded by the ring-sheaf adjoint ρ, its structure-sheaf compatibility, and equality of ρ with the adjoint of c |
| A morphism of graded O_Z-algebras | `IsBaseChangeMap` supplies a sheaf-of-commutative-rings map `ρ : A'.algebra.right ⟶ f_* A.algebra.right`, commuting with the structure maps. Its equality on every section with `c` after the tensor-pullback unit identifies it with the adjoint of the O_Z-linear module map c. It is therefore a multiplicative unital map out of algebra scalar extension. The maps `d n : f*(piece i' n) ⟶ piece i n` and `(tensorPullback f).map (A'.inclusion n) ≫ c = d n ≫ A.inclusion n` express preservation of every homogeneous piece |
| There is a unique such morphism with the affine formula | The theorem asserts `∃! c, IsBaseChangeMap i i' g f h A A' c`; the uniqueness predicate includes the affine characterization, and the separate final universal clause establishes the properties for every map with that characterization |
| Every compatible pair of affine opens U, U' | Both the ideal equality and affine specification quantify over every `U : X.affineOpens`, `U' : X'.affineOpens`, `H : U.1 ≤ g ⁻¹ᵁ U'.1` |
| On such a chart I = I'R | The first conjunct of the theorem is `i.ker.ideal U = Ideal.map (g.appLE U'.1 U.1 H).hom (i'.ker.ideal U')` |
| In every degree, [a] tensor r maps to [g-sharp(a) r] | The predicate quantifies over all `n : ℕ`, ideal-power sections `a`, and `r : Γ(X, U.1)`. It obtains a section b of the actual target power with `(powerInclusion i n) b = g.appLE ... ((powerInclusion i' n) a) * r`, and equates the image with `representative i n U.1 b`. The left side uses `adjointPiece` followed by restriction along `i.preimage_mono H` and scalar multiplication by `i.app U.1 r` |
| These are the identifications in the conormal-algebra dependency | `power`, `powerInclusion`, `piece`, `representative`, and the presentation's `powerIdentification`/`affineChart` are reused. The two adjunction units in `adjointPiece` first take a to its conormal class and then to its pure tensor with one. Multiplying by `i.app U r` supplies the arbitrary tensor coefficient. No unrelated affine chart or arbitrary tensor isomorphism is chosen |
| Degree zero is the identity under the canonical structure-sheaf comparison | `d 0 ≫ tensorPullbackObjUnitToUnit i = (tensorPullback f).map (tensorPullbackObjUnitToUnit i') ≫ tensorPullbackObjUnitToUnit f`. Here `piece i 0` is definitionally the pullback of the unit module, so both sides are the two routes to O_Z |
| Degree one is the canonical conormal map | `d 1` is equated with `Classical.choose ((Classical.choose_spec (closedImmersion_conormal_functorial i i' g f h).2).2)`. The power-one definition is literally `i.ker.toModules`, so no unidentified isomorphism or extra assumption is needed |
| c is surjective | The final universal clause gives `Epi c`. For sheaves of modules this is local surjectivity, equivalently surjectivity on all stalks; it does not assert sectionwise surjectivity on arbitrary opens |
| If g is flat, c is an isomorphism of graded algebras | The same clause gives `Flat g → IsIso c`. Together with the already specified ring and grading structure, invertibility of the underlying module map is equivalent to invertibility of the graded algebra map; the inverse preserves multiplication/unit, and the direct-sum grading, by composing with c |

`adjointPiece` has actual data: the composite of the i' adjunction unit, the
pushforward of the f adjunction unit followed by the pushforward of d, the canonical
pushforward-composition comparison, and the pushforward identification from h. Its
formula is the same adjoint convention used by the recorded conormal-functorial theorem.
`IsBaseChangeMap` is just the specification of the map asserted in this node, with all
binders explicit. There is no arbitrary algebra construction, assumed map, chosen
Nonempty algebra, or postponed well-definedness proof inside a definition. Every
variable and universe is explicitly bound; `autoImplicit` is disabled.

Dependencies used, with their recorded declarations and modules:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, morphisms `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, with
  `Mathlib.AlgebraicGeometry.Pullbacks`: `pullback`, the pullback cones and their universal
  property, here expressed by `IsLimit (PullbackCone.mk i f h)`.
- `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra`:
  `AlgebraicGeometry.ConormalGradedAlgebra.Presentation`, `power`, `powerInclusion`,
  `piece`, `representative`, and `exists_conormalGradedAlgebra` (the presentation's
  existing universal property is used rather than restated).
- `WeilConjectures.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.exists_tensorPullbackAdjunction` and the recorded
  module pushforward composition/congruence identifications.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackObjUnitToUnit`.
- `WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial`:
  `AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_functorial`.

The proof-only imports retain the node's plan: closed-subscheme base-change ideal
image, module-pullback ideal quotient, preservation of quasi-coherence, affine sections,
affine tilde adjunction and tilde sections, module-morphism cover gluing, graded sheaf
structures, local surjectivity/stalk detection, flat tensor exactness, and tensor-quotient
base change. All already recorded theorem modules are imported, without public imports
unless their declarations occur in the signature/specification. No proof dependency
creates an import cycle.

Edge cases checked mathematically before drafting:

- Empty schemes and the unit ideal give the zero sheaf/ring on the empty closed
  subscheme, and the universal formulas and isomorphism clause remain valid.
- The zero ideal gives only degree zero and the canonical structure-sheaf pullback.
- Degree zero is included in every quantifier, uses the actual power-zero unit module,
  and has its explicit canonical normalization.
- Degree one is definitionally the recorded conormal module and has its explicit map.
- Identity base change gives the identity through the canonical tensor-pullback
  identifications, for every conormal presentation.
- A flat polynomial extension A → A[t] gives all-degree isomorphisms, with no finite
  generation, Noetherian, reducedness, separatedness, or characteristic assumption.
- Nonreduced ideals such as (x²) retain the same successive-power quotients and formula.
- For A = k[x], I' = (x), B = k, the nonflat base change kills the positive-degree
  target pieces; it is surjective but degree one is not injective. Flatness is therefore
  only used for the conditional isomorphism, not added to existence or surjectivity.
- No affine-intersection assumption is made, and no passage of non-affine sections
  through an infinite direct sum or a cokernel is asserted.

Searches performed for an existing declaration:

- `msearch.py` LeanFinder, query “The conormal graded algebra of a closed immersion
  has a canonical surjective base change map which is an isomorphism under flat base
  change”: eight results including KaehlerDifferential base-change surjectivity and
  IsClosedImmersion results, none stating this graded algebra/sheaf comparison.
- `msearch.py` Loogle, query `Ideal.tensorCotangentHom, Module.Flat`: one result,
  `Ideal.tensorCotangentHom_injective_of_flat`, only ring-level degree one.
- `msearch.py` grep, query `conormal|associatedGraded`, Mathlib `AlgebraicGeometry`:
  zero hits.
- `msearch.py` LeanSearch, query “The associated graded algebra of an ideal commutes
  with flat base change”: eight results on graded tensor products, graded algebras,
  and flatness, none the required statement.
- `rg` on the source project's `WeilConjectures/AlgebraicGeometry` for
  `conormal|Conormal|associatedGraded`: only the deformation-to-normal-cone comment;
  searching all source `WeilConjectures` for the item id found no declaration.
- `rg` on project `lean/Sheaf` for conormal/base-change/graded algebra terms located
  `ConormalGradedAlgebra`, `ClosedImmersionConormalFunctorial`,
  `ClosedImmersionConormalFlatBaseChange`, and affine comparison helpers. I read them:
  the flat base-change theorem is degree one only, not the graded algebra statement.
- Name checks in `dag/lean_names_upstream.json`, Mathlib, the upstream project, and
  project `lean/Sheaf` found no declarations named
  `AlgebraicGeometry.ConormalGradedAlgebra.adjointPiece`,
  `AlgebraicGeometry.ConormalGradedAlgebra.IsBaseChangeMap`, or
  `AlgebraicGeometry.ConormalGradedAlgebra.existsUnique_baseChangeMap`.

No `STATEMENT-DISPUTED` issue or source-based correction is needed. No statement or
proof dependency has been changed. The proof docstring follows all nine node proof
steps and includes the local-generation and flat-injectivity arguments.

Validation: `scompile.py Q131 lem-pur-conormal-algebra-flat-base-change` compiled the
single sandbox file both under its sandbox module and under the delivered library
module path, cleanly within the default 60-second per-file limit. The final delivery
also runs the prescribed server preflight and per-file compile through `deliver2.py`.

## Second reading by Q131

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
