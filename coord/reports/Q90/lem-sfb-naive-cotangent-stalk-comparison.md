## Worker report

Item: `lem-sfb-naive-cotangent-stalk-comparison`.
Module: `Sheaf.Topology.NaiveCotangentStalkComparison`.
Main declaration: `TopCat.NaiveCotangent.naive_cotangent_stalk_comparison`.

Read the node, every statement dependency and its recorded declaration, the
stage-1 proof, Stacks `modules.tex` section-netherlander (canonical presentation,
naive complex and equation-commutative-square-sheaves), lemma-pullback-NL and
lemma-stalk-NL (Tag 0D09). The source proves the latter by inverse image along
the inclusion of a point. The Lean asserts precisely its derived comparison,
with the additional section/germ normalization and naturality required by the
node. No statement correction, no new nodes, and no dependency repairs.

The theorem asserts the existence of `Comparison T`. The record specifies
canonical constructions by their generator formulas; it is not an arbitrary
isomorphism assumption. Its only postponed proof is the named main theorem.
Definitions have actual data, including the existing Mathlib conormal quotient,
tensor differential, complex and module-stalk action. All variables and the
common universe `u` are explicit, and `autoImplicit` is false.

Hypotheses and clauses, in the order of the node:

- An arbitrary topological space is `T : TopCat.{u}`. There are no separation,
  finiteness, nonemptiness, or local-ring hypotheses.
- Ring sheaves and their homomorphism are `A B : T.Sheaf CommRingCat.{u}` and
  `f : A ⟶ B`, quantified in the fields of `Comparison`. This is the small site
  `Opens T` with its usual Grothendieck topology, with no replacement topology.
- The size convention is explicit universe `u` for the space, sheaf values,
  polynomial variables and module carriers; Opens T is small in that universe.
  `HasDerivedCategory.{u+1} (ModuleCat.{u} R)` is the usual localization-size
  parameter, quantified for all coefficient rings. It imposes no mathematical
  condition on a ring: Mathlib's `HasDerivedCategory.standard` supplies it.
- The standard sheaf complex is an arbitrary
  `SheafPolynomialCotangent.Model (SheafPolynomialCotangent.canonical f)`.
  This uses the dependency's actual polynomial sheaf and differential tensor
  term, and its locally surjective conormal quotient with exactly the locally
  generated kernel-square kernel. Its support and differential are already
  specified by that recorded Model. Quantifying over all these coordinate
  models avoids choosing data from the dependency's existence theorem.
- A point is `t : T`. `stalkComplex K t` applies the existing
  `RingedSpace.moduleStalkFunctor` termwise to `K.complex`, after merely packaging
  `(T,B)` as a ringed space. This is the actual additive stalk with Mathlib's
  commutative-stalk-ring action; it is not a new stalk construction or an
  arbitrarily chosen complex with stalk-like cohomology.
- `stalkArrow f t` is the arrow between the categorical commutative-ring stalks.
  `germs f W t ht` consists of the two actual germ ring homomorphisms. Naturality
  of stalks supplies its commutative square.
- For every ring arrow `r`, `presentation r` is the surjection
  `MvPolynomial r.right r.left → r.right`, with coefficients sent by `r.hom`
  and `X b` sent to `b`. The surjectivity witness is literally `X b`.
  `Naive.complex (presentation r)` is the recorded existing complex
  `[I/I² → B ⊗_P Ω[P/A]]` in degrees -1 and 0. `Naive.kernelClass`,
  `Naive.tensorGenerator` and `Naive.differential` are reused, not redefined.
- The canonical comparison is `Comparison.stalks f K t`, a chain map from
  the actual module-stalk complex to that actual standard ring complex.
  `Comparison.derived_iso` asserts `IsIso (DerivedCategory.Q.map ...)` for
  this very map. Thus `asIso` yields the displayed isomorphism in D(B_t),
  with its forward map fixed as the localization of the specified comparison.
  This is a derived assertion, not only a family of cohomology isomorphisms.
- Each neighborhood is `W : Opens T`, with `ht : t ∈ W`.
  `Comparison.sections f K W` is the sectionwise chain map into `K(W)`.
  `polynomialSection f W` is the polynomial-sheafification unit.
  `sectionKernel` and `sectionKernel_formula` identify the sectionwise kernel
  with its image under this unit; the formula determines this subtype value
  uniquely, so no arbitrary kernel data is being introduced.
- The sectionwise map on kernel classes is `sections_neg_one`; on differential
  tensors it is `sections_zero`. These use respectively `K.quotient` and
  the existing sheaf tensor `SheafPolynomialCotangent.tensorD` through
  `K.degreeZero`, so the source section complex has not been replaced by
  a presentation of the target's section rings.
- `germ_formula` states, in every degree and for every element of the
  sectionwise ring complex, that the composite of `sections`, the actual
  module germ, and `stalks` equals the ring-complex map of the two germ ring
  homomorphisms. Localizing this equality gives exactly the requested equality
  in the derived category.
- For a ring square `q`, `presentationMap q` sends coefficients along `q.left`
  and sends `X b` to `X (q.right b)`. Its base and augmentation triangles are
  verified in the definition. `ringMaps q : Naive.NaiveMap (presentationMap q)`
  uses the existing interface requiring `[h] ↦ [q(h)]` and
  `b ⊗ dp ↦ q.right(b) ⊗ d(q(p))`. Applied to `germs`, these are exactly
  `x_b ↦ x_(b_t)`, `[h] ↦ [h_t]` and `b ⊗ dh ↦ b_t ⊗ d(h_t)`.
- Scalar changes in ring-complex maps use the existing `restrictComplex`;
  by the scalar-extension adjunction these are the maps from ordinary extension
  of source coefficients mentioned in the node. No derived tensor or flatness
  hypothesis has been inserted.
- Naturality for an arbitrary square of ring sheaves is expressed by
  `sheafMaps`, `sheafMaps_semilinear`, `sheafMaps_sections`, and `naturality`.
  The first is an actual additive chain map, semilinear on every section;
  the next fixes its action by the sectionwise ring-square map. The final
  equality is the naturality square on every germ in every degree and for
  every element of the source sheaf term. Every stalk element is a germ,
  so it states the entire chain-map naturality square and hence its localization.

Dependency declarations used:

- `Sheaf.CategoryTheory.SheafPolynomialCotangentComparison`:
  `SheafPolynomialCotangent.Model`, `canonical`, `polynomials`, `polynomialSheaf`,
  `kernelIdeal`, `sets`, `tensorD`, and the source's polynomial comparison theorem.
  Their full signatures and normalization docstrings were read.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor` and its stalk-map interface were read;
  the commutative-ring sheaf specialization is used through the following
  already landed definition node, because its coefficient ring is B_t itself.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor` and its zero-morphism
  preservation instance. Added the already landed `def-pc-module-stalk-functor`
  to stmt_deps to name this exact specialization. Its source and node were read.
- `Sheaf.RingTheory.NaiveCotangentComparison`: `Naive.Presentation`,
  `PresentationMap`, `NaiveMap`, `complex`, `conormalIso`, `differentialsIso`,
  `kernelClass`, `tensorGenerator` and `differential`. Added the already landed
  `def-trf-naive-cotangent-comparison-data` to stmt_deps for these definitions.
  No coherence datum, lift, or arbitrary comparison is used to define the ring
  complex; these initial definitions do not depend on the coherence parameter.
- `Mathlib.RingTheory.Smooth.Basic`: the recorded `Algebra.Smooth` and its
  `FormallySmooth`/first-cotangent-homology interpretation were read. No smoothness
  assumption is present here; the node cites it for the standard ring complex.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `.D`, and
  `.linearMapEquivDerivation`, used by the existing conormal differential and
  tensor generators. The full signatures and docstrings were read.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, Basic and Map: `TensorProduct`,
  `.lift`, `.ext'`, and `LinearMap.rTensor`, including their generator formulas.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `.standard`, and `DerivedCategory.Q`.
- Proof-only imports are `WeilConjectures.Topology.InverseImageStalk`
  (`exists_inverseImage_stalk_iso_ab`, `exists_inverseImage_stalk_iso_commRing`),
  `WeilConjectures.Topology.InverseImageModule` (`inverseImageModule`), and
  `Mathlib.Topology.Sheaves.Functors` (`pullbackPushforwardAdjunction`).
  Their signatures and germ/unit docstrings were read. Polynomial universal
  properties and the differential/tensor proof dependencies are already public
  imports. The proof dependency `lem-sfb-topos-naive-cotangent-pullback` has no
  recorded Lean declaration/module on the base and is consequently not imported;
  it is not needed for elaborating the statement. Its planned use remains in
  the main theorem's proof docstring, with the four original DAG steps retained.

Searches actually run:

- msearch leanfinder: “The stalk of a sheaf naive cotangent complex is the naive
  cotangent complex of stalk rings with germ compatibility”: 8 hits, including
  ring cotangent maps, H1Cotangent and affine module stalks; none is the statement.
- msearch loogle: `"cotangent", "stalk"`: zero hits.
- msearch grep: `cotangent|Cotangent`, subdirectory `Algebra/Category/ModuleCat`:
  zero hits.
- msearch leansearch: “The stalk of the naive cotangent complex of sheaves of
  commutative rings is the naive cotangent complex of the stalks”: 8 hits,
  ordinary stalks and module/scheme local-ring comparisons, no exact match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id, cotangent/stalk
  combinations and the module-stalk functor: found the full cotangent-complex
  `Sheaf.Topology.SheafCotangentComparison` and its StalkModel, and existing
  ring naive-complex definitions. The full cotangent complex is not the two-term
  naive complex required here. The latter existing ring complex and the actual
  module-stalk functor are reused. No exact theorem was found.

Edge cases checked before and after writing:

- Empty T: there are no t or nonempty neighborhoods to quantify over; all point
  fields are vacuous and the section constructions still exist on the empty open.
- A one-point or non-Hausdorff space: no separation or local constancy occurs;
  the map is precisely coefficient and variable germs in either case.
- Zero ring sheaves: no Nontrivial instance is required and every construction
  (including polynomial evaluation and its X-b preimage) still exists.
- A=B or identity ring-square: the standard naive complex need not have zero
  terms, so it has not been replaced by zero. Its comparison uses its genuine
  standard presentation and the identity-variable map.
- Infinite or arbitrarily large rings within the chosen universe: one variable
  for every element; no finite presentation, finite support of the generator
  set, or finite-dimensional module hypothesis. Each polynomial is finite as
  usual, sufficient for representing its germ.
- Only degrees -1 and 0 can be nonzero by the dependency Model; `germ_formula`
  and naturality also quantify over every other degree, without assuming an
  arbitrary replacement complex has literally zero objects in those degrees.
- No characteristic, flatness, or smoothness constraint.

Validation: scompile.py compiled the sandbox and actual library module with no
errors or warnings after formatting repairs. The only sorry is the main theorem,
as required for stage 2. Final imports and the delivery are checked again by
scompile.py/deliver2.py below.

## Second reading by Q90

The dispatcher explicitly forbids starting other agents and assigns independent
review to the maintainer. This section records a separate second pass by the
same worker, rather than claiming an independent reviewer participated.

Read the node and file together again. Checked the actual stalk source against
`moduleStalkFunctor` and the exact commutative stalk ring, degrees -1/0 against
`Naive.complex`, quotient classes against `K.quotient`, and differential tensors
against `K.degreeZero` and `tensorD`. Checked that `derived_iso` applies to the
very map of `germ_formula`; there is no unrelated chosen isomorphism. Checked
that the germ square uses both ring germ homomorphisms, including changes of
the base ring, and that naturality is for every section in every degree, not
merely one selected generator. Checked the two added dependencies were already
landed and introduce no copied conormal, differential, tensor, or stalk notions.
Compilation first found an orientation/elaboration issue in the polynomial
augmentation triangle, two line breaks in field notation, and an insufficiently
explicit scalar-action type in the semilinearity field; these were repaired.
The subsequent pass removed all three style/unused-variable warnings. No
mathematical mismatch, statement correction, or disputed clause remains.
