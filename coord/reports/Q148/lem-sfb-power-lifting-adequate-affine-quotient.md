## Worker report

The module `Sheaf.AlgebraicGeometry.PowerLiftingAdequateAffineQuotient` states
`AlgebraicGeometry.SchemeAction.power_lifting_adequate_affine_quotient`, with its
whole proof `sorry`. There are no new definitions, dependency repairs, or statement
changes. Only the item's `lean` field changes.

Hypothesis and conclusion correspondence:

- The field is `(k : Type u) [Field k]`, the exact Mathlib match of def-weil-field.
- The group scheme is `(G : Over (Spec (CommRingCat.of k))) [GrpObj G]`.
  Smoothness and affineness are `[Smooth G.hom] [IsAffineHom G.hom]`.
  Finite type is `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, exactly the
  dependency's convention, with no connectedness or reductivity assumption.
- Every pair of finitely generated commutative k-algebras is quantified in
  `hpower` as `B C : Type u`, with their `CommRing`, `Algebra`, and
  `Algebra.FiniteType` instances. There is no nontriviality assumption on B or C.
- Rational actions use `[ModObj G (affineActionScheme k B)]` and the same for C.
  `ModObj` includes the unit and associativity laws, not just an arbitrary map.
  Affine duality identifies these with counital, coassociative algebra coactions.
  For the conventional right coordinate coaction use group inversion to pass
  from a left scheme action to a right one. The dependency's
  `affineTensorCoaction` is instead the directly swapped pullback of the left
  action. Applying inversion on the group factor relates the two maps. Its
  involutivity and preservation of the unit imply exactly the same invariant
  equalizer and exactly the same equivariant algebra morphisms. Consequently
  quantifying scheme actions neither restricts nor enlarges the rational actions
  of the node, and the handedness convention does not change the hypothesis.
- An equivariant surjection is `(f : B →ₐ[k] C)` with `Function.Surjective f` and
  the displayed equality for every `b : B` between the C coaction of `f b` and
  `Algebra.TensorProduct.map f (AlgHom.id k (affineGroupCoordinates k G))`
  applied to the B coaction. The map is a k-algebra morphism, not a mere ring map.
- The invariant element is `c : affineInvariants k C G`; the invariant lift is
  `b : affineInvariants k B G`. Their subtype coercions give the equality in C.
  The conclusion of `hpower` is `∃ N : ℕ, 0 < N ∧ ∃ b, f b = (c : C) ^ N`.
  Natural positive exponents express exactly the positive integer exponent.
- The arbitrary finite-type rational E is separately bound with `CommRing E`,
  `Algebra k E`, `Algebra.FiniteType k E`, and its `ModObj` action.
- The source stack is literally `affineActionQuotientStack k E G`. Its algebraic
  stack proof is `(affine_action_stack_presentation k E G).1`.
- The target is `AlgebraicSpace.schemeSpace (affineInvariantSpectrum k E G)`.
  `affineInvariantSpectrum` is Spec of the actual `affineInvariants` equalizer;
  `affineInvariants_mem_iff` identifies it with the tensor coaction equalizer.
  No finite-generation assumption on the invariant ring is added.
- The canonical morphism is `φ`, with `hφ` saying its atlas composite is vertically
  isomorphic to `discreteModuliMap (yoneda.map (affineInvariantProjection k E G))`.
  The projection is Spec of the invariant inclusion. This is exactly the
  characterization in the recorded `affine_action_stack_invariant_spectrum`.
  That dependency already proves existence and uniqueness up to vertical
  isomorphism. Thus this binder ranges over representatives of the specified
  canonical map, and does not assume existence of an arbitrary auxiliary map.
- `IsAdequateModuliSpace ... φ` is the entire existing predicate: quasi-compact,
  quasi-separated, canonical structure-sheaf map an isomorphism, and positive
  power lifting for all surjections of quasi-coherent algebras on every affine
  etale 2-base change, including algebras not descending from the original stack.
  No exactness of direct image is asserted.

Dependencies read and used:

- Mathlib.Algebra.Field.Defs, `Field` (docstring and full class signature read).
- Sheaf.AlgebraicGeometry.AffineActionQuotientStack,
  `AlgebraicGeometry.affineActionScheme`, `affineActionQuotientStack`, and
  `AlgebraicGeometry.SchemeAction.quotientAtlas`; the recorded left torsor total
  category and action data are reused, with no new action or quotient definition.
- Sheaf.AlgebraicGeometry.AffineActionStackPresentation,
  `AlgebraicGeometry.SchemeAction.affineGroupCoordinates`, `affineTensorCoaction`,
  `affineInvariants`, `affineInvariants_mem_iff`, `affineInvariantSpectrum`,
  `affineInvariantProjection`, `affine_action_stack_presentation`, and
  `affine_action_stack_invariant_spectrum`; their full source/docstrings were read.
- Sheaf.AlgebraicGeometry.AdequateModuliSpace,
  `CategoryTheory.IsAdequateModuliSpace` (entire definition read).
- Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite,
  `AlgebraicGeometry.AlgebraicSpace.schemeSpace` (real representable-sheaf data).
  This is the existing scheme-as-space helper needed by the predicate.
- Already stated proof dependencies are privately imported:
  Mathlib.RingTheory.Smooth.Flat (`Algebra.Smooth.flat`) and
  Mathlib.RingTheory.Flat.Basic (`Module.Flat.lTensor_exact`, `rTensor_exact`).
  The two rational-comodule/descent proof nodes currently have no Lean records
  or Mathlib matches, so have no modules to import. They are proof prerequisites,
  not notions required for this statement; their complete role is in the proof
  docstring. The three recorded statement dependency modules are public imports.

Source checked: https://arxiv.org/html/1005.2398v3, Section 2.1, Lemma 9.2.5(3'),
Remark 9.2.4(1), Lemma 9.2.8(3), Theorem 9.1.4 and Remark 9.1.5. The finite-type
invariant-lifting criterion followed by the affine GIT theorem agrees with this
node. No source-based statement correction is required.

Edge cases checked by reading the statement: zero algebras and the empty affine
scheme are allowed; no `Nontrivial E` or reducedness condition is present. The
exponent zero is explicitly excluded. Invariant rings need not be finite type.
The trivial group is allowed; no positive dimension, characteristic, algebraic
closure, or connectedness assumption is present. All algebras and schemes use the
dependency's universe u; every finite-type algebra over k has a representative in
this universe (a quotient of a finite-variable polynomial algebra), so this test
universe loses no finite-type case. Equality is tested on coordinate morphisms,
not just k-rational or geometric points, so nilpotents are retained.

Searches made before writing:

- msearch.py leanfinder: "Power lifting of invariant elements along equivariant
  surjections gives an adequate moduli space for an affine quotient stack".
  Eight hits on ordinary representation coinvariants, profinite ring invariants,
  and Galois categories; none states the node.
- msearch.py loogle: `"invariants", "Surjective"`. Two hits,
  Representation.Coinvariants.mk_surjective and a group-homology surjectivity
  theorem; neither is a rational algebra action or an adequate moduli theorem.
- msearch.py leansearch: "Power lifting invariants adequate quotient stack".
  Eight hits (manifold invariant properties, transferred powers, representation
  quotient invariants), no match.
- msearch.py grep in Mathlib/AlgebraicGeometry:
  `adequate|Adequate|power.lift|PowerLift`: zero hits.
- msearch.py grep throughout Mathlib:
  `adequate.*[Qq]uotient|power.*[Ll]ift.*[Ii]nvariant|IsAdequateModuliSpace`:
  zero hits.
- rg on lean/WeilConjectures and lean/Sheaf for rational actions, coactions,
  power lifting and IsAdequateModuliSpace: found the recorded quotient and
  predicate interfaces, plus separate Hopf-module data and downstream adequate
  moduli consequences. No declaration already states this implication.
- rg for this item id in lean/WeilConjectures: no hits. Exact proposed declaration
  and module-name searches in lean/Sheaf, lean/WeilConjectures and
  dag/lean_names_upstream.json: no collisions.
- The instructed CompactObject example is withdrawn in this checkout; its source
  contains only `module` and a withdrawal comment. The live dependency files
  provide the current header/module/public-section conventions instead.

No STATEMENT-DISPUTED flag or node fault. The scompile.py check passed in both
sandbox and library-module modes (3.2 and 3.3 seconds), with no errors or unexpected
warnings. No global build or direct Git command was run.

## Second reading by Q148

A separate second pass by the sole dispatched worker compared the complete node
with the final signature and unfolded its dependencies. No second agent was
started, as the dispatch brief forbids it; the maintainer's independent review is
still required. This pass checked in particular that hpower is universal over
both actions, that the equalizer is the recorded one, that the tensor map is
covariant in B → C, and that hφ is the dependency's existing canonical-map
characterization rather than a new geometric hypothesis. The docstring was
clarified to explain group inversion in the left-action/right-coaction convention.
No mathematical mismatch was found.
