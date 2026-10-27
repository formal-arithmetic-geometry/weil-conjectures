## Worker report

The module `Sheaf.RingTheory.StandardCotangentChainProjection` states
`Algebra.CotangentResolution.StandardProjection.exists_system`. It asserts the
existence of the face-difference chain projections simultaneously for every ring
map, with strict naturality for every commutative ring square. The only theorem
has proof `sorry`. All helper definitions contain explicit data; there is no
choice from an unproved existence theorem.

Source read: `literature/stacks-project/cotangent.tex`, Tag 08UP,
`remark-explicit-comparison-map`, lines 1977–2017 (downward generator formula,
compatibility with the first differential, annihilation of the second), and
Tag 08QL, `section-functoriality`, lines 867–905 (the recursive standard maps
and their maps on differentials). The statement remains unchanged. The seven
accepted proof steps are included in the theorem docstring, with their DAG
citations. There is no statement dispute or correction.

Hypotheses and clauses, matched individually:

- A homomorphism of arbitrary commutative rings is `f : Arrow CommRingCat.{u}`,
  with rings `f.left`, `f.right` and homomorphism `f.hom`. There is no flatness,
  finiteness, nontriviality, characteristic, injectivity, or surjectivity assumption
  on this ring map. A ring square is an arbitrary `q : f ⟶ g`, including its
  commutativity equation.
- The standard resolution is exactly `C.standard f`, with all polynomial terms,
  augmentation, faces, degeneracies and standard semilinear maps fixed by
  `C.standard_spec` and `C.standardMap_formula`. `C : Coherence` is the existing
  dependency's representation of the standard resolution, not a new resolution.
  The inherited `HasDerivedCategory` instances only support that interface;
  Mathlib supplies these instances for module categories, and the dependency's
  `exists_coherence` supplies such a `C`. The result holds for every such `C`.
  A common universe contains all four rings of every square; no independent
  smaller testing universe or equality of unrelated universes is imposed.
- `Q_n=(F_AU)^(n+1)B` is the dependency's `standardTerm f n`.
  `coordinates C f n` is the equality-induced ring isomorphism from the recorded
  standard term to that literal polynomial ring. The face formulas in the node
  follow directly from the dependency's `standardFace` and `standard_spec`:
  the two faces of `Y_p` are `p` and `X_(εp)`, and the three faces of `Z_f` are
  `f`, `Y_(d₀f)`, `Y_(d₁f)`. No face operator is replaced by an arbitrary map.
- `M_n` is the recorded `differentialTerm (C.standard f) n`, represented using
  `B ⊗_{Q_n} Ω¹[Q_n/A]`. `differentialGenerator ... n b x` is `b ⊗ dx`.
  This is precisely the tensor swap of the node's `dx ⊗ b`. The chain complex
  `K` is `differentialComplex (C.differentials (C.standard f))`, with the existing
  alternating differential and zero positive terms. `degreeIso` gives its tensor
  coordinates, and `boundary C f 0` and `boundary C f 1` are ∂₁ and ∂₂.
- `R=Q₀=A[B]` and its evaluation map are the dependency's `standardTerm f 0`
  and `standardAugmentation f 0`. `extension f` specializes Mathlib's canonical
  `Algebra.Generators.self` extension to this actual polynomial evaluation map.
  Its kernel is definitionally `RingHom.ker (standardAugmentation f 0).hom`.
  `conormal f` is Mathlib's `Extension.Cotangent`, the type synonym of the
  actual ideal quotient `I/I²` carrying its descended `B`-module action.
  `kernelClass f h` is the existing Mathlib quotient map, not an abstract class.
- `Projection.target`, `negIso`, `zeroIso`, and `otherTerms` specify the two-term
  target `[I/I² → M₀]` in degrees -1 and 0. Specifying a concrete complex by
  coordinate isomorphisms does not change its objects or differential. The
  `differential_formula` field specifies its differential on every kernel class
  as `1 ⊗ dh`, using inverse polynomial coordinates. Since kernel classes
  generate the quotient, this fixes exactly δ. The helper `delta` is this
  differential expressed as a `B`-linear morphism in the actual modules.
- `faceDifference C f x` is the literal polynomial-coordinate value of
  `d₀x-d₁x`. `face_mem_kernel` proves its evaluation is zero for every x, so
  the class formula never relies on an uninhabited proof premise.
- `rho P` is a morphism from the actual tensor module `M₁` to the actual
  conormal module. Consequently it is well-defined and `B`-linear.
  `System.rho_formula` and `Projection.neg_component` specify
  `ρ(b ⊗ dx)=b[d₀x-d₁x]` for every x and b, with kernel membership supplied
  by `face_mem_kernel`.
- `System.delta_rho` is `rho ≫ delta = boundary ... 0`, namely δρ=∂₁.
  `System.rho_partial` is `boundary ... 1 ≫ rho = 0`, namely ρ∂₂=0.
- `Projection.map` is the actual cochain morphism `K → target`.
  `zero_component` is the identity on `M₀` under `degreeIso` and `zeroIso`.
  `rho` is exactly its degree -1 component in tensor/conormal coordinates;
  `other_components` specifies zero for every other degree. `otherTerms`
  specifies that the target terms in all these other degrees are zero objects.
- `TargetMap.map` is a cochain map into the restriction of the target complex
  along `q.right : B → B'`, hence every component is `B`-linear or,
  equivalently before restriction, `q.right`-semilinear. `kernel_mem` supplies
  kernel membership for every source class. `conormal_formula` fixes its
  action to `[h] ↦ [standardSquareMap q 0 h]`. `tensor_formula` fixes the
  degree-zero action to `b ⊗ dx ↦ β(b) ⊗ d(t₀x)` for the recorded standard map.
  Zero terms force all other components. `System.naturality` is an equality
  of cochain maps `c ≫ C(q) = K(q) ≫ restrict(c')`, not a homotopy or an
  equality merely after passing to a derived category. The incoming `K(q)`
  is the exact dependency's `C.differentialMap (C.standardMap q)`.

Dependency declarations used:

- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Coherence`, `Augmentation`, `DifferentialModel`,
  `standardTerm`, `standardAugmentation`, `standardFace`, `standardSquareMap`,
  `differentialTerm`, `differentialGenerator`, `differentialComplex`,
  `complexGenerator`, `restrictComplex`, and the structure's recorded standard
  and differential maps. Read its full source and existence theorem docstring.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation`;
  read the type, construction and universal-property signatures/docstrings.
  The module-category differential notation is inherited from the coherence
  dependency and uses exactly these differentials.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`,
  `MvPolynomial.algHom_ext`, `MvPolynomial.aeval`, and `aeval_X`; these are
  the recorded polynomial definition and universal property underlying the
  standard-resolution dependency, not new polynomial-algebra definitions.
- Proof dependency `lem-weil-pbc-module-base-change-universal-property` is the
  existing `LinearMap.liftBaseChangeEquiv`, `liftBaseChange`,
  `liftBaseChange_tmul`, `liftBaseChangeEquiv_symm_apply`. Their current source
  is `Mathlib.RingTheory.TensorProduct.Basic`, lines 40–66 (the node's older
  file hint says `LinearAlgebra/TensorProduct/Basic`; declaration names and
  signatures are usable unchanged). This module is a plain proof import.
- Mathlib `Algebra.Generators.self` and `.toExtension`
  (`RingTheory/Extension/Generators.lean`, lines 167–182),
  `Algebra.Extension.Cotangent`, its module instance, and `.mk`
  (`RingTheory/Extension/Basic.lean`, lines 326–430) provide the actual
  quotient. Read those definitions and their docstrings. The already landed
  general naive-comparison module cannot be imported here: its node uses this
  item in its proof. The helpers in this delivery only specialize Mathlib's
  existing quotient to the standard evaluation map and expose its classes;
  they introduce no alternative general conormal or naive-complex definition.

Edge cases checked against the formulas before drafting: zero target ring B,
zero source ring (which then forces zero target), the identity ring map A=B,
characteristic two (the alternating signs still mean additive inverses),
infinite variable sets, noninjective and nonsurjective maps α and β, identity
squares, and arbitrary changes in characteristic. No argument requires a
nonzero quotient or finite generating set. The kernel-class and face-kernel
fields include every kernel element, and no edge case is excluded by a
conditional premise on a face difference. The tensor convention introduces
no flatness hypothesis.

Searches actually run through `batch2/msearch.py` for this item:

- LeanFinder: `standard simplicial polynomial cotangent resolution chain
  projection to conormal complex face differences`. Eight hits, including
  `Algebra.PreSubmersivePresentation.cotangentComplexAux`,
  `Algebra.Generators.H1Cotangent.δAux`, `AlternatingFaceMapComplex.objD`,
  and `NormalizedMooreComplex.obj_d`. None states this projection with strict
  ring-square naturality. These provide presentation or boundary constructions.
- Loogle: `Algebra.Extension.cotangentComplex`. Twelve hits, including the
  general conormal differential and `.Cotangent.map_sub_map`. Read
  `Extension/Cotangent/Basic.lean` lines 45–67 and 249–288: the latter supplies
  a difference map for two extension maps, but neither its boundary-annihilation
  assertion nor strict naturality of this standard-resolution projection.
- Grep: `standard.*resolution|face.*derivation|cotangentComplex`, subdirectory
  `RingTheory`. Twenty-five hits, primarily the extension cotangent APIs,
  scalar extension, and polynomial cotangent bases; no exact statement.
- LeanSearch: `standard cotangent resolution face difference chain map
  conormal ideal modulo square strict naturality`. Eight hits, including
  `Algebra.Extension.Hom.sub`, `Ideal.Cotangent`, `Ideal.mapCotangent`, and
  `Algebra.Extension.Cotangent.map_sub_map`. They confirm reuse of the actual
  quotient; they do not supply the entire node's assertion.
- `rg -n` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `standard.*[Cc]otangent|[Cc]otangent.*[Pp]rojection|` followed by the exact item
  id and `face.*[Dd]ifference`: existing coherence and general naive-comparison
  interfaces, sheafwise projection data, and unrelated occurrences. Read
  `NaiveCotangentComparison.lean` in full and the sectionwise projection in
  `Topology/ZariskiSheafAlgebraExtensionExt.lean` lines 194–234. The former
  depends on this item; the latter is for a sheaf comparison and does not state
  this ring-resolution projection with these two chain identities.
- Searches of both source roots and `dag/lean_names_upstream.json` for the new
  namespace and module name found no declaration collisions. The exact item
  id was included in the search of both source roots; there was no existing
  module attached to this item.

Validation: `batch2/scompile.py Q23 lem-trf-standard-cotangent-chain-projection`
compiled the complete file in module mode, both its sandbox and library module
names, cleanly (10.2 s and 11.6 s). A first elaboration found a parenthesization
error on an isomorphism's `.hom` and the reserved keyword `partial` used as a
name; both were repaired (`boundary` is the final name). No mathematical
statement changed in that repair. Direct imports of the two recorded Mathlib
statement dependencies were then made explicit before final preflight.

## Second reading by Q23

This is the dispatcher's single-worker self-delivery route; no second agent was
started. Independent review belongs to the maintainer, as the task brief says.
A separate final pass by this worker reopened the original node and full module:
`Projection.differential_formula` uses every kernel class, `face_mem_kernel`
ensures the ρ formula is nonvacuous, `delta_rho` and `rho_partial` have the correct
composition order, and `naturality` is in the category of complexes over B with
the target restricted along β. The degree-zero component uses the canonical
coordinate isomorphism, not an arbitrary linear endomorphism. The main theorem
has no extra algebraic hypothesis; the inherited coherence parameter is available
from its dependency for arbitrary rings. The seven source proof steps and each
hypothesis/clause are matched above. No additional mismatch was found.
