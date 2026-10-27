## Worker report

NW, 2026-10-22. Stage 2 of lem-sfb-standard-proj-twist-tensor. The live node already
has Q19's independently reviewed stage-1 split, but has no Lean record. Its natural-language
statement, seven proof steps, dependencies, and review records are preserved verbatim.
The sandbox contained only dispatcher briefs when this repair started: there was no
preserved module, node copy or report to repair. This delivery supplies the missing stage-2
statement; it does not resplit the reviewed node.

The module Sheaf.AlgebraicGeometry.StandardProjTwistTensor states
AlgebraicGeometry.Proj.standardProjTwistTensor, with one sorry proof. Its three auxiliary
Prop-valued definitions package the chart equations and canonical-map equations used in
this statement. They construct no associated sheaf, twisting sheaf, tensor product,
localization or map by choice. These are helpers for this node's existing notions, not
independent new notions. Each has a source/blueprint docstring and is recorded in
lean.declarations. There are no new DAG nodes or dependency repairs.

Hypothesis-by-hypothesis reading:

- S is an arbitrary nonnegatively graded commutative ring: `{S : Type u} [CommRing S]`,
  `𝒜 : ℕ → AddSubgroup S`, `[GradedRing 𝒜]`. The scheme X is the existing `Proj 𝒜`.
- The degree-one standard opens cover X: `cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1,
  x ∈ basicOpen 𝒜 f`. This is exactly the cover assumption, not generation or finiteness.
- M is any graded S-module: `{M : Type u} [AddCommGroup M] [Module S M]`,
  `𝓜 : ℤ → AddSubgroup M`, `h𝓜 : DirectSum.IsInternal 𝓜`, and `hsmul` explicitly
  asserts S_k M_n is contained in M_(k+n). No finite-generation, flatness, reducedness,
  domain or Noetherian hypothesis is present. Universes are explicit, with the common
  universe convention of the recorded gradedModuleSheaf_exists and Scheme.Modules.
- The existing existential associated-sheaf interface supplies F n representing M(n).
  `F : ℤ → (Proj 𝒜).Modules`, `chart`, and `hF` specify these representatives just as
  gradedModuleSheaf_exists and the already landed finite_graded_module_section_tail do.
  The helper IsStandardProjShiftSheaf is the conjunction of chart injectivity, image
  exactly `degreeZeroFractions` for `𝓜 (n+k)`, scalar compatibility through
  `awayToSection`, and the canonical restriction formula for every g^e = c f.
  Thus n uses M(n)_k=M_(n+k), including negative n. These parameters are representation
  data supplied by the dependency, not additional mathematical hypotheses on M.
  The theorem works with every representative carrying those identifications.

Clause-by-clause reading:

- Invertibility for every integer n is the first conjunct,
  `∀ n : ℤ, (twist 𝒜 n).IsInvertible`, using the recorded scheme-module predicate.
- Twist multiplication is the existing `twistTensorIso 𝒜 cover a b`; its type is an
  actual isomorphism `twist 𝒜 a ⊗ twist 𝒜 b ≅ twist 𝒜 (a+b)`.
  The next conjunct identifies its value on a tensor of sections with the product
  of their values in every ordinary prime localization. Therefore on the fractions
  u/f^r and v/f^s it is uv/f^(r+s), not an unspecified isomorphism.
- The next three conjuncts are its left unit, right unit, and associativity equations
  as equalities of sheaf morphisms. The unit identification is `unitIsoTwistZero`;
  the unitors and associator are those of the existing sheaf tensor. `eqToHom` only
  transports the integer equalities 0+a=a, a+0=a and (a+b)+c=a+(b+c).
- The existential `mult : ∀ a b : ℤ, F a ⊗ twist 𝒜 b ⟶ F (a+b)` constructs the
  canonical comparison maps. Taking a=0 gives precisely alpha_(M,b) in the node.
  Allowing a applies the same assertion to M(a), with the equality of the double
  shift fixed by the same chart descriptions; it does not impose a new condition.
- IsStandardProjTensorMultiplication fixes these maps on fractions. If chart(x)=y/f^r
  and t is the existing twist section v/f^s (its equality is checked at every point),
  chart(mult(tmulSection x t))=(v • y)/f^(r+s). Neither numerator degree needs an
  added assumption: x and t are actual sections of the prescribed graded sheaves.
- `∀ a b, IsIso (mult a b)` says the actual canonical arrows are isomorphisms.
- The following two conjuncts are their right unit and associativity equations,
  with the existing twist multiplication, unitor, associator and integer transports.
- The final conjunct expresses naturality for every N, grading 𝓝, sheaf family G
  with the same associated-sheaf charts, degree-preserving S-linear phi, and induced
  maps chi on those sheaves. IsStandardProjGradedMap specifies chi by y/f^r ↦ phi(y)/f^r.
  Every canonical multiplication beta for G then satisfies
  `(chi a ▷ twist 𝒜 b) ≫ beta a b = mult a b ≫ chi (a+b)`.
  Applying the theorem to G supplies beta; no arbitrary-map or isomorphism assumption
  substitutes for the canonical construction. Functoriality of chi is the recorded
  tilde_functorial theorem. This also applies to M=S(c), so the module and twist
  coherence laws concern the same canonical multiplication characterized on fractions.

Dependency declarations read and reused:

- def-pc-proj (Mathlib leaf): Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic and
  Scheme, AlgebraicGeometry.Proj, AlgebraicGeometry.projIsoSpec, ProjectiveSpectrum.basicOpen.
- def-weil-pbc-proj-twisting-sheaf: the existing
  WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules,
  AlgebraicGeometry.Proj.twist and Proj.unitIsoTwistZero. Its record explicitly
  delegates general M-tilde to gradedModuleSheaf_exists, rather than constructing
  an independent tilde object. TensorIso also imports Modules publicly.
- def-sc-invertible-module: WeilConjectures.AlgebraicGeometry.Modules.Invertible,
  Scheme.Modules.IsInvertible. This class is available publicly through Modules.
- def-pur-sheaf-tensor-product: the recorded
  Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses is imported publicly.
  The tensor is the existing sheafification tensor, with the public upstream
  Scheme.Modules.tmulSection from Modules.TensorSection; no second tensor is defined.
- The arbitrary-module chart specification follows
  WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists,
  AlgebraicGeometry.Proj.gradedModuleSheaf_exists. Every clause used was read, including
  the chart scalar and restriction laws and the uniqueness clause.
- The binary twist isomorphism and degree-one local fractions are from
  WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorIso and TensorObj,
  Proj.twistTensorIso, Proj.twistPowSection and Proj.pow_mem_primeCompl.
- Stated proof dependencies are imported without public: ProjTildeFunctorial
  (Proj.tilde_functorial), ProjStandardOpenProperties (Proj.standardOpenProperties),
  Mathlib.Topology.Sheaves.SheafCondition.Sites (TopCat.Sheaf.restrictHomEquivHom,
  extend_hom_app, hom_ext, isIso_iff_isIso_basis),
  Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
  (PresheafOfModules.sheafification), upstream TensorClosed (SheafOfModules.tensorClosed),
  and SheafificationBilinearExtensionUniqueness
  (PresheafOfModules.unique_bilinear_sheafification_extension).
  The full seven-step proof from the reviewed node is present in the theorem docstring,
  including the iterated tensor/bilinear uniqueness argument repaired by Q19's reviewer.

Source and edge cases:

Read literature/stacks-project/constructions.tex, equations equation-multiply and
-equation-multiply-more-generally, lemma-when-invertible (01MS), and lemma-apply-modules
(01MT), including their proofs. The source agrees with the unchanged node.
Checked M=0, torsion modules M=S/(f), negative a,b, n=0, S with zero divisors,
a nilpotent degree-one f (its chart is empty), and empty Proj including rings
concentrated in degree zero. No nonemptiness or finite-cover assumption is made.
For S=k[t] with deg(t)=2, the degree-one cover fails while O(1) can vanish; this
confirms that the cover is necessary and has not been dropped. Fraction tests over
empty charts are still meaningful because the chart image and injectivity conditions
identify their section modules, and the relevant localized graded components are zero.
The associativity equations explicitly transport addition indices, so negative
indices are treated identically to positive indices.

Searches made:

- msearch.py leanfinder: "For any graded module on Proj covered by degree one opens
  the sheaf of its shift is its tensor product with the twisting sheaf" returned
  Proj structure-sheaf and scalar multiplication declarations, no arbitrary-module
  comparison.
- msearch.py leansearch: "The associated sheaf of a shifted graded module on Proj
  is the tensor product with the twisting sheaf" returned ModuleCat.tilde,
  tildeInModuleCat (affine Spec), Proj.structureSheaf, Proj.mul_apply, Scheme.Modules,
  and structure-presheaf declarations. The affine hits are different objects.
- msearch.py loogle: "AlgebraicGeometry.Proj.twist" reported unknown identifier;
  repeated with the valid query "AlgebraicGeometry.Proj, TensorProduct", zero hits.
- msearch.py grep: "twist|Twist|gradedModule|GradedModule" in
  AlgebraicGeometry/ProjectiveSpectrum, zero Mathlib hits.
- rg of live WeilConjectures and Sheaf for graded-module shifts, associated sheaves
  and twist tensor comparisons found twistTensorIso and nonempty_tensorObj_twist_iso,
  which supply only the structure twists, as Q19 also established. The landed
  FiniteGradedModuleSectionTail uses the same chart interface but states eventual
  section recovery, not this comparison. ProjShiftedFreeTwist is about finite free
  sums and the projective line; it does not state the item.
- rg of WeilConjectures for the exact blueprint id returned no implementation.
  rg for the four proposed declaration names in WeilConjectures, Sheaf and
  dag/lean_names_upstream.json returned no existing declarations.

No statement correction or statement dispute. No file in the shared read-only project
was directly changed. Compilation uses only the prescribed scompile.py wrapper;
both the sandbox and its module-path compilation passed with no errors or warnings.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
