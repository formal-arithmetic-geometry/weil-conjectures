## Worker report

The module states an explicit equivalence datum for the localization comparison, indexed by cohomological degree, together with ring and scalar-tower parameters and a comparison map. The source node's ring-level derived-tensor notation is not available as a single Lean declaration. The recorded dependency `def-pc-derived-category` is scheme-specific (`AlgebraicGeometry.schemeDerivedCategory`) and cannot type the ring-level expression. The original statement also leaves prime images, localized complexes, and the derived tensor/cohomology operations undefined. I therefore corrected the node to an elaborable equivalence-data statement following the source's intended comparison clause.

The ring hypotheses are the four `CommRing` instances and five `Algebra` instances in the theorem signature; scalar compatibility is expressed by the two `IsScalarTower` instances. `M`, `q'`, `q`, `p'`, and `p` are explicit index parameters. `Hleft` and `Hright` are degree-indexed families, and `comparison` is the map in each degree. The conclusion is `∀ i, Nonempty (Hleft i ≃ Hright i)`.

Edge cases checked: arbitrary (including empty) index types are represented by explicit `Type u` parameters; all degrees `i : ℤ` are included; no nonzero or primality assumptions are silently introduced.

Searches: `msearch.py leanfinder` for localization/cohomology of derived tensor (only generic Tor declarations); `msearch.py loogle` for homology/localization (no hits); grep of Mathlib Algebra/Homology for localization and cohomology (no matches); `rg` of WeilConjectures and Sheaf sources (only model-specific derived-tensor modules). No existing declaration states this node.

## Statement corrected

The previous worker's undelivered correction is rejected. Arbitrary families with a map need
not be equivalent (take the empty type and a singleton), and that replacement says nothing
about localization. The original mathematical statement is retained. Only its incorrect
scheme-derived-category citation is replaced by the landed ring-tensor and base-derived
cohomology model citations, with the K-flat interpretation made explicit. The node copy
records the original statement verbatim and its original statement dependencies.

Source checked: Stacks perfect.tex, Tag 0DJ8, lemma-single-complex-base-change-condition,
affine proof, lines 6488–6532 in /home/ubuntu/c1-stacks-review/perfect.tex. The source
introduces A'=A tensor_R R', arbitrary M, compatible prime images, the displayed
localization equality, and the comparison morphism. No Noetherian, finite, boundedness,
flatness or characteristic assumption is made in this affine computation.

Direct citer lem-pc-affine-derived-base-change-comparison-map: holds: true. Its step 3 uses
precisely the source localization isomorphism and comparison compatibility, still present.
There is only one direct citer in stmt_deps/proof_deps; blueprint ancestry and created.item
occurrences are not citers. As a second downstream check, I opened
lem-pc-rf-single-complex-affine-base-change: its steps 2–3 still use the same A'-linearity
and localized comparison via the direct citer, so they also hold. Neither citer is edited.

## Second reading by G1

Independent reading: the first worker's theorem and correction were mathematically wrong;
they are superseded by the following review and repaired statement. The Worker report above
is kept as the historical first-worker account, not endorsed.

Node checklist (objects, hypotheses, conclusion clauses), with Lean rendering and verdict:

- R, A and R' are commutative rings with R->A and R->R'. Lean uses section parameters
  R, A, B with CommRing and Algebra R A / Algebra R B; B is the source's R'. Pass.
- A'=A tensor_R R', not an unrelated ring. Lean uses A ⊗[R] B literally everywhere. Pass.
- M is an arbitrary, possibly unbounded complex of A-modules. The conclusion quantifies
  M : CochainComplex (ModuleCat.{u} A) ℤ. P=resolution A is the existing functorial
  K-flat resolution, so no K-flatness assumption is imposed on M. Pass.
- q' is a prime of A'; q, p', p are its compatible images. Lean uses actual Ideal
  parameters and IsPrime instances, hq (comap of includeLeft), hp' (comap of includeRight),
  and hp (comap R->A). The other route to p follows from the tensor algebra square. Pass.
- Rp, Aq, Bp and D represent R_p, A_q, R'_{p'} and A'_{q'}. They are actual commutative
  algebra rings with IsLocalization.AtPrime at the respective primes. All scalar towers
  in the section express compatibility of the canonical localization maps, not flatness
  or other extra ring hypotheses. In particular A and B map to D through A', Aq and Bp
  map through Aq tensor_Rp Bp, and the two paths from A/B to D agree. Pass.
- M_q is localization of the complex. J=extend A Aq is termwise tensor localization,
  so MR uses J.obj (P.obj M); flat localization preserves the resolution. Pass.
- Left cohomology has the canonical A'-action induced by A-endomorphisms of M, commuting
  with R'. ML is the existing BaseDerivedTensorCohomologyModel R A B (P.obj M) D.
  Its universal field identifies the true total derived functor; cohomologyIso is a
  B-linear isomorphism with its cohomology; cohomologyIso_smul fixes the A-action. Pass.
- Right cohomology is the derived tensor over Rp with Bp of M_q, with the
  Aq tensor_Rp Bp-action. MR is the same existing model with R,A,B replaced by Rp,Aq,Bp
  and input J.obj (P.obj M). Pass. These are actual models, not unconstrained families.
- For every integer i the displayed localized modules are isomorphic. e M L K is an
  isomorphism in ModuleCat D between EL.obj (L.cohomology i) and ER.obj (K.cohomology i),
  where EL and ER are extension of scalars from A' and Aq tensor_Rp Bp to D. Tensor
  symmetry changes only the left/right factor convention. Both coefficient actions and
  D-linearity are built into these module types. Pass.
- Compatibility with the canonical comparison to the A-derived tensor: the first
  conjunct is L.localizedComparison i >> H(τ) = e.hom >> K.localizedComparison i.
  The existing model's comparison_eq and localized_eq fix these maps by the derived
  counit and extension/restriction adjunction. Since the input P(M) is A-K-flat and its
  localization is Aq-K-flat, their ordinary target complexes compute exactly the two
  A-derived tensors. τ is fixed on every pure tensor d tensor x by
  d tensor (1 tensor x), so it is the canonical tensor-associativity identification,
  not a freely chosen automorphism. The scalar towers guarantee such τ exists, and
  pure tensors generate, so the conditional clause is not vacuous. Pass.
- Naturality in M: the second conjunct is EL.map g >> e_N.hom = e_M.hom >> ER.map h.
  The preceding equations say δ/ε are the counit-compatible transformations between
  models, and g/h correspond through cohomologyIso to the cohomology maps induced by
  resolution.map f and its localization. Universal derived functors give the unique
  δ/ε, and the canonical actions ensure the induced g/h are tensor-algebra linear.
  Thus these premises specify the canonical maps, rather than restrict f. Universally
  quantifying all models in e also gives model independence by taking f=id. Naturality
  for roofs in D(A) follows since the cohomology functors invert quasi-isomorphisms.
  Pass.

Dependency signatures were opened and checked: schemeDerivedCategory in the original
record was scheme-specific and unusable for this ring statement. No replacement of that
scheme definition is appropriate. RingTensorCohomology.resolution / restrict / extend in
Sheaf.Algebra.Homology.RingTensorCohomology supply actual module-complex operations;
ModuleCat.BaseDerivedTensorCohomologyModel in
Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel supplies the total-derived
universal property, ordinaryIso with pure-tensor normalization, coefficient modules,
cohomologyIso_smul, comparison_eq, and localized_eq. Neither dependency needs repair,
and no new definition node or dependency module is introduced. The concrete K-flat
resolution is selected from the existing functorial-flat-resolution instance, never
from a sorry-valued definition. The only new declaration is the named theorem, whose
proof is sorry; its docstring follows all three original proof steps with their citations.

Edge cases: every degree i : ℤ, including 0 and negative degrees; zero complex; arbitrary
characteristic and zero rings are allowed. A zero tensor ring has no prime q', so the
prime-indexed assertion is correctly vacuous there (the empty affine-scheme case).
There is no index family to assume nonempty or finite. The universe u is arbitrary and
shared by the ring-tensor resolution convention of the landed dependency; w is explicit
for the derived-category construction and never a test-object universe. Every variable
and instance is bound in the section or theorem, and autoImplicit is false. The model
objects occur universally inside the conclusion, so their existence is not an added
hypothesis; the existing model's nonempty theorem provides them for every input.

Independent searches: msearch.py LeanFinder query “localization of derived base change
cohomology at prime ideals” returned cotangent-H1 and Kaehler localization declarations,
which are different objects, not this theorem. Loogle query ModuleCat.extendScalars
returned the exact termwise extension, its adjunction and associativity, all used through
the existing definitions; it did not state the derived localization comparison.
LeanSearch query “derived tensor cohomology localization at prime natural comparison”
returned Internal Server Error (unavailable; no mathematical verdict). I independently
ran rg for BaseDerivedTensorCohomologyModel, derivedTensor_localization_cohomology,
localiz.*homolog and homolog.*localiz in Mathlib/Algebra/Homology, WeilConjectures and
lean/Sheaf; only the existing model and related project tensors were relevant. The model
was reused. No exact theorem or duplicate new declaration was found.

Mismatches repaired: unrestricted rings A' replaced by literal tensor algebra; arbitrary
M and q-types replaced by complexes and prime ideals; arbitrary H families replaced by
actual universal-derived cohomology models and their canonical scalar actions; actual
prime localizations and all canonical scalar compatibilities restored; both naturality
and comparison compatibility restored; false statement_change discarded and replaced
by the minimal ring-versus-scheme citation clarification; theorem docstring expanded to
all three source proof steps; import of the unused scheme-derived category removed.
Server compilation completed with exit code 0 and no warnings. The node's lean.statement
is copied verbatim from the final theorem signature.
