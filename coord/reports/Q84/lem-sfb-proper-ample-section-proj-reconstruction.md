## Worker report

Item: `lem-sfb-proper-ample-section-proj-reconstruction`.
Module: `Sheaf.AlgebraicGeometry.ProperAmpleSectionProjReconstruction`.
Main declaration: `AlgebraicGeometry.Scheme.Modules.proper_ample_section_proj_reconstruction`.
The only postponed theorem is that declaration, with proof `by sorry`. Its docstring gives
all eight node-proof steps and their dependencies. Five auxiliary Prop definitions unpack
clauses of this same theorem; they contain actual propositions, no postponed data and no
second section-algebra, pullback, tensor-power, nonvanishing-locus or Proj construction.

The node's statement, proof, proof_deps, source and other metadata are unchanged. The two
already recorded definition owners `def-sfb-relative-proj-iso-of-graded-iso` and
`def-sc-tensor-pullback-power-comparison` were added to stmt_deps for the explicit Proj
comparison and power comparison appearing in the statement. No new node is needed.

Clause-by-clause correspondence:

* The schemes S and X are arbitrary `Scheme.{u}`; f is `f : X ⟶ S` with `[IsProper f]`.
  There is no quasi-compactness, quasi-separatedness or Noetherian hypothesis on S.
* The invertible module is `L : X.Modules` with `[L.IsInvertible]`. Relative ampleness
  is `hample`: every affine open V of S has ample tensor pullback of L along the
  inverse-image open immersion. Its existential invertibility proof supplies exactly
  the proof argument of the existing `IsAmple`; it is not extra mathematical data.
* The full section algebra is the existing `RelativeSectionAlgebra f L`. Its
  `sectionEquiv V n` identifies its homogeneous piece with sections of `L.tensorPow n`
  on `f ⁻¹ᵁ V`; its `smul`, `one`, `mul` and `restriction` fix the actual structural
  scalar action, degree-zero unit, tensor multiplication and restriction maps.
  `A.data : S.GradedAlgebraData` requires genuine degreewise base change on affine
  restrictions, i.e. the quasi-coherent affine-basis presentation, not arbitrary rings.
* Quasi-coherence of the underlying sheaf sum is also an explicit conclusion:
  `(∐ fun n : ℕ ↦ (pushforward f).obj (L.tensorPow n)).IsQuasicoherent` in
  `IsProperAmpleReconstruction`. This is precisely the module sum underlying the
  graded sheaf algebra, with the homogeneous multiplication fixed by A above.
* Degree zero remains `A.sectionEquiv V 0`, hence sections of `L.tensorPow 0 = O_X`
  on `f ⁻¹ᵁ V`. No equality of that ring or sheaf with O_S is stated or assumed.
* Reconstruction is `r : X ≅ A.data.relProj`, with `A.IsCanonicalMap r.hom` in
  `IsProperAmpleReconstruction`. This recorded predicate includes
  `r.hom ≫ A.data.relProjHom = f` and the normalized evaluation chart formula in
  every trivialization and every homogeneous degree, including zero.
* On each affine V, `q V : (f ⁻¹ᵁ V.1).toScheme ≅ Proj (A.data.grading V)` has
  `q V` followed by `relProjι V` equal to the restriction of r, and
  `(q V).hom ≫ A.data.toOpen V = f ∣_ V.1`; it is therefore an isomorphism over V.
  `HasReconstructionChart` identifies `A.data.obj V` with the existing full
  `InvertibleSectionRing` of the restricted module by the evaluated homogeneous
  sections and `DirectSum.of`. This additive isomorphism also respects the tensor
  product multiplication because it is fixed by `A.mul`, and respects the unit by
  `A.one`. Thus the Proj is of the full section ring, not of a coordinate subring.
* For each d > 0 and s in degree d, `HasReconstructionChart` states that the preimage
  of `Proj.basicOpen ... s.val` is the existing `nonvanishingLocus` of its evaluated
  section. For every a >= 0 and t in degree a*d, its second formula says the
  pullback of `Proj.awayToSection ... (HomogeneousLocalization.Away.mk ... t ...)`,
  multiplied by the restricted evaluated section `s^a`, is the restricted evaluated t.
  Nonvanishing makes this denominator section a generator, so the multiplication
  equation is exactly the quotient formula; it also works on an empty open.
  The quantified proof h is `⊤ ≤ U.ι ⁻¹ᵁ U` for U = f inverse-image V. It always
  exists by `Scheme.Opens.ι_preimage_self` and only lets the recorded evaluation
  interface restrict its section to all of U. It is no extra hypothesis and does
  not make the chart condition vacuous.
* For every affine inclusion W <= V, the final two clauses of
  `IsProperAmpleReconstruction` identify q_V after inclusion with q_W followed by
  the canonical Proj restriction, and identify their inverses in the reverse order.
  Applying these clauses to each affine refinement of V intersect V' gives precisely
  agreement on overlaps without supposing the overlap is affine.
* `HasPolarizedNaturality` quantifies over X', f', L', another section algebra A',
  its reconstruction r', an isomorphism `h : X' ≅ X` with `h.hom ≫ f = f'`, and
  `lam : (tensorPullback h.hom).obj L ≅ L'`. The other reconstruction exists by the
  same main theorem when f' is proper and L' relatively ample. Conversely, an h and
  lam as above already transport the original properness and relative ampleness;
  their repetition is unnecessary. Quantifying over all reconstructions avoids any
  arbitrary choice of a particular representation of the quasi-coherent algebra.
* The unique `phi : A.data ≅ A'.data` is characterized by `IsPolarizedIso`: in every
  affine open and every degree, its homogeneous section map is exactly the actual
  `tensorPullbackSection` (1 tensor s), restricted along the over-S open inclusion,
  then `boundaryPullbackPowIso`, then `boundaryTensorPowIso lam`.
  Invertibility, O_S-algebra linearity and multiplicativity are in the type of phi
  (the existing category of graded algebra data), not added assumptions.
* Naturality is literally
  `r'.hom ≫ (GradedAlgebraData.relProjIsoOfIso phi).hom = h.hom ≫ r.hom`, i.e.
  `Proj(phi) ∘ r_L' = r_L ∘ h` in right-to-left mathematical notation.
* `PolarizedCoherence` fixes the identity polarization with
  `tensorPullbackSectionId` and states that its graded isomorphism and Proj
  isomorphism are identities. For h and k over S, it fixes the composite
  polarization using `tensorPullbackSectionComp`, `(tensorPullback k).mapIso lam`
  and mu; the associated omega is `phi ≪≫ psi`, and its Proj is
  `relProjIsoOfIso psi ≪≫ relProjIsoOfIso phi`. The naturality statement applied
  to the composite agrees with substituting the two individual naturality equalities.
* There is no nodality, curve dimension, Noetherian, finite generation, degree-one
  generation or arbitrary base-change assertion anywhere in these predicates or
  the main theorem. Base change inside `GradedAlgebraData` concerns affine open
  restrictions, not arbitrary changes of base scheme.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its Hom and opens.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
* `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `tensorPow` and its tensor-power addition comparison.
* `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`,
  `Scheme.Modules.nonvanishingLocus`.
* `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`: `GradedSheafAlgebra`;
  the theorem uses its equivalent quasi-coherent affine-basis presentation already
  fixed by the recorded relative section-algebra and relative Proj dependencies.
* `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`:
  `Scheme.IsQuasiCoherentAlgebra` is quasi-coherence of the underlying module;
  that property of the actual direct sum is explicit in the conclusion.
* `WeilConjectures.AlgebraicGeometry.InvertibleSectionRing`:
  `InvertibleSectionRing`, `SectionRingComponent`, tensor-product multiplication.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullback`,
  `tensorPullbackSection`, `tensorPullbackSectionAdjunction`,
  `tensorPullbackSectionId`, `tensorPullbackSectionComp`.
* `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic` and its
  `GradedAlgebraData` import: `Scheme.GradedAlgebraData`, its graded Hom category,
  `relProj`, `relProjHom`, `relProjι`, `toOpen`, and canonical restriction maps.
* `Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion`:
  `Scheme.Modules.RelativeSectionAlgebra`, `evaluate`, `IsCanonicalMap` and the
  existing relative-ampleness criterion.
* `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`:
  `Scheme.GradedAlgebraData.relProjIsoOfIso` (existing definition owner added).
* `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`:
  `Scheme.Modules.boundaryPullbackPowIso` and `boundaryTensorPowIso`; these are
  genuinely general comparisons despite the module name. Existing comparison owner
  added to stmt_deps; no independent comparison definition introduced.

Proof dependency imports include the recorded ordinary canonical-map, localization,
ample separatedness, invertible tensor-pullback, properness, separated Proj, and gluing
modules. `lem-trf-qcqs-line-section-algebra-evaluation` and
`lem-trf-local-proj-isomorphism-compatibility` currently have no Lean record or closed
upstream declaration; no import is invented for these future proof dependencies.
The main theorem imports and builds on the stated relative-ampleness criterion.

Sources read: local Stacks `morphisms.tex`, labels
`lemma-characterize-relatively-ample` (01VJ), `lemma-proper-ample-is-proj` (0C6J);
`constructions.tex`, labels `lemma-morphism-proj` (01MY) and
`lemma-morphism-proj-transitive` (01MZ). 0C6J allows universally closed f; the node
specializes it to proper f and the Lean preserves that exact node hypothesis.

Edge cases checked before writing and in the final reading:

* Empty X and empty affine base opens: empty Proj and its charts are allowed;
  section rings and localization rings may be the zero ring. No Nonempty, nontrivial
  section or nonzero denominator assumption is made.
* Zero numerator and zero homogeneous section: basic opens/nonvanishing loci may be
  empty; the fraction multiplication equality remains well typed and correct.
* Exponent a = 0 and homogeneous degree n = 0: the fraction has unit denominator,
  and the polarized map is normalized structure-sheaf pullback. d = 0 is excluded
  only in standard-open assertions, exactly as in the node.
* A_0 different from O_S, e.g. a finite affine proper morphism with ample trivial
  line bundle: section degree zero is f_*O_X, never replaced by the base ring.
* A unit rescaling of lambda changes degree n by its nth power; it is retained in
  `IsPolarizedIso`. In degree zero that power is the identity, as required.
* Identity h and composite k,h: both use the normalized adjunction comparisons,
  retaining equality on sections rather than merely abstract isomorphism classes.
* Nonreduced schemes and arbitrary base overlaps: scheme morphisms and section
  comorphisms are tested, not only point maps; affine refinements handle overlaps.
* Arbitrary scheme universe u and arbitrary base S: no independent test universe,
  dimension, characteristic, field or Noetherian restriction introduced.

Searches actually run with msearch.py, group Q84 and this item:

* LeanFinder: “Proper scheme with relatively ample invertible module is canonically
  the relative Proj of its full section algebra naturally under polarized
  isomorphisms”; also “Proper scheme ample section ring reconstruction”. Eight
  hits include Proj, fromOfGlobalSections and its chart formulas; none state
  reconstruction or polarized naturality.
* Loogle: `"Proj", "IsProper"`. One hit,
  `Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat`; it assumes a finite
  type graded ring and proves properness of its existing Proj, not reconstruction.
* Mathlib grep: `section.*[Rr]ing|[Rr]elative[Pp]roj|proj.*[Aa]mple`, subdirectory
  AlgebraicGeometry. Twenty-five capped hits are Proj structure-sheaf section
  operations, affine section rings and Noetherian results; no match.
* LeanSearch: “A proper scheme with a relatively ample invertible sheaf is
  canonically the relative Proj of its full section algebra”. Eight hits include
  Proj.fromOfGlobalSections, Proj.fromOfGlobalSections_resLE, separated Proj,
  Proj.toSpecZero and awayι; no reconstruction or naturality theorem.
* rg in the exact read clone's lean/WeilConjectures and lean/Sheaf:
  `proper.*[Aa]mple|[Aa]mple.*[Pp]roj|lem-sfb-proper-ample-section-proj-reconstruction|[Pp]olarized`.
  Existing ample canonical-map, relative-ampleness criterion, and projectivity
  declarations have different conclusions. No existing declaration matches this node.
  Targeted searches for `RelativeSectionAlgebra`, `relProjIsoOfIso`,
  `boundaryPullbackPowIso`, `boundaryTensorPowIso`, `tensorPow` and
  `InvertibleSectionRing` located the recorded interfaces used above.

No statement dispute, node correction, missing notion or dependency interface repair.
All compilation used the prescribed scompile.py, sandbox and module modes. The final
file compiles cleanly in both modes (3.1 / 3.4 seconds); only one theorem is postponed.

## Second reading by Q84

This is a separate self-reading, not a claim of an independent worker review: the
assignment prohibits starting other agents, and the maintainer provides the independent
review. I reopened the node and final module and checked the hypothesis/clause mapping
above. Two omissions in the first draft were repaired: an explicit quasi-coherence
conclusion for the direct sum, and an explicit identification with the full
InvertibleSectionRing on affine base opens. The latter uses its homogeneous additive
identification; multiplication and the unit already agree by A.mul and A.one, avoiding
an additional restricted-invertibility instance parameter in the chart predicate.
I checked the direction of every affine inclusion, inverse restriction, polarized
section map, naturality composite and contravariant Proj composite. No remaining
mismatch was found. There is no proof in the delivery other than the expected sorry.
