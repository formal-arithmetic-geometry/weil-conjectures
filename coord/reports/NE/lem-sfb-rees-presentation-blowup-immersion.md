## Worker report

The new module `Sheaf.AlgebraicGeometry.ReesPresentationBlowupImmersion` states
`AlgebraicGeometry.Scheme.IdealSheafData.rees_presentation_blowup_immersion`.
Its sole proof is `sorry`. It defines no new objects and preserves the DAG statement,
statement dependencies, proof and proof dependencies. No dependency repair or new node is needed.

Hypothesis-by-hypothesis correspondence:

- A scheme X is `{X : Scheme.{u}}`, with arbitrary explicit universe u.
- The quasi-coherent ideal is `I : X.IdealSheafData`. This is the recorded ordinary-blowup
  input: the ideals on affine opens with their localization compatibility. The actual ideal
  module sheaf and inclusion are the existing `I.toModules` and `I.toModulesι`.
- Finite type and quasi-coherence of that module are precisely
  `hI : I.toModules.IsQuasiCoherentFiniteType`. Its first projection supplies the instance
  needed by the canonical symmetric graded algebra; its second projection is finite type.
  Finite type is retained even though the immersion construction itself can be more general.
- The ordinary glued blowup B and b are the existing `I.blowup` and `I.blowupMap`, not
  new models or arbitrary witnesses. Its canonical affine chart is `I.blowupι U`, with
  source `AffineBlowup (I.ideal U) = Proj (reesGrading (I.ideal U))`.
- The quasi-coherent graded algebra C is `C : X.GradedAlgebraData`, the equivalent
  affine-basis interface expressly recorded by def-nagata-relative-proj. Its obj, grading,
  algebra instances and coefficient-base-change restrictions present the sections and
  homogeneous pieces of the quasi-coherent graded algebra sheaf. It is not an arbitrary
  diagram of graded rings: its restriction maps satisfy actual degreewise base change.
- The family theta is `θ : C ≅ I.reesData`. In this category its forward components
  `θ.hom.app U` are degree-preserving ring homomorphisms, base-linear by
  `Hom.app_algebraMap`, and compatible with all affine restrictions by `Hom.naturality`.
  The inverse components and inverse identities give exactly the stipulated graded
  R-algebra isomorphisms. Bundling the inverses is equivalent to the given isomorphisms.
  The target `I.reesData.obj U` is definitionally `reesAlgebra (I.ideal U)`.
- The degree-zero normalization and C_0 = O_X require no extra arbitrary identification:
  each base-linear theta component fixes scalar images, and the canonical base map
  `R → reesGrading (I.ideal U) 0` is an isomorphism (`reesGradingZero`). The inverse
  of theta therefore identifies C_0 with R via the unit, so theta is the identity under
  this structural identification. This includes both injectivity and exhaustiveness of C_0.
- Compatibility of theta uses exactly the coefficient restriction stipulated in the
  node: `reesData.res` is `reesGrading.hom` for the structure-sheaf restriction, whose
  underlying polynomial map applies restriction to each coefficient. On D(s) the scalar
  restriction is localization, hence xt^n goes to (x/1)t^n. This holds for every affine
  inclusion, not just a selected cover or principal opens.
- The given morphism is
  `φ : @SymmetricAlgebraSheaf.gradedAlgebraData X I.toModules hI.1 ⟶ C`.
  Its source is the recorded canonical symmetric grading, not a chosen grading.
  It is base-linear, degree-preserving and compatible with affine restriction by the
  existing Hom structure. Its degreewise affine surjectivity is exactly
  `hφ : ∀ U n, Function.Surjective ((φ.app U).gradedAddHom n)`.

Conclusion-by-conclusion correspondence:

- The first two existential witnesses `hθirr` and `hφirr` are proofs of the irrelevant
  ideal conditions needed to call the existing canonical Proj API. These conditions are
  conclusions obtained from the given isomorphism and degreewise surjection, not extra
  assumptions on them. Lifting and summing finitely many homogeneous components gives
  total surjectivity for phi; the existing surjection lemma gives the condition.
- `∃ e : I.blowup ≅ C.relProj` supplies the required isomorphism. The equation
  `e.hom ≫ C.relProjHom = I.blowupMap` says it lies over X.
- For every affine U, the equation
  `I.blowupι U ≫ e.hom = Proj.map (θ.hom.app U) (hθirr U) ≫ C.relProjι U`
  specifies exactly the contravariant Proj morphism of theta_U under the canonical
  ordinary blowup and relative-Proj local identifications. Because theta_U is an
  isomorphism, this morphism is its induced Proj isomorphism. The existing Proj.map
  is the homogeneous-localization construction, so its chart comorphism is
  a/f^m mapping to theta_U(a)/theta_U(f)^m, not an arbitrary local isomorphism.
- Uniqueness is explicitly quantified over *all* `e' : I.blowup ≅ C.relProj` that
  lie over X and satisfy these affine equations. It does not ask that e' additionally
  carry an immersion or any supplementary properties before concluding `e' = e`.
- Arbitrary overlaps are expressed by the equality after `pullback.fst` and
  `pullback.snd` for the two open embeddings `I.blowupι U`, `I.blowupι V`.
  Their pullback is precisely the overlap in B. Neither U intersect V nor this
  overlap is assumed affine. The next equation, for every affine refinement U ≤ V,
  specifies compatibility with the canonical `I.blowupFunctor` transition maps.
- The actual j is the displayed term `e.hom ≫ relProjMap φ hφirr`. Thus applying
  relative Proj to phi and composing with e is part of the statement, not merely an
  existence assertion about an unspecified closed immersion.
- `IsClosedImmersion (e.hom ≫ relProjMap φ hφirr)` is its closed-immersion clause.
- The target of this term is definitionally
  `(@SymmetricAlgebraSheaf.gradedAlgebraData X I.toModules hI.1).relProj`, the same
  P_X(I) used by `IsProjectiveBundle`. Local freeness is not imposed on the ideal.
- The next equation on every affine U says that j_U is precisely
  `Proj.map ((θ.hom.app U).comp (φ.app U)) ...`. Since `Proj.map` is the canonical
  homogeneous-localization morphism, this also specifies its domain charts and its
  fraction formula for the composite theta_U phi_U.
- The final equation says that j followed by the canonical projective-bundle
  projection is `I.blowupMap`, exactly as stated in the node.
- There is no integral, Noetherian or nonzero-ideal assumption anywhere in the signature.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType`, the conjunction of Mathlib's
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`,
  `blowupι`, `blowupFunctor`, and the affine inverse-image/pullback identification.
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`: `GradedSheafAlgebra`;
  `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`:
  `Scheme.IsQuasiCoherentAlgebra` and `QuasiCoherentAlgebra`. Their quasi-coherent
  affine-basis interface is the existing `Scheme.GradedAlgebraData` from
  `WeilConjectures.AlgebraicGeometry.RelativeProj.GradedAlgebraData`, expressly
  recorded by def-nagata-relative-proj. These notions are not redefined here.
- `Mathlib.RingTheory.ReesAlgebra`: `reesAlgebra` (coefficient-in-I^n subalgebra).
- `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`:
  `SymmetricAlgebraSheaf.gradedAlgebraData` (actual symmetric section rings,
  powers of the degree-one inclusion range and actual restrictions).
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `Scheme.GradedAlgebraData.relProj`, `relProjHom`, `relProjι`, `relProjFunctor`.
- `WeilConjectures.Blowup.Affine.Defs`: `AffineBlowup`, definitionally Proj of the
  existing Rees grading, and `AffineBlowup.toSpec`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `IsProjectiveBundle`; the
  target and projection in its definition are exactly the target and projection here.
- The already recorded proof interface
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality` gives
  `relProjMap`, `IrrelevantLE`, `relProjIsoOfIso`, and
  `isClosedImmersion_relProjMap`; this is also the statement's canonical map API.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Rees` gives the canonical
  `I.reesData` and `I.relProjReesIso` used by the ordinary blowup comparison.
- Private proof imports include
  `Sheaf.AlgebraicGeometry.BlowupReesSymmetricPresentation`,
  `Sheaf.AlgebraicGeometry.GradedProjQuotientTwistComparison`,
  `Mathlib.AlgebraicGeometry.AffineScheme` (affine basis), and
  `Mathlib.AlgebraicGeometry.Gluing` (morphism gluing/uniqueness).
  The node lem-sfb-sheaf-rees-symmetric-presentation has no recorded Lean module in
  the read snapshot; it is only a proof dependency and is listed in the proof
  docstring. No missing notion from it is needed to type this statement.

Source check: read the statement and proof of Stacks divisors.tex
lemma-blowing-up-projective (02NS), and constructions.tex
lemma-glue-relative-proj (01NQ) and
lemma-surjective-generated-degree-1-map-relative-proj (07ZK). The 02NS proof uses
exactly the symmetric-to-Rees surjection and the closed immersion into P(I).
The generalized compatible Rees presentation in the node transports that construction
through theta. The six-step proof docstring follows all six accepted DAG steps.

Edge cases checked before writing:

- I = 0: all positive Rees degrees vanish and its Proj is empty, hence both the
  ordinary blowup and C.relProj are empty. The unique e and empty closed immersion
  are still covered. No nonempty chart or generator is requested.
- I = O_X: the Rees algebra is R[t], so its Proj is X. No proper-center assumption
  excludes this case; the comparison and immersion formulas remain the same.
- A nilpotent ideal, for example (epsilon) in k[epsilon]/(epsilon^2): the irrelevant
  ideal in the Rees algebra is nilpotent, so the Proj and blowup are empty. This is
  allowed and does not require an injective ideal-generator localization.
- Empty X and zero affine section rings: no point/nontrivial-ring hypothesis occurs.
  The affine-open family and all inverse-image charts are the canonical ones.
- Non-affine intersections and nonseparated X: arbitrary overlaps are pullbacks of
  open embeddings and compatibility is checked on affine refinements. There is no
  assumption of affine intersections or separatedness.
- The n = 0 case is included in hφ; degree zero and base scalar normalization are
  supplied by the existing R-algebra structures and theta, with no extra scalar map.
- Universes are explicitly bound; no independent smaller test-object universe or
  nonempty indexing assumption is introduced.

Searches for an existing statement (all through the prescribed msearch wrapper or rg):

- LeanFinder, query: "A compatible family of graded Rees algebra presentations identifies
  the global blowup with relative Proj and embeds it in the symmetric algebra projective
  bundle". Eight hits: `Proj.fromOfGlobalSections`, `Proj.pullbackAwayιIso`, `Proj.awayι`,
  `Proj`, `projIsoSpecTopComponent`, `projIsoSpec`,
  `ProjIsoSpecTopComponent.toSpec_fromSpec`, `Proj.fromOfGlobalSections_toSpecZero`.
  None states the node's compatible Rees presentation and projective-bundle immersion.
- Loogle, query `reesAlgebra, AlgebraicGeometry.Proj`: zero hits.
- LeanSearch, query: "blowup is relative Proj of a graded algebra with compatible Rees
  presentations and closed immersion into projective bundle of the ideal". Eight hits
  give `reesAlgebra`, `Proj`, `ProjectiveSpectrum`, `ProjectiveSpectrum.mk`, its notation,
  `Proj.toSpecZero`, `Proj.openCoverOfMapIrrelevantEqTop`,
  `Proj.iSup_basicOpen_eq_top'`; no match for the theorem.
- msearch grep `blowup|reesAlgebra|relProjIsoOfIso` in Mathlib/AlgebraicGeometry: zero
  hits from that wrapper. Direct source searches, rather than this zero-hit result,
  located and supplied the upstream relative-Proj and Rees interfaces listed above.
- rg `rees.presentation|reesPresentation|blowup.*immersion|<item id>` over
  `lean/WeilConjectures` and `lean/Sheaf`: no exact theorem. The special canonical
  comparison `blowup_rees_symmetric_presentation` is already present and reused;
  it does not give arbitrary C, theta, phi, uniqueness or the requested immersion.
- grep of the item id in `lean/WeilConjectures`: no hit. rg of the new full declaration
  suffix in `dag/lean_names_upstream.json`, Mathlib, WeilConjectures and Sheaf: no hit.

Validation: scompile.py compiled both the isolated sandbox module and its intended
library module cleanly under the 60-second per-file limit. Auto-implicit and relaxed
auto-implicit binding are disabled. No lines exceed 100 characters. The node copy
changes only `lean`, whose signature is copied verbatim from the theorem declaration.
No disputed statement or source fault was found.

## Second reading by NE

No second worker reading: the dispatcher brief requires direct worker delivery and
forbids starting other agents. The maintainer's independent review reads this delivery.
