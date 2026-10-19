## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageFormula` states
`AlgebraicGeometry.Scheme.AffineProEt.closed_inverseImage_sheafification`, with `sorry`.
No definitions or dependency repairs are introduced and the natural-language statement is unchanged.

Hypotheses and clauses:

- An affine closed immersion is expressed in the coordinates specified by the node's
  first proof step: `A : Type u`, `[CommRing A]`, `I : Ideal A`, with
  `i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`. Every closed immersion
  of affine schemes has this presentation up to the canonical affine identifications.
- The finite coefficient ring is `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ]`.
  `[TopologicalSpace Λ] [DiscreteTopology Λ]` gives exactly its discrete topology.
  There is no commutativity or nontriviality assumption on Λ.
- The input `F : ProEtale.FiniteCoefficientModules (Spec (.of A)) Λ` is literally
  a module sheaf over the coefficient sheaf defined by the dependency, with no
  boundedness, constructibility, or finite-generation condition.
- The inverse of `ProEtale.finiteCoefficientRealization (Spec (.of A)) Λ`, taken
  via its `asEquivalence.inverse`, expresses that same F as a sheaf valued in
  `ModuleCat.{u + 1} Λ`. The published `finiteCoefficientRealization_isEquivalence_ring`
  and `finiteCoefficientRealizationIsEquivalenceRing` apply to every finite Ring,
  including noncommutative rings. This is the canonical scalar realization
  equivalence, not an unspecified equivalent category or a chosen unrelated functor.
- In this presentation i-star is `ProEtale.upperStar (ModuleCat.{u + 1} Λ) i`.
  Its definition is left Kan extension and module sheafification, as reexported by
  the operations dependency. For the canonically identified coefficient rings this
  is the specified module inverse image: its Λ-action is induced by constant
  sections. The node's coefficient-transport argument identifies the tensor formula
  with precisely this fixed-scalar inverse image, also for noncommutative rings.
- `toProEt Z |>.sheafPushforwardContinuous ...` restricts that inverse image to
  the recorded affine basis `B_Z` with its recorded `topology Z`.
- The right-hand presheaf is `(closedSiteLift A I ⋙ toProEt X).op ⋙ F_fixed.obj`.
  At V this is exactly F(v(V)), and at an arrow a it is F(v(a)); the fixed scalar
  presentation retains the original sections with their constant Λ-action.
- `presheafToSheaf (topology Z) (ModuleCat.{u + 1} Λ)` is explicit sheafification
  on B_Z. The comparison is an isomorphism in the category of Λ-module sheaves,
  expressed by `Nonempty (... ≅ ...)`. It therefore retains the module action,
  and does not assert that the presheaf already satisfies descent.

Dependency declarations read and used:

- `Sheaf.Paper.RefinementCoefficientRealization` reexports
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientRingSheaf`,
  `FiniteCoefficientModules`, `finiteCoefficientRealization`, and the published
  general-ring realization equivalence and instance named above. The commutative
  refinement theorem is not used to restrict the input coefficient ring.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations` reexports the
  fixed-scalar `AlgebraicGeometry.ProEtale.upperStar` from
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`;
  it is defined for any Grothendieck abelian value category, including left
  ModuleCat for noncommutative rings. We do not impose the CommRing assumptions
  of the additional intrinsic-commutative specialization.
- `Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift`:
  `AlgebraicGeometry.Scheme.AffineProEt.closedSiteLift` and its actual algebraic construction.
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`:
  `Scheme.AffineProEt`, `AffineProEt.toProEt`, `AffineProEt.topology`, and its
  actual restriction equivalence. This is the recorded basis, not a private site.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`. All source signatures and docstrings were read.
- Stated proof dependencies are imported: `ClosedSiteAdjunction` (the adjunction
  with invertible unit), `ProEtaleInverseImage` (the Kan-extension inverse image),
  `ProEtaleConstantRingMap` (the canonical finite-ring coefficient comparison),
  and Mathlib `Adjunction.Mates` (conjugate comparison). Basis and finite-limit
  preservation of sheafification come from the already imported modules.

The six-step proof docstring follows the node: basis restriction and v ⊣ u;
forward/backward Hom formulas; the two triangle-identity calculations;
sheafification and uniqueness of adjoints; product compatibility of operations;
and the coefficient change-of-scalars identification for left modules.

Edge cases checked before drafting: I = bottom gives the identity closed immersion;
I = top gives the empty closed scheme; the zero base ring is allowed; the zero
coefficient ring and zero module sheaf are allowed; no weak contractibility of V
is assumed; no surjectivity on all section maps or presheaf sheaf condition is
asserted. The empty cover is retained by the actual basis topology. The site object
universe remains u+1 with Hom universe u, and module values have size u+1.

Searches made:

- `msearch.py`, LeanFinder: inverse image of a pro-etale module sheaf along a closed
  immersion as sheafification of precomposition with the closed site lift; no exact
  match (related scheme restriction and generic sheaf tools).
- `msearch.py`, Loogle: `CategoryTheory.presheafToSheaf,
  AlgebraicGeometry.ProEtale.upperStar`; no match, with upperStar unknown to the
  Mathlib-only index.
- `msearch.py`, grep of Mathlib `CategoryTheory/Sites` for
  `closed.*[Ii]nverse|sheafPullbackIso`: only generic sheaf-pullback isomorphisms
  and an unrelated sieves calculation.
- `msearch.py`, LeanSearch: inverse image along a closed immersion as sheafification
  of precomposition with a left adjoint on basis sites; generic sheafification
  adjoint and open-immersion results, no closed pro-etale formula.
- Repeated LeanFinder for the module version: open scheme restriction and closed
  immersion ideal-sheaf results, no exact formula.
- `rg` in upstream WeilConjectures and project lean/Sheaf for closed inverse-image
  names, closedSiteLift, and related patterns; `grep -rn` for the exact node id
  in upstream has no hit. The project's `affine_closed_inverseImage_evaluation`
  only treats sheaves of sets and has an additional weak-contractibility clause;
  it does not give this finite-ring module statement, so no duplicate is created.

Source checks: read the entire node and dependencies, including their recorded
modules. The local literature folders are absent, so opened Stacks Tags
https://stacks.math.columbia.edu/tag/09BK and
https://stacks.math.columbia.edu/tag/09BL directly. Tag 09BL (1) gives precisely
sheafification; its affine hypothesis and Tag 09BK agree with the coordinate model.
The module-specific extension is the explicit six-step proof recorded in the node.
There is no node fault or STATEMENT-DISPUTED flag.

Validation: single-file compilation through scompile.py and deliver2.py --no-push;
results are recorded after the clean dry run. An independent second reader is still
responsible for the second-reading section and delivery.


## Second reading by Q31

Independently read the sandbox node, all five statement-dependency nodes and their
recorded source declarations, all ten proof-dependency records, the complete Lean
module, Stacks proetale.tex section `section-closed-immersion` through the proof of
`lemma-closed-immersion-affines-apply`, and Tags 09BK and 09BL. The section has no
standing Noetherian, characteristic, separatedness, or nonempty hypotheses. Tag
09BL(1) is the sheafification assertion; its weakly contractible evaluation assertion
is a separate clause and is not a hypothesis here. Local literature is absent;
read the public Stacks .tex and tag pages. Source links:
https://stacks.math.columbia.edu/tag/09BK and
https://stacks.math.columbia.edu/tag/09BL.

Object/hypothesis/conclusion inventory and matching:

1. Affine schemes X and Z, and a closed immersion i: the binders
   `(A : Type u) [CommRing A] (I : Ideal A)` and the displayed
   `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))` give X = Spec A,
   Z = Spec(A/I), and their quotient closed immersion. Verdict: exact coordinate
   convention of the node's first proof step and of Tag 09BK. No arbitrary affine
   morphism or open immersion is substituted. Every affine closed immersion admits
   this presentation through the affine-spectrum identifications; the basis lift
   dependency itself uses precisely these coordinates, so no special case is lost.
2. A finite discrete coefficient ring, with left modules:
   `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ] [TopologicalSpace Λ]
   [DiscreteTopology Λ]`. Verdict: exact, including noncommutative and zero rings.
   Choosing the unique discrete topology is not an additional mathematical
   hypothesis, and there is no CommRing, Nontrivial, or invertible-order assumption.
3. An arbitrary pro-etale coefficient module sheaf F:
   `(F : ProEtale.FiniteCoefficientModules (Spec (.of A)) Λ)`.
   Verdict: the actual category of left modules over finiteCoefficientRingSheaf
   from def-weil-pbc-proetale-modules. Opened finiteCoefficientPresheaf,
   finiteCoefficientRingSheaf, FiniteCoefficientModules, finiteCoefficientScalarMap,
   finiteCoefficientModulePresheaf, finiteCoefficientRealization and its general-ring
   equivalence theorem and instance. They use the prescribed connected-component
   quotient topology and canonical constant scalar sections. No constructibility,
   finite generation, boundedness or extra structure is required of F.
4. The input's fixed-scalar presentation:
   `(ProEtale.finiteCoefficientRealization (Spec (.of A)) Λ).asEquivalence.inverse.obj F`.
   Verdict: valid presentation of the same module sheaf, up to the realization
   unit/counit isomorphisms. This inverse is determined up to compatible isomorphism
   by the explicit realization equivalence, not an arbitrary equivalence. Sections
   are canonically identified with the original sections restricted to constant
   Λ-scalars; they need not be definitionally equal in Lean. The general Ring
   equivalence is available from the reexported finite-module module, so the
   commutative theorem in RefinementCoefficientRealization adds no restriction.
5. The module inverse image i-star:
   `(ProEtale.upperStar (ModuleCat.{u + 1} Λ) i).obj F_fixed`.
   Verdict: the precise fixed-scalar inverse image, implemented by left Kan
   extension and sheafification along the same base-change functor as
   proEtaleSheafInverseImage. Read its definition and adjunction in the shared
   FiniteCoefficient/UpperLowerStar/Defs framework. Its Grothendieck abelian
   assumptions are instances for ModuleCat of any Ring, not new hypotheses on Λ.
   The operations dependency reexports this interface. For commutative Λ it
   presents the recorded ringed tensor pullback; the node's sixth proof step
   explicitly extends this to general left modules. The canonical coefficient
   inverse-image isomorphism preserves constant sections, so this presentation
   retains the specified action rather than choosing a different coefficient map.
6. Restriction to the affine ind-etale basis B_Z:
   `(toProEt Z).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
     (topology Z) (ProEt.topology Z)` on the left side.
   Verdict: the recorded full affine basis, with its induced precoverage and
   topology. Opened AffineProEt, toProEt, precoverage, topology and the recorded
   restriction-equivalence signature. The full inclusion and restriction are
   the ones of def-weil-pbc-ind-etale-basis and lem-weil-pbc-ind-etale-basis.
7. The prescribed presheaf P_F, including all restriction maps:
   `(closedSiteLift A I ⋙ toProEt X).op ⋙ F_fixed.obj`.
   Verdict: at V it is F_fixed(v(V)), and at a: V' → V the map is F_fixed(v(a)).
   Opened the complete ClosedSiteLift source: its objects are the spectrum of the
   genuine Algebra.ClosedLift of the coordinate algebra, and its arrows are the
   opposite induced algebra maps. No private replacement lift or arbitrary map.
8. Sheafification on B_Z of this module presheaf:
   `(presheafToSheaf (topology Z) (ModuleCat.{u + 1} Λ)).obj P_F`.
   Verdict: the recorded Mathlib sheafification, with its universal-property
   adjunction. Opened presheafToSheaf, toSheafify and sheafificationAdjunction.
   ModuleCat-valued sheafification carries the original fixed scalar action.
9. Identification of the restricted inverse image with that sheafification:
   `Nonempty (leftSide ≅ rightSide)` in the category of ModuleCat-valued sheaves
   on B_Z. Verdict: exactly the asserted object identification, including linearity.
   The node does not separately demand a specified natural transformation as
   theorem data. No assertion that P_F is already a sheaf is added, and no
   sectionwise surjectivity or weak contractibility is imposed.

Edge cases: I = bottom includes the identity after the standard quotient
identification; I = top includes the empty closed scheme. A may be the zero ring,
so X itself may be empty. Λ may be the zero ring and F may be the zero sheaf;
ModuleCat and sheafification still apply. There is no index set or degree n in this
statement. Empty coverings are retained by the imported topology, including the
empty scheme. No characteristic is fixed. Universes are fully bound: A and schemes
are at u, the site object types are at u+1 with Hom types at u, and module values
are at u+1. No equality between site object and Hom universes is imposed; these
are the dependency size conventions, and there is no independent smaller universe
for quantified test objects. Finite coefficient types can be lifted to this value
universe. There are no extra explicit typeclass hypotheses beyond the listed
ring and discrete-topology data.

Independent duplicate searches (different queries from the first reader):

- msearch.py LeanFinder: `closed embedding proetale pullback on affine sites
  precomposition with adjoint and associated module sheaf` returned generic scheme
  module pullback adjunctions, affine-space pullbacks and etale pullbacks. None is
  a closed pro-etale affine-basis module formula.
- msearch.py Loogle: `CategoryTheory.presheafToSheaf, CategoryTheory.Adjunction`
  returned sheafificationAdjunction only. It supplies the universal property,
  not this comparison.
- msearch.py grep: `closed immersion sheafification inverse image modules`
  returned no matches. Independently ran rg on Mathlib Sites/Pullback and on both
  the upstream WeilConjectures tree and project lean/Sheaf for
  closed_inverseImage, closed/sheafification, closed/inverseImage,
  affine_closed_inverseImage and closedSiteLift. Inspected the nearby
  affine_closed_inverseImage_evaluation signature: it is a sets-valued natural
  comparison with an additional contractible-evaluation clause, not this module
  statement. Generic sheafPullbackIso tools are likewise not this theorem.

No new nodes, dependency modules or statement correction occur in this delivery.
The dependencies used by the theorem are usable as recorded; the generic reexports
above are intentional and impose no commutativity assumption. All stated proof
prerequisites are imported, using their Mathlib matches for sheafification exactness
and conjugate units. The six-step proof docstring follows the node's basis
adjunction, both Hom maps and naturality, both triangle calculations,
sheafification/adjoint uniqueness, finite-product operation transport including
nullary operations, and coefficient identification with the left-module
extension-of-scalars formula. Module and declaration docstrings include the source
and blueprint marker. The only declaration is the theorem and its proof is `sorry`;
there are no new data definitions, local notation, private declarations or local
instances. All lines satisfy the 100-character bound, and the node's lean.statement
was mechanically compared verbatim with the complete signature before `:= by`.

Mismatch verdict: no mathematical or Lean-signature mismatch found. Kept the
module and node unchanged. Added this independent reading, with the unit/counit
precision about the fixed-scalar presentation that the worker report abbreviated.

Second-reader validation: scompile.py compiled the delivered module cleanly in
sandbox and library modes (37.6 s and 7.4 s), with no errors or warnings.
