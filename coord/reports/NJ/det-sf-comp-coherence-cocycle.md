## Worker report

Item: `det-sf-comp-coherence-cocycle`. Module:
`Sheaf.Paper.CompactificationCoherenceCocycle`. The only postponed theorem is
`AlgebraicGeometry.ProEtale.CondensedRing.compactification_coherence_cocycle`;
its proof is exactly `sorry`. The two auxiliary declarations have real data and
belong to the comparison construction of this node. No new DAG node, dependency
repair, or statement correction is delivered. The node copy changes only `lean`.

Source read: the entire current blueprint file
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-comp-coherence/det-sf-comp-coherence-cocycle.md`,
its proposition `_section.md`, the chapter `_section.md`, and the setting node
`sk-def-sfb-dc-setting/_section.md`. The seven DAG proof steps were read as well.
The statement is the current source's statement, including the qcqs base, with
no field, characteristic, Noetherian, or derived-completeness restriction added.

Hypothesis and clause correspondence:

- Admissible Lambda: `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`,
  `[MonObj Λ] [IsCommMonObj Λ]`, and
  `(ℓ : ℕ) [Fact ℓ.Prime] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)`.
  This uses the dependency's full six-case coefficient convention, including
  its specified all-continuous-maps algebraic-closure case.
- Schemes and the named morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Separated of finite type: `[IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]`. Finite type is local finite type plus quasi-compactness.
- Y qcqs: `[CompactSpace Y] [QuasiSeparatedSpace Y]`.
- Each compactification is `Compactification.BoundaryCompactification f`.
  Its nested `obj.obj` is the existing `Compactification f`; the object
  property retains quasi-compactness of its open immersion. Properness,
  open immersion and the factorization equality come from that structure.
  Neither of the compared compactifications is required to be dense.
- `Rf_!^c = Rp_* j_!` on the indicated localizing category is exactly
  `compactificationLocalizingCandidate Λ c`, an abbreviation for
  `(localizingClosureProEtale Λ X).ι ⋙
  rightDerivedLowerShriekOfCompactification Λ c.obj.obj`.
  The latter is the existing levelwise-derived exact extension by zero
  followed by right-derived pushforward. The target is the ordinary
  unbounded module-object derived category on Y, as specified in proof
  step 1; no conclusion about preservation of Loc on Y is appended.
- For every pair there is an isomorphism: the single existential
  `∃ φ : ∀ c₁ c₂, ... ≅ ...` supplies a family of natural isomorphisms,
  so the same family is used in all coherence equations.
- Refinement isomorphisms: the first conjunct states invertibility of
  `compactificationRefinementComponent Λ h K.obj` for every dense-source
  refinement `h : d.obj ⟶ c` and every object K of Loc. This spells out
  the isomorphisms through which the source defines its comparison.
- The component is the canonical one: its data are `Rp_c.map` of
  `localizingRefinementMap Λ h K`, then the inverse of
  `refinementDerivedLowerStarComp Λ h.hom.hom.hom c.obj.obj.g`, then
  `eqToIso` of the refinement's exact proper triangle. It has direction
  `F_c(K) ⟶ F_d(K)`; no arbitrary morphism is supplied as a hypothesis.
- Obtained through ANY common dense refinement, independently of its
  choice: the second conjunct quantifies over `c₁`, `c₂`, every dense d,
  both boundary-preserving projections `h₁`, `h₂`, and every K in Loc.
  It requires `(φ c₁ c₂).hom.app K ≫ ρ_h₂(K) = ρ_h₁(K)`.
  By the preceding invertibility clause this is precisely
  `φ_{c₂,c₁}(K) = ρ_h₁(K) ≫ (ρ_h₂(K))⁻¹`. Thus all diagrams, including
  different projection maps from the same d, compute the same natural
  transformation. Componentwise equality is equality of natural
  transformations by extensionality; φ itself is a natural isomorphism.
- Identity: `∀ c, φ c c = Iso.refl _`, including nondense c.
- Cocycle: `∀ c₁ c₂ c₃, φ c₁ c₂ ≪≫ φ c₂ c₃ = φ c₁ c₃`.
  Lean composes left to right, so this is the source's
  `φ_{c₃,c₂} ∘ φ_{c₂,c₁} = φ_{c₃,c₁}`.

Dependency declarations read and used:

- `WeilConjectures.Compactification.Defs`:
  `AlgebraicGeometry.Compactification`, with its actual open/proper fields.
  Its upstream structure alone does not require a quasi-compact open;
  `BoundaryCompactification` supplies precisely that object restriction.
- `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`:
  `AlgebraicGeometry.IsSchemeTheoreticallyDominant`, the trivial-kernel
  predicate, used by the dense full subcategory.
- `Sheaf.Compactification.BoundaryRefinement`:
  `QuasiCompactObjects`, `boundaryRefinementProperty`,
  `BoundaryCompactification`, and `DenseBoundaryCompactification`.
  Refinement morphisms include both triangles AND the inverse-image-open
  equality, and the dense objects form the recorded full subcategory.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`, publicly
  importing the exact `localizingClosureProEtale` construction from
  `Sheaf.Paper.LocalizingClosure`. No closure or coefficient is redefined.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`:
  `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification`.
- `Sheaf.Paper.CompactificationRefinementLocalizing`:
  `localizingRefinementMap`, `refinementTheta`,
  `refinementDerivedLowerStarComp`, and `localizingRefinement_coherence`.
  The definitions themselves are available without field/density
  assumptions; the theorem's narrower hypotheses are discussed below.
- `Sheaf.Paper.ProEtaleProperOpenInterchange`:
  `compositionInterchangeRestriction`,
  `compositionInterchangeIsNormalized`, and `properOpenInterchange`.
  This is imported for the node's proof, not used to choose comparison data.
- Other stated proof dependencies are imported as proof imports:
  `Sheaf.Compactification.CommonDenseRefinement.exists_common_dense_refinement`
  (declaration namespace `AlgebraicGeometry.Compactification`);
  `AlgebraicGeometry.denseCompactification_refinement_morphisms` in
  `Sheaf.Compactification.DenseRefinementMorphisms`;
  `AlgebraicGeometry.ProEtale.cartesianCoefficients` in
  `Sheaf.Paper.CartesianCoefficients`;
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` in
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`;
  `CategoryTheory.ringedToposDerivedPushforwardComposition` in
  `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`;
  `CategoryTheory.Adjunction.preservesKInjectiveComplexes` in
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`;
  `AlgebraicGeometry.ProEtale.lowerStar` in
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`.
  The module-object `lowerStar`/`lowerStarComp` and the exact
  `openImmersionLowerShriek` are publicly exported by the statement
  dependency imports; their full constructions were also read in the
  read-only side framework, as required by `coord/pefw-upstream-framework.md`.

Edge cases checked by reading the actual quantifiers and constructions:

1. Nondense c₁ and c₂ remain quantified. Only d is dense. There is no
   invalid use of c itself as its own dense refinement in the identity law.
2. An empty source is allowed, as is the zero object of the localizing
   category; no nonemptiness or nonzero hypothesis is introduced.
3. Empty target is allowed. Quasi-compact and quasi-separated do not
   require a point. No test-object nonemptiness is used in the definitions.
4. Identity and repeated projections are included. For c₁=c₂ and
   h₁=h₂, the normalization reads φρ=ρ and cancellation gives identity.
5. Independent dense choices and distinct projections are all universally
   quantified. Invertibility is explicitly included, so the normalization
   cannot be satisfied vacuously by zero comparison arrows.
6. K is any object of the FULL ambient localizing closure, with arbitrary
   unbounded cohomology; it is not restricted to Dctf or Dbc, an etale
   origin, a common coefficient stage, or a completed category.
7. Every universe and variable is explicit (`set_option autoImplicit false`).
   Scheme universe u and sheaf coefficient universe u+1 follow the
   recorded framework; no extra universe equality is assumed.

Searches (all performed before writing):

- `msearch.py ... leanfinder`: "Compactly supported derived direct image
  is independent of compactification with comparison isomorphisms
  satisfying a cocycle condition". Eight hits, headed by
  `CompactlySupportedContinuousMap.compLinearMap`, `...comp`, and
  `CompHausLike.LocallyConstant.presheaf_ext`; none is the statement.
- `msearch.py ... loogle`: `CategoryTheory.Iso.trans, CategoryTheory.Iso.symm`.
  Twelve hits, including `Iso.self_symm_id`, `Iso.symm_self_id`,
  `Iso.trans_symm` and whiskering lemmas. These are categorical tools,
  not the canonical pro-etale compactification comparison.
- `msearch.py ... leansearch`: "Derived compact support functors from
  different scheme compactifications have canonical coherent natural
  isomorphisms". Eight hits, including `SheafOfModules.pushforwardNatIso`,
  `Scheme.Modules.restrictFunctorCongr` and `localCohomology.isoOfFinal`;
  none gives this result or its coefficient category.
- `msearch.py ... grep`: `compactification|shriekIso`, Mathlib
  `CategoryTheory`: zero hits. Direct rg of that Mathlib directory also
  returned no match.
- Direct rg of the upstream `WeilConjectures/` and side `lean/Sheaf/`
  for `coherenceCocycle|coherence_cocycle|compactification.*[Cc]ocycle|compactification.*[Ii]ndepend|det-sf-comp-coherence-cocycle`:
  references and comparisons for etale-origin/finite scalar strict
  towers appeared, but none states this ordinary module-object theorem
  on the full localizing closure with all six coefficients. In particular
  `Sheaf.Paper.RefinementExchangeCoherence` was opened: its theorem is
  on strict towers with levelwise finite scalar etale origins, hence is
  not this node. Upstream etale compactification comparisons likewise
  have another coefficient category/domain.
- Direct rg of all three new declaration names in Mathlib, upstream,
  side modules, and `dag/lean_names_upstream.json`: no existing names.
- `scompile.py --source Sheaf.Paper.CompactificationRefinementLocalizing`
  confirmed that the live interface agrees with the source read locally.

Node proof fault for independent review: the item's prose and current
blueprint source impose only the qcqs-base/finite-type geometric
setting stated above, whereas the present DAG statements of
`det-sf-comp-coherence-refinement` and `det-sf-comp-composition-interchange`
(and their compiled theorems) explicitly impose the later standing
positive-characteristic finite-type-over-a-field setting. The interchange
node additionally specifies finite-subextension condensed Qbar, unlike the
all-continuous-map Qbar case in `sk-def-localizing-closure`. Thus the
item's stored proof cannot literally apply those theorem signatures to
all its cases. This delivery does not assert that the stronger general
statement is false, and does not silently add those hypotheses or change
the coefficient. The proof docstring faithfully records the seven-step
intended argument; stage 3 must justify its invertibility step in the
source's full generality. The canonical comparison DATA used here are
well typed in that full generality. This is a reported proof-plan scope
fault, not a hidden strengthening of the hypotheses or a replacement of
a dependency definition. No counterexample to the item is claimed.

Validation: `scompile.py NJ det-sf-comp-coherence-cocycle <module>` passed
both the sandbox copy (6.4 seconds) and the actual module-path copy
(5.2 seconds), with no errors or warnings. The first attempt diagnosed a
missing `CategoryTheory.Obj` scope for coefficient ring-object instances;
this was fixed and `CategoryTheory.Mod` was made fully qualified. No
source dependency was edited, and no global build was run.

## Second reading by NJ

Author's second pass, with the JSON and final file open; this is not an
independent-agent review. The dispatcher explicitly prohibits starting
other agents and assigns independent review to the maintainer.

I checked the hypothesis list against every phrase of the current source:
admissible commutative condensed Lambda, f separated/finite type and Y
qcqs are present exactly. The candidate uses the existing unbounded
module-object composite and full source localizing category. I checked
the type of ρ: it goes from F_c to F_d, so the equation φρ₂=ρ₁ has the
correct direction and, using its IsIso clause, computes ρ₂⁻¹∘ρ₁. The
same existential family is quantified before all clauses. Both common
refinement maps are arbitrary boundary-preserving refinements; the common
source, and only that source, is scheme-theoretically dense. Identity
and composition are functor-category isomorphism equalities. No clause
uses a mere existence of unrelated objectwise isomorphisms. No local
notation, local instance, private definition, let-binder, or hidden
statement cast was introduced. No new theorem beyond this node is
postponed. I also rechecked the proof-scope fault described above and
kept the source's stated generality rather than adding a field
hypothesis that its statement does not contain. Compilation fixes only
opened the documented instance scope and qualified the existing module
object category; they did not change the mathematical statement.
