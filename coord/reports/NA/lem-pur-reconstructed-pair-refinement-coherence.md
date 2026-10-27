## Worker report

Item: lem-pur-reconstructed-pair-refinement-coherence. Module:
`Sheaf.Paper.ReconstructedPairRefinementCoherence`; namespace
`WeilConjectures.ReconstructedPairRefinement`. The primary statement is
`reconstructedPairRefinementCoherence : Coherence l E k C X Y f`.
All three postponed theorems have `sorry` proofs. All helper data are actual
composites of the published constructions, or records of the hypotheses and
conclusions of this same node. No independent notion is introduced.
The node's statement and accepted split are unchanged.

### Hypotheses and clauses

* Distinct prime characteristic p and l: `l : ℕ`, `[Fact l.Prime]`,
  `k : Type u`, `[Field k]`, `[Fact (ringChar k).Prime]`,
  `[Fact (ringChar k ≠ l)]`. Writing p as ringChar k retains exactly all fields
  of the stated positive prime characteristic, as in the realization dependency.
* Separated finite-type k-schemes: `X Y : CondensedERealization.Base k`.
  Its fields are scheme, structural morphism to Spec k, locally finite type,
  quasi-compact and separated. `f : X.scheme ⟶ Y.scheme` and
  `[f.IsOver (Spec (.of k))]` express exactly the k-morphism hypothesis.
* Finite coefficient extension: `E : Type u`, `[NormedField E]`,
  `[NormedAlgebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` use the published
  finite-extension interface. The valuation ring, its chosen uniformizer and
  positive coefficient quotients are `integralExceptionalIntegers`,
  `integralExceptionalUniformizer` and the dependency's actual quotient rings.
  The norm is the extending norm of a finite p-adic extension, not an additional
  restriction of fields. Dependency index n denotes the exponent n+1.
* `c d : Compactification f`, `w : c.Refinement d` retain the proper ambient map,
  identity restriction to X and commuting proper structure maps. No cartesian,
  dense-open or smoothness hypothesis is imposed.
* Completion and integral category: `CondensedERealization.Integral l E T` is the
  published full complete uniform constructible category, with compatible origins.
  No replacement category or mere finite-level condition is used.
* `C : ComparisonFamily l k` is the simultaneous compact-support reconstruction
  and coefficient realization comparison supplied by the recorded dependency.
  `support` abbreviates its own `integralSupport`. Its reduction data are
  `(C.coefficient E).reduction`. `PurIntegralRepresentingPair.reduction`,
  `totalLimit` and `adjunction` are reused, including their actual unit/counit.
* `At c` packages the supplied strict etale support, Brown adjunction, finite
  evaluations, normalized bounded site transport and published representing family
  for that compactification. `At.Supplied` is exactly the recorded supplied-system
  structure, including normalization, common bounds, finite constructibility,
  finite exceptional identifications, quotient transitions, both recognition modes,
  integral total limit and actual reduction-isomorphism hypotheses.
* `At.output` is the actual Brown system N. `At.pair` retains the theta selected
  by the published family, with its finite evaluation and good-truncation
  normalization. `At.counit` is the actual transported Brown counit, evaluated at
  the supplied origin, normalization, finite Tor and output-bound proofs.
  `At.trace` is literally the published Hom bijection at identity.
* `systemDown` is the dependency's actual `systemRefinement` conjugated through
  the exact quotient coordinates using their counit and the uniquely normalized
  `PurIntegralSupportComparison.beta`. That beta is fixed on ordinary sections,
  open-adjunction transposes, complex representatives and the proper-derived unit.
  Thus no arbitrary isomorphism with the same endpoints enters the construction.
* `systemDown_isIso` states invertibility on the intrinsic bounded-below origin
  domain. Its proof plan uses finite normalized proper/open comparison and
  conservative evaluation only for invertibility. `systemComparison` is its
  inverse, giving exactly the node's forward q^S direction.
* `output_origin` states that the other supplied Brown output belongs to the same
  intrinsic origin domain. This is part of the node's bounded transported-Brown
  setting, expressed across the two normalized site coordinate packages.
* `comparison` is the inverse of the published integral refinement arrow, whose
  invertibility is supplied by `C.refinement`. `Coherence.reduction` is the
  alpha comparison square, written after postcomposition with the actual inverse
  direction systemRefinement. Since that component is invertible on these inputs,
  this is precisely alpha2 R(q_R) = q^S alpha1.
* The ordinary-system identity, composition, common-refinement independence and
  cocycle are `system_id`, `system_comp`, `system_common_independent`,
  `system_cocycle`. The corresponding integral assertions are `integral_id`,
  `integral_comp`, `common_independent`, `cocycle`. `commonComparison` quantifies
  over every dominating compactification and its arrows, without a selected one.
* `mate` is the inverse of the actual bounded Brown Hom bijection applied to
  q^S followed by the second Brown counit. `mate_counit` states its defining
  counit equation; `mate_iso` and `mate_comp` retain invertibility and successive
  refinement coherence. No global constructible integral right adjoint is assumed.
* `Coherence.pairs` quantifies over `L`, both supplied systems and an actual system
  isomorphism `s : A₂.system ≅ A₁.system`, with the exact theta-square hypothesis.
  `reconstructedMap` is the actual total-limit functor applied to s.hom and lifted
  through the full integral subcategory. `Equations.counit` is precisely
  P1(sbar) followed by t1 = q_R followed by t2.
* `Equations.hom` is the square of published integral linear Hom bijections for
  every integral K and every h : K → M2. These are the original published linear
  equivalences, not newly postulated representations.
* `single_degree` states that the compatible evaluation equations imply the actual
  theta square when the supplied systems are in the same single degree.
  The supplied recognition alternative and dependency's normalized theta retain
  the functorial good-truncation interpretation. No inference from evaluations
  is made for arbitrary derived morphisms.
* `common_pair_counit` expresses the same trace equation for the comparison
  through any common dominating compactification and supplied dominating pair.
  Together with `common_independent`, `mate_comp` and `integral_comp`, it retains
  successive/common refinement compatibility of the equations.
* `scalarTrace` is actual completed integral scalar extension followed by the
  inverse of the specified compact-support tensor comparison.
  `Equations.scalar` gives the extended counit equation for every finite H/E,
  including ramified ones. `scalar_identity` and `scalar_transitive` insert exactly
  the recorded tensor unit and associator comparisons. Hom squares follow by
  precomposition with arbitrary test maps, as for `Equations.hom`.
* `realize` is rationalization followed by the actual E realization equivalence.
  `fieldSupport`, `fieldComparison` and `fieldTrace` restrict the original
  condensed proper/open support, intrinsic refinement and specified realization
  comparison to the original full bounded categories. `Equations.field` is the
  realized equation; `field_hom` includes every condensed E test object.
* `toOmega`, `omegaSupport` and `omegaComparison` use the archived finite-valued
  `Profinite.padicAlgClRingObj`, not the full continuous-function coefficient ring.
  `omegaTrace` is the actual projection comparison inverse followed by scalar
  extension of the E trace. `Equations.omega` and `omega_hom` give the closure
  counit equation and its Hom form for every closure test object. The proof plan
  records common finite-field descent and eventual equality of finite diagrams.
* `Equations.transpose` quantifies over specified right adjoints J1 and J2 of
  the original closure support functors. The c_i are their actual Hom transposes
  of the realized counits; rho is exactly `conjugateEquiv adj₂ adj₁ q.hom`.
  The equation is sOmega followed by c1 = c2 followed by rho, with Lean's
  left-to-right composition convention.
* Every map is constructed before evaluation or total limit. The docstrings and
  proof plan explicitly prohibit using finite evaluations to prove equality of
  arbitrary derived-system morphisms.

### Dependencies read and used

Read each statement-dependency statement and record, then its signature/docstring.
The scheme-conventions node is a convention record. The compactification interface
is `WeilConjectures.Compactification.RefinementCategory`,
`AlgebraicGeometry.Compactification.Refinement`, including its automatic properness.
Coefficient rings/finiteness are in
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
`Padic.finite_coefficientExtensionRing`. The complete category specialization is
`Sheaf.Paper.IntegralUniformCoefficient`,
`AlgebraicGeometry.Scheme.pbcBoundedConstructibleComplete`; the actual category
used here is its published equivalent integral coefficient-model presentation.

The actual reduction/limit calculus is
`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`,
`WeilConjectures.CoefficientDerivedSystemCalculus` and
`coefficientDerivedSystemEvaluationCalculus`. Support, alpha, refinement,
coefficient and realization constructions come from
`Sheaf.Paper.CompactSupportCondensedRealization`,
`WeilConjectures.CompactSupportCondensedRealization.ComparisonFamily` and
`compactSupport_condensedRealization`. Supplied data and normalized traces are
`Sheaf.Paper.PurIntegralRepresentingPair`,
`WeilConjectures.PurIntegralRepresentingPair.Supplied`, `PublishedFamily` and
`reconstructedRepresentingPair`. The coordinate comparison is the dependency's
`Sheaf.Paper.PurIntegralSupportComparison`, `coordinates` and `beta`.

The actual ringed-system clopen mate is specified by
`Sheaf.Paper.RingedRefinementCoefficientSquare`,
`SheafOfModules.ringedRefinementCoefficientSquare` and its Package. The diagram
site realization is `Sheaf.CategoryTheory.DiagramSiteRealization`,
`CategoryTheory.exists_diagramSite_realization`. Formal coherence is
`Sheaf.AlgebraicGeometry.CompactificationRefinementCoherence`,
`AlgebraicGeometry.ProperOpenCalculus.compactification_refinement_coherence`.
The unique-adjoint dependency is Mathlib
`CategoryTheory.Adjunction.rightAdjointUniq`, whose counit normalization was read
alongside `conjugateEquiv` in `Mathlib.CategoryTheory.Adjunction.Mates`.
Closure descent is
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`,
`AlgebraicGeometry.ProEtale.constructibleCocone_isFilteredTwoColimit`.

Proof-only imports include VaryingRingProperOpenPasting and
Compactification.CategoryBaseChange. The other recorded stated proof dependencies
are already in the public import closure: SemilinearDerivedSections,
StrictTowerProperOpenCalculus, PurNormalizedReconstructionAdjunctionCalculus,
BrownTowerFiniteSiteComparison, and Mathlib's adjunction mate-pasting lemmas.
`lem-pur-reconstructed-pair-finite-scalar-extension` has no recorded declaration;
no invented import or opaque map was substituted. Here scalarTrace explicitly
constructs the scalar-extended counit from the existing actual integral scalar
functor and compact-support comparison, and the scalar equations are stated as
conclusions for that construction. This suffices to state this node; the finer
identification with independently supplied extended pairs remains that proof
prerequisite's task. No statement of that separate node is borrowed as a hypothesis.

### Sources and searches

Read current `literature/blueprint/latest/blueprint/sec-smooth-purity/`:
`sk-prop-sp-unique-adjoint/sk-prop-sp-unique-adjoint-categorical.proof.md`,
`sk-thm-purity-transport/_section.md` and its proof, and the integral-adjunction
bijection statement. The categorical source defines the comparison by its counit
transpose, so choosing an arbitrary comparison would not state this node.

Actual searches made:

* msearch leanfinder: "Reconstructed exceptional representing pairs commute with
  compactification refinement and counit preserving right adjoint mates" returned
  8 hits, including Mathlib mateEquiv_counit, mateEquiv, mateEquiv_apply and unit
  formulas. These supply formal mate calculus, not this geometric reconstruction.
* msearch loogle: "CategoryTheory.conjugateEquiv, CategoryTheory.Adjunction.homEquiv"
  returned 0 hits for the combined query. Direct source reading found and reused
  `conjugateEquiv`; it does not itself state this node.
* msearch grep: "reconstructed.*[Rr]efinement|[Rr]efinement.*[Rr]epresenting"
  returned 0 hits.
* rg on project Sheaf and WeilConjectures for reconstructed/refinement/coherence
  and the exact item id found the existing support/refinement and formal-coherence
  interfaces listed above, no declaration of this representing-pair theorem.
* Exact-id search in WeilConjectures found no match. No duplicate definition was
  written. The old CompactObject example is now withdrawn; the record was read.

### Edge cases and validation

Checked identity refinement and repeated compactification: all comparisons use
actual identities and their inverse, with identity asserted explicitly. Common
refinements and all their arrows are quantified, so no uniqueness of refinement
is silently assumed. Empty schemes and zero objects are allowed by Base, full
integral categories and supplied systems. No Nonempty hypothesis is imposed on X,
Y or support. Single degree is an arbitrary integer, including zero and negative
degrees. Quotient exponents are n+1, so no accidental R/t^0 level is included.
No flatness of quotient maps or concentration after ramified scalar change is
assumed. The coefficient identity and successive extension cases retain their
specified tensor unit and associators. The final J_i remain conditional choices
of specified right adjoints; representability at the supplied L never assumes
an integral global right adjoint. Universes follow the existing coefficient and
scheme interface, with sheaf universes u+1 and actual ordinary derived systems.

The module compiles cleanly through the prescribed scompile.py, both as sandbox
and at its real library module path, within the 60-second limit. `autoImplicit`
is explicitly false; all universe and variable binders are explicit.
No mathematical node fault or STATEMENT-DISPUTED issue was found.

## Second reading by NA

This is the dispatcher's single-worker delivery; no other agent was started.
The independent mathematical review is the maintainer's delivery review, as the
assignment specifies. I performed a separate second pass with the node and Lean
open, checked every correspondence above, and corrected namespace/scope and
coefficient API argument order errors exposed by compilation. This paragraph does
not claim an independent worker reviewed the file.

The key direction check was repeated: the published system and integral arrows
run d to c for w:c→d; systemComparison and comparison invert them, and mate runs
N2 to N1. The Lean counit equation therefore reads P1(sbar) ≫ t1 = q ≫ t2.
I expanded the two closures of the final transpose: under adj1 both become that
same realized counit equation. The commonComparison order is q_r inverse then q_s,
which indeed goes from c to d. The scalarTrace order is comparison inverse then
scalar(t), exactly the required P_H(M_H) to L_H direction. A second pass added
explicit system common-refinement/cocycle clauses, the common-pair trace equation,
all condensed test-object Hom equations, and the scalar unit law rather than
leaving these only in prose. No hypotheses or source statement were changed.
