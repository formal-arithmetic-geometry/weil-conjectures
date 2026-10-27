## Worker report

Stage 2 statement delivery for lem-trf-projective-bidual-representative-comparison.
The Q39 delivery merged on 2026-10-23 is a stage-1 split, not a Lean statement:
the current node has no lean record. The stage-handoff paragraph of brief-stage2
explicitly permits this stage-2 delivery. The accepted statement, proof, proof_deps,
source and review records are unchanged. This repair addresses the independent review of returned head 180e0cd6b553.
A new definition node owns the three existing ordinary-Hom maps; there is no
Lean-code change, dependency module, statement correction or statement dispute.

The module is Sheaf.TraceFormula.ProjectiveBidualRepresentativeComparison. Its sole
postponed theorem is
CategoryTheory.ProjectiveBidualRepresentative.projective_bidual_representative_comparison.
Every auxiliary definition has actual data; Transport and Statement are explicit
propositions, not assumptions on the input. The only input is a commutative ring B
in an arbitrary universe u. No derived-category, braiding, boundedness or finiteness
instance is an additional input. The library supplies the module derived category;
sheafGrothendieck obtains the coefficient-universe sheaf localization from the recorded
Grothendieck theorem. koszulBraiding is the descended cochain Koszul braiding, not an
arbitrary choice of braiding.

Hypotheses and clauses, read against the node:

1. “B a commutative ring”: `(B : Type u) [CommRing B]`, explicitly bound in the
   namespace variable declaration. `autoImplicit` is false. All derived categories
   in Transport and Statement use localization universe u, the coefficient universe.
2. “one object, only identity, maximal covering sieve; underline B”: the existing
   singletonSite, singletonTopology, singletonRingSheaf B and singletonModuleCategory B.
   No replacement site or new module-sheaf category is defined. The first conjunct
   of Transport states the equivalence with functor singletonEvaluation B, inverse
   singletonConstantModuleSheaf B, and preservation of every short exact complex.
3. “evaluation and inverse one-object sheaf construction”: evaluation and constant
   are just the existing functors applied degreewise. The derived equivalence d and
   natural isomorphism k explicitly satisfy `Q ⋙ d.functor ≅ evaluation B ⋙ Q`.
   This specifies the equivalence induced by evaluation, not an unnormalized
   equivalence of the two categories.
4. “product total Hom H”: `CochainComplex.moduleHomComplex`, the recorded module
   complex with degree-n cochains and differential d_target f - (-1)^n f d_source.
   `sheafHom` abbreviates the recorded general-site homComplex. The isomorphisms χ
   in Transport match every cochain component with coefficientHomComponent, evaluated
   at the sole object and the identity in its slice. Thus the B-linear product
   coordinates and the differentials agree. Their chain-isomorphism types ensure
   compatibility of the differentials; the coordinate formula uniquely specifies χ.
5. “K-injectives and resolution augmentations”: Transport contains preservation and
   reflection of IsKInjective under evaluation and constant, and explicitly says
   the evaluated image of each existing ringedSiteHomAugmentation is a quasi-isomorphism
   with K-injective target. resolution is the actual composite constant, fixed
   coefficientHomResolution, evaluation. augmentation is the evaluated existing
   augmentation at the constant complex; evaluation of a constant complex is
   definitionally the original complex. Statement also records its quasi-isomorphism
   and K-injective target. No fresh replacement or augmentation is chosen.
6. “identifies derived internal Hom”: ρ in Transport compares the actual
   derivedInternalHomOfUniverses at u with the existing ordinary closed Hom, naturally
   in both variables. The latter is exactly the ordinaryModuleDerivedInternalHom
   abbreviation, whose definition is Functor.uncurry.obj MonoidalClosed.internalHom;
   spelling its values with ihom and its maps with MonoidalClosed.pre does not
   introduce a second derived Hom. The displayed square with
   ringedSiteOrdinaryHomComparison, k, Qχ and comparison pins the identification to
   the existing fixed K-injective localization factorization, in both variables.
7. “coefficient evaluation and Koszul-symmetry transpose”: ev is specified on every
   total-tensor summand by `(-1)^(p*q) * z(x)`. This is the module convention for the
   imported Hom complex and left-tensor adjunction. comparison is its actual
   localized transpose `curry (Q.tensorator ≫ Q.map ev)`, not an arbitrary isomorphism.
   Transport supplies a normalized RingedSiteDualityModel M, a natural derived tensor
   comparison τ, the evaluation equation, the Koszul-braiding equation, the explicit
   transpose equation for every f, and the induced equality for ringedSiteBidual.
   Consequently evaluations and their transposes are identified, not just the objects
   which occur as their sources and targets.
8. “O=B[0], V dual, b”: coefficient is the existing singleFunctor in degree zero
   applied to ModuleCat.of B B. Ordinary duality is ihom into Q(coefficient B).
   bidual is the imported MonoidalClosed.toIhomIhom with that coefficient and the
   fixed descended Koszul braiding. The transport equality is stated for every
   coefficient W, so in particular for the constant sheaf B[0].
9. “fixed augmentation induces the canonical comparison”: Statement displays
   `comparison S O ≫ RHom(QS,Qη) = Q(H(id,η)) ≫ comparison S I(O)` and asserts the
   comparison into the K-injective I(O) is invertible. Qη is invertible because the
   preceding augmentation clause says QuasiIso. Equivalently, putting
   `λ = RHom(QS,Qη) ≫ (comparison S I(O))⁻¹`, the comparison is exactly
   `Q(H(id,η)) ≫ λ⁻¹`. The ρ/k/χ square identifies this λ with transport of the fixed
   sheaf localization factorization. This pins the actual maps used in the node.
10. “T and D=H(T,O) both bounded above and projective”: the final T clause of
    Statement has separately the upper-bound existence and the termwise
    Module.Projective binders for T and moduleHomComplex T O. After these four
    hypotheses its first four conclusions give QuasiIso of H(T,η), QuasiIso of
    H(D,η), IsIso of comparison T O and IsIso of comparison D O. The hypotheses
    are retained for both complexes, rather than inferred for D from T.
11. “signed δ and zero coordinates”: δ is a family of actual chain maps
    `T ⟶ moduleHomComplex (moduleHomComplex T O) O`. Its value at every p,q,x,phi
    is `(p*q).negOnePow • phi(x)`. A separate clause says the q-coordinate is the
    zero linear map whenever q+p is nonzero. These equations uniquely determine δ
    using the existing cochain projections; no arbitrary map can satisfy them.
12. “(gamma_T) dual composed with b equals gamma_D composed with Qδ”: the last
    conclusion under the four T/D hypotheses is exactly
    `bidual (Q T) ≫ (pre (comparison T O)).app (Q O) = Q.map (δ T) ≫ comparison D O`.
    Both sides are maps Q T to RHom(Q D,Q O). Diagrammatic Lean composition reverses
    the written functional-composition order, as required.
13. “comparisons natural in chain maps”: the separate S,S',f clause states
    `QH(f,id) ≫ gamma_S = gamma_S' ≫ (pre (Qf)).app (Q O)` in the contravariant
    direction. H itself is specified for simultaneous pre- and postcomposition by
    its component formula. These specify the existing Hom action, not a new notion.
14. “whole-derived-category bidual naturality”: the last clause quantifies over
    every V,W in DerivedCategory.{u} (ModuleCat.{u} B) and every e:V→W, and states
    `e ≫ b_W = b_V ≫ (pre ((pre e).app (Q O))).app (Q O)`.
    It is not restricted to localized chain maps or to projective objects.
15. “no finite generation or invertibility of b”: no Module.Finite, dualizability,
    perfectness or IsIso (bidual ...) occurs. IsIso is asserted only for the two
    ordinary-to-derived Hom comparisons and the K-injective factorization.

All existential H, ev, δ and χ data are uniquely specified by formulas on every
homogeneous coordinate/summand. They are quantified in the proposition; no definition
extracts unknown data from an existence theorem with sorry. The definitions of the
comparison and bidual maps use actual imported adjunction/localization data.

Recorded dependency declarations read and used:

- def-weil-abstract-derived-category: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  DerivedCategory, HasDerivedCategory and DerivedCategory.Q, including the localization
  universe binder. These are the ordinary unbounded derived categories throughout.
- def-sc-module-total-hom-complex:
  WeilConjectures.Algebra.Homology.ModuleHomComplex, CochainComplex.moduleHomComplex;
  its terms are Mathlib HomComplex.Cochain and its differential is δ_hom.
- def-weil-pbc-projective-module: Mathlib.Algebra.Module.Projective, Module.Projective;
  its actual class says the canonical free-module surjection splits.
- def-weil-sheaf-of-modules-category: Sheaf.CategoryTheory.RingedSiteModules,
  CategoryTheory.ringedSiteModules, transparently the Mathlib SheafOfModules category.
- def-pur-derived-internal-hom:
  Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom,
  CategoryTheory.ordinaryModuleDerivedInternalHom and its public general-site
  derivedInternalHomOfUniverses. Both full signatures and their docstrings were read.
- lem-sfb-ringed-site-duality-maps: Sheaf.CategoryTheory.RingedSiteDualityMaps,
  ringedSiteBidual, RingedSiteDualityModel, ringedSiteBidual_normalization and
  ringedSiteBidual_naturality. This module supplies the normalized existing closed
  sheaf model and signed representative normalization; it is not replaced privately.

stmt_deps additionally names already landed owners used explicitly in the signature:
def-trf-singleton-site-operations (the existing SingletonSiteModuleComparison definitions),
def-coef-hom-representative-evaluation (coefficientHomComponent and coefficientHomResolution),
prop-pur-kinjective-resolutions-exist (the recorded Grothendieck theorem),
def-pur-hom-complex (CategoryTheory.homComplex), def-pur-kinjective-complex
(Mathlib CochainComplex.IsKInjective), and def-trf-ringed-site-ordinary-hom-comparison
(ringedSiteHomAugmentation, ringedSiteHomComplexMap and ringedSiteOrdinaryHomComparison).
Their nodes, signatures and source docstrings were read. The comparison maps are
plain definitions, rather than choices from the isomorphism theorem; the new definition
node records their ownership. All imported declarations are retained verbatim. Explicit plain imports retain the proof's K-projectivity, Hom/cone,
transpose and representative-composition interfaces. Other proof dependencies are
already reached through the public imports.

Edge cases checked before finalizing:

- The zero ring is allowed by CommRing; no Nontrivial assumption occurs.
- The zero complex gives the unique zero maps and the same identities.
- A degree-zero projective module gives unsigned ordinary evaluation. In odd degree
  p, the only contributing q=-p gives (-1)^(p*q)=(-1)^p, so the bidual sign is present.
- Characteristic two makes the sign one, without altering the statement.
- An infinite-rank free module in degree zero is not excluded. Its dual's projectivity
  is still an explicit separate hypothesis; no finite generation or evaluation
  isomorphism is inferred.
- T may be unbounded below. For example a sum of copies B[n], n≥0, can have dual
  unbounded above; the separate D upper-bound hypothesis correctly excludes applying
  the final bidual assertion to that case without proof.
- I(O) may be unbounded; no boundedness of the resolution target is imposed.
- The coefficient and localization universe can both be zero. The punctual category
  is Type 0, and max(0,0,u)=u; no extra universe equality is assumed to use the API.
- Naturality includes every derived morphism, including inverses of quasi-isomorphisms.

Searches actually run in this attempt, recorded by msearch.py in searches.jsonl:

- LeanFinder: “The canonical signed bidual map on bounded above projective cochain
  complexes agrees with the derived bidual map through the fixed K injective Hom
  comparison”. Eight hits, including CochainComplex.isKProjective_of_projective and
  HomComplex.CohomologyClass.bijective_toSmallShiftedHom_of_isKProjective. These prove
  K-projectivity/representability, not the full punctual-site normalized comparison.
- Loogle: “CochainComplex.IsKProjective”. Twelve hits; the bounded-above-projective
  lemma is the existing proof leaf, not an exact statement match.
- Mathlib grep: “bidual|toIhomIhomUnit|isKProjective_of_projective”, subdirectory
  Algebra/Homology. Two hits in HomotopyCategory/KProjective.lean, lines 113 and 128;
  no full-item match.
- LeanSearch: “Canonical biduality comparison on bounded above projective complexes
  and the one object site derived Hom with fixed K injective augmentation”. Eight
  hits on injective/projective opposite categories, Module.dual_projective and
  K-projectivity invariance. None states the item. The printed Module.dual_projective
  snippet is not used to infer the node's D hypotheses.
- Local rg of WeilConjectures and Sheaf for the exact blueprint id, bidual,
  double-dual, toIhomIhom, module Hom and singleton-site Hom. The exact id has no
  upstream declaration. PerfectComplexDerivedBiduality states a perfectness and
  isomorphism result, not this representative-normalization theorem. The existing
  ProjectiveHomEvaluationModel gives the projective Hom/evaluation comparison but
  not the fixed punctual-site augmentation transport or the bidual equation.
- Read the actual MonoidalClosed.toIhomIhom and its naturality in the upstream
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided module; reused them
  for bidual. They alone do not state this node's other clauses.

Sources read locally: more-algebra.tex lemma-RHom-out-of-projective, including its
proof using the actual map to a K-injective target; sites-cohomology.tex
lemma-internal-hom-evaluate, including the K-flat/K-injective construction and its
functoriality assertion; sites.tex section-topoi for the punctual topos. The module
proof docstring follows the accepted six-step DAG argument. No source or node
statement was corrected.

Original delivery validation: the final module passed scompile.py in sandbox mode (49.2 seconds)
and library module mode (37.1 seconds), with no errors or non-sorry warnings.
The prescribed deliver2.py --no-push completed with OK: the complete three-file
packet passes server preflight and compiles (dry-run commit 701556000b5).
No direct Git mutation, live-file edit, global build or subagent was used.

## Return repair

The sole H2/H3 point in the independent review of immutable head 180e0cd6b553
is repaired by adding def-trf-ringed-site-ordinary-hom-comparison with an
existing:true record on Sheaf.CategoryTheory.RingedSiteOrdinaryHomComparison.
Its declarations list owns CategoryTheory.ringedSiteHomAugmentation,
CategoryTheory.ringedSiteHomComplexMap and CategoryTheory.ringedSiteOrdinaryHomComparison.
The item's stmt_deps replaces lem-sfb-ringed-site-ordinary-hom-comparison with
this new definition node. The original accepted statement, proof and proof_deps
remain byte-for-byte equal as JSON values to current main; the Lean module is unchanged.
The retained packet passed the initial required dry run at 8fd730d72a9.

The review expressly passed the use of prop-pur-kinjective-resolutions-exist:
only its Grothendieck-abelian conclusion, .1, is used to construct the instance.
That theorem dependency is retained. No theorem choice is substituted for the
fixed augmentation or the fixed localization comparison.

## New nodes

def-trf-ringed-site-ordinary-hom-comparison gives ownership to the existing fixed
augmentation, simultaneous Hom-complex action, and ordinary-to-derived comparison.
The source is Stacks sites-cohomology.tex, Tags 079P, 0A8X and 0A95. It introduces
no module. The signature in lean.statement is extracted verbatim from the existing
comparison definition; the three actual bodies have been read. The augmentation
is toKInjectiveResolution for coefficientHomResolution; Hom(f,g) is precomposition
then postcomposition via homComplexFunctor; the comparison is Q.map of Hom(id,eta)
followed by coefficientHomResolutionIso.inv. Its ringed-site and sheafification
hypotheses match the module variables, with independent c,v,r,w universes. Zero
complexes and unbounded complexes are allowed. No comparison-isomorphism assertion
or extra quasi-isomorphism assumption is part of this definition.

Fresh msearch LeanSearch and LeanFinder queries were “fixed K injective augmentation
ordinary internal Hom complex to derived internal Hom comparison ringed site”: each
returned eight generic injective-resolution or Hom-representability hits, no exact
comparison construction. Mathlib grep for the three exact names in CategoryTheory
returned zero hits. WeilConjectures rg also returned zero hits. The Sheaf source has
the three exact definitions at lines 42, 49 and 60 of RingedSiteOrdinaryHomComparison.
DAG search found their attachment only to the ordinary-comparison theorem node.
Blueprint search found zero matching ordinary-Hom-comparison blueprint nodes.
The new node retains these fresh search records in mathlib_searches.
The related def-trf-ringed-hom-representative-comparison records the ringedHom-prefixed
interface in RingedHomCompositionModel, not the three declarations this return
requires owned. This repair uses the existing declarations and creates no duplicate data.

## Second reading by Q44

Self-check of the returned ownership repair (no other agent was started): reopened
the node, retained Lean module, and the full RingedSiteOrdinaryHomComparison source.
The item's augmentation and Transport square refer to the plain definitions
ringedSiteHomAugmentation and ringedSiteOrdinaryHomComparison. They are not extracted
from ringedSiteOrdinaryHomComparison_isIso, so citing its theorem node was insufficient.
The new definition node now records precisely those maps and their Hom-action helper.
Its formula for c is exactly Q.map (ringedSiteHomComplexMap id eta) followed by the
inverse fixed representative isomorphism; its map order agrees with the source.
All theorem clauses and the four separate T/D hypotheses are unchanged, as requested
by the independent reviewer. The retained clause-by-clause analysis above still applies.
Only metadata ownership and the report changed.

Repair validation: scompile.py completed successfully for the unchanged delivered module
in sandbox mode (49.2 seconds) and library mode (37.1 seconds), with no error or
non-sorry warning. A JSON-value comparison with the current main node confirms that
only lean and stmt_deps differ. The new existing:true signature matches the existing
source verbatim; its cited dependency ids exactly match its stmt_deps.

The repaired-packet preflight requested the current schema field import_flags on
the new node. Added the empty list (this node is new ownership metadata, with no
import fault). The theorem-dependency and route-pivot notices are advisory; the
independent return specifically passes the Grothendieck theorem conclusion use
and requests the unchanged Lean module.
