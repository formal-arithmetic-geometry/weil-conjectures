## Worker report

Stage-2 delivery for lem-sfb-ringed-site-leray-spectral-sequence. The current
node is split, queued for stage 2, and has no Lean attachment. NX's reviewed
stage-1 split was read and preserved. The inherited stale-stage-1 failure does
not apply to this stage-2 assignment (brief-stage2, stage handoff).

The module Sheaf.CategoryTheory.RingedSiteLeraySpectralSequence states
CategoryTheory.exists_ringedSite_leray_spectralSequence, with a single sorry.
It defines no replacement site, module category, global-sections functor,
spectral sequence, or filtration. No statement correction is needed.

Hypothesis and clause correspondence:

- Sites small in the common coefficient universe: explicit universe u,
  C D : Type u, SmallCategory C and D, and Grothendieck topologies J and K.
  This is the small-skeleton convention of def-weil-size-convention. It
  imposes no terminal-object assumption and permits the empty site.
- Commutative structure rings: A : Sheaf J CommRingCat.{u} and
  B : Sheaf K CommRingCat.{u}. Their underlying RingCat sheaves are the
  sheafCompose/forget₂ terms, with no replacement scalar structures.
- Arbitrary ringed-topos morphism: f : RingedToposMorphism of those
  underlying ring sheaves. Its fields inverse, direct, adj, leftExact,
  ringMap, underlying and module_linear are exactly the recorded
  geometric morphism and its induced module action. There is no presented
  site functor, flatness, or exact tensor-pullback hypothesis.
- The direct image is f.modules. Source and target module categories are
  the already recorded coefficientModules abbreviations, transparently
  the same ringedSiteModules / Mathlib SheafOfModules categories.
- Global sections are coefficientSections, the existing composite
  SheafOfModules.toSheaf ⋙ Sheaf.Γ. Its rightDerived n is derived in the
  module category using injective resolutions. The attribute on the
  existing proved SheafOfModules.isGrothendieckAbelian supplies the
  standard enough-injectives and resolution instances; none is assumed
  as an extra mathematical hypothesis.
- The underived comparison t has type f.modules ⋙ Gamma_B ≅ Gamma_A.
  The auxiliary zC and zD are the global elements represented by global
  sections: their evaluations are required to be Sheaf.ΓRes at every
  site object and every generalized point of the terminal sheaf. The
  third equation identifies t on these elements using f.adj.homEquiv,
  terminal.from and f.underlying. Thus t is the geometric comparison,
  not an arbitrary natural isomorphism between these functors.
- The first-quadrant cohomological sequence is E, an existing
  E₂CohomologicalSpectralSequenceNat in the category of functors from
  coefficientModules A to AddCommGrpCat.{u}. This has the required
  cohomological bidegrees and nonnegative indices. Its page morphisms,
  differentials, and homology identifications are natural transformations.
- The equation E₂^(a,b) = H^a(D,R^b f_*F) is the natural isomorphism
  e₂ a b : (E.page 2).X (a,b) ≅ f.modules.rightDerived b ⋙ Gamma_B.rightDerived a.
- Convergence to H^(a+b)(C,F): T n is DecreasingFiltration
  (Gamma_A.rightDerived n), with step 0 = top and step (n+1) = bottom.
  The stable-page clause uses the usual bound r > max(a,b+1).
  For every n,a,b with a+b=n, g identifies its gradedPiece a with
  E.pageInfinity (a,b). Because T and g live in the functor category,
  the filtration and all graded identifications are natural in F.
- The canonical inclusion E_infinity^(0,n) into E₂^(0,n) is j at page
  0+n+2, the literal definition of pageInfinity. Every j is mono;
  j_2 is identity, and the homologyπ / E.iso / iCycles equation
  fixes its recursion from page to page. No arbitrary inclusion is used.
- q n is the quotient H^n to the zeroth graded piece: its composite
  with the top subobject's arrow is the cokernel projection from step 0
  modulo step 1. The edge equation is exactly q, then g, then j, then
  e₂, then the canonical R^0 Gamma_B ≅ Gamma_B identification.
- The final quantifier ranges over every source module M, every
  InjectiveResolution M, and every n. Its c is characterized by the
  cycles inclusion equation, using the same normalized t. Its second
  equation sends the resulting global cocycle through homologyπ, the
  canonical inverse I.isoRightDerivedObj Gamma_A n, edge, and the
  target comparison Gamma_B.map (I.isoRightDerivedObj f.modules n).hom.
  The result is Gamma_B.map homologyπ for f_*I. This is precisely the
  asserted cocycle formula and uses one fixed edge for all resolutions.

Dependency declarations read and used:

- def-weil-size-convention is metatheoretic, with a convention lean record;
  explicit universe u implements its role, so no declaration is copied.
- Sheaf.CategoryTheory.SiteCoveringAxioms,
  CategoryTheory.Precoverage.IsSiteForCoverings: read its full signature,
  bind-composition and covering-pullback clauses. The present theorem
  uses the associated Grothendieck topology and does not add stronger
  assumptions on presented covering families.
- Sheaf.CategoryTheory.RingedSiteModules,
  CategoryTheory.ringedSiteModules; Mathlib.Algebra.Category.ModuleCat.Sheaf,
  SheafOfModules; and Sheaf.Abelian, SheafOfModules.instAbelian.
- Sheaf.CategoryTheory.RingedToposMorphism,
  CategoryTheory.RingedToposMorphism: read all fields, including the
  generalized-element action identities and underlying natural isomorphism.
- Mathlib.CategoryTheory.Preadditive.Injective.Basic,
  CategoryTheory.Injective; Injective.Resolution,
  CategoryTheory.InjectiveResolution (N-indexed, quasi-isomorphic to degree zero).
- Mathlib.Algebra.Homology.SpectralSequence.Basic,
  CategoryTheory.SpectralSequence and SpectralSequence.Hom, via the
  upstream first-quadrant abbreviation and pageInfinity API.
- WeilConjectures.CategoryTheory.Abelian.Filtration,
  CategoryTheory.DecreasingFiltration; CanonicalFiltration supplies the
  transparent step and gradedPiece accessors, with no second filtration.
- Mathlib.CategoryTheory.Preadditive.AdditiveFunctor,
  CategoryTheory.Functor.Additive; Limits.Preserves.Finite,
  CategoryTheory.Limits.PreservesFiniteLimits; Abelian.RightDerived,
  Functor.rightDerived, rightDerivedZeroIsoSelf and
  InjectiveResolution.isoRightDerivedObj.
- Sheaf.CategoryTheory.DerivedSectionsScalarCoherence,
  CategoryTheory.CoefficientDerivedSections.coefficientModules and
  coefficientSections: their full definitions and docstrings were read.
  The new definition node def-sfb-coefficient-module-global-sections owns
  both existing abbreviations with existing:true. It is cited in stmt_deps
  instead of lem-coef-derived-sections-scalar-coherence; the latter theorem
  is not used to state the Leray theorem.

The stated proof dependencies are imported in plain import mode. The
unrecorded acyclicity proof dependency is not required to elaborate the
statement, and is not restated as an assumption. The docstring records
all seven accepted proof steps, including the precise missing acyclicity
input, so stage 3 can use its own node when proved. Mathlib's
isoRightDerivedObj and rightDerivedZeroIsoSelf implement the existing
well-definedness leaf; GrothendieckCategory.EnoughInjectives implements
lem-sp-grothendieck-enough-injectives. No proof dependency import cycle
was introduced.

Sources read: literature/stacks-project/sites-cohomology.tex,
lemma-direct-image-injective-sheaf (072Z), lemma-limp-acyclic (0731),
lemma-Leray (0732), lemma-apply-Leray (0733), and relative-Leray for
comparison; derived.tex lemma-grothendieck-spectral-sequence (015N).
Also read the current latest blueprint's
sk-thm-sf-ctf-stability-direct-images.proof.md. This is an auxiliary
cohomological input; the unit's statement and route are untouched.

Edge cases checked before writing: F=0 gives the zero sequence and
filtration; n=0 gives top at 0, bottom at 1, and the ordinary sections
isomorphism; f=id reduces to the usual sequence with vanishing positive
higher direct images; the punctual ring map Z -> F_p has nonexact module
pullback but is covered, since no flatness is assumed. Sites without a
terminal object are covered by Sheaf.Γ; an empty site causes no binder
failure. The fixed edge is quantified over all resolutions, including
arbitrary isomorphic choices, so resolution independence is retained.

Searches (2026-10-23):

- msearch.py leanfinder: "Natural Leray spectral sequence for module
  sheaves on a morphism of ringed topoi with edge map given by global
  cocycles". Eight hits (module presentations, pushforwardNatTrans,
  pushforwardSections, unitToPushforwardObjUnit, component formulas,
  Sheaf.H, and HasDifferentials); none states the requested theorem.
- msearch.py loogle: "CategoryTheory.SpectralSequence,
  CategoryTheory.Functor.rightDerived". Zero hits.
- msearch.py grep: "Leray|leray", Mathlib/CategoryTheory. Zero hits.
- rg of WeilConjectures and Sheaf for Leray/leray and the item id.
  Existing topological and etale sequences are abelian-only; the generic
  Grothendieck theorem has an acyclicity input and no ringed-topos
  global-sections normalization. Neither is this theorem. The item-id
  search found no existing theorem. Narrow searches found the shared
  coefficientSections definition, which was used instead of duplicated.
- Read the definitions of the recorded dependency declarations in source,
  not merely their names. The repair adds definition-node ownership for the already existing ordinary
  module/global-sections abbreviations; no Lean definition is duplicated.

Validation: module-mode compiler probe checked that the original module
categories have HasInjectiveResolutions and that the composite global
sections functor is Additive. scompile.py compiled the final module in
sandbox and library mode, 17.7 and 18.1 seconds, with no errors or warnings.
Every universe and binder is explicit; autoImplicit is false. All Lean
lines have at most 100 characters. Only the named theorem has sorry.

## Second reading by Q10

Re-read the current node, source and entire final module after compilation.
Checked the direction of t: target sections after f_* -> source sections;
its normalization uses adj.homEquiv in the inverse-to-direct direction.
Checked e₂: rightDerived b of pushforward followed by rightDerived a of
Gamma_B, in that order. Checked the graded indices a+b=n, both finite
filtration endpoints, and the literal stable page (0+n+2 : N). Checked
j's recursion against the column-zero cycles inclusion, where there are
no incoming differentials. Checked q's cokernel type and the edge's
R^0 identification. Checked the cocycle equation against the source and
the existing grothendieck_left_edge_cocycle signature; all comparison
isomorphisms have the correct direction, and the same edge is used for
every resolution. The site and module universes are u throughout, as in
the recorded arbitrary-ringed-topos interface, without requiring a
terminal object or a functor between site presentations. No added
flatness, preservation-of-injectives or acyclicity hypothesis occurs.
The Leray statement and its Lean module are unchanged. The additional
statement dependency is now the definition-node owner of the two reused
abbreviations, rather than the scalar-coherence theorem.


## New nodes

def-sfb-coefficient-module-global-sections owns the two existing abbreviations
CategoryTheory.CoefficientDerivedSections.coefficientModules and coefficientSections
in Sheaf.CategoryTheory.DerivedSectionsScalarCoherence (existing:true). Its source
is sites-cohomology.tex, equation-global-sections, the module-cohomology definition,
and lemma-Leray (0732). A small site is C : Type u with SmallCategory C and
GrothendieckTopology C; R : Sheaf J CommRingCat.{u} is the coefficient sheaf.
coefficientModules is exactly ringedSiteModules of its forget₂ ring sheaf.
coefficientSections is exactly SheafOfModules.toSheaf _ ⋙ Sheaf.Γ J AddCommGrpCat.{u}:
its objects are compatible section families with their abelian-group operations,
and its morphisms apply the underlying sheaf morphism. The existing definitions
have complete data and do not invoke the scalar-coherence theorem. The small-site
instances supply the sheafification/global-sections structures automatically.
No site terminal-object hypothesis is imposed. This does not create another
module category, global-sections functor, or copy of either abbreviation.

The three new msearch queries (leansearch on module global sections, loogle on
SheafOfModules.toSheaf and Sheaf.Γ, grep on Γ/toSheaf definitions) returned respectively
eight component hits, zero hits, and five sheafification/local-site hits. Their
original machine records are included in mathlib_searches. Searches of WeilConjectures,
Sheaf, all DAG declarations, and blueprint_refs.py search 'global sections' found the
existing project abbreviations but no definition-node owner. Other global-sections
nodes concern derived, condensed, fixed-scalar, or particular-site constructions.

## Repair of independent review at b09a244b1ea9

Repaired the single H2/brief-stage2 §1 return: replaced the additional statement
dependency lem-coef-derived-sections-scalar-coherence by
def-sfb-coefficient-module-global-sections. The definition node records both
abbreviations already present in the imported module. The Leray Lean file remains
byte-identical to the returned file and the saved packet; its statement, seven-step
proof docstring, hypotheses, filtrations, normalization and edge formula are retained.
Only stmt_deps and lean differ from the current main item's node. No statement
correction or dependency module is needed.

The resumed self-check read the new definition statement against both full abbreviation
bodies and the source equation-global-sections. Empty sites give a unique compatible
family; zero module sheaves give the zero abelian group; a terminal site object recovers
evaluation, and the absence of such an object requires no extra binder. A zero ring
and nonflat scalar change do not change the definition. Both declarations are listed
in lean.declarations and their module remains the same imported module as before.
The new node's blueprint ancestor and via path, chapter and unit match the item's.
The saved pre-repair packet passed deliver2.py --no-push at 0e138f30669; it was not
pushed because the independent ownership return still required this explicit repair.

Repair validation: scompile.py checked the unchanged Leray file cleanly in both
sandbox and library modes. The first repaired dry run requested the now-required
import_flags field on the new node; it is supplied as an empty list.
