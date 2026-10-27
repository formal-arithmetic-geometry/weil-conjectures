## Worker report

Item: lem-pur-resolving-tensor-signed-coherence. Group Q25, stage 2, 2026-10-22.
Module: lean/Sheaf/Algebra/Homology/ResolvingTensorSignedCoherence.lean.

Repair of the independent stage-2 return on immutable head 027ab8fc312a.
The saved packet was inspected first, and the initial required dry run passed
(commit cae812c2f0d). The return identifies one H2 issue: the packet added
lem-pur-derived-tensor-additive-constraints as a statement dependency even though
the statement uses its definition interface, not its theorem conclusion. The
repair adds def-pur-derived-tensor-constraint-normalization with existing:true on
the unchanged definitions, and substitutes that definition node in stmt_deps.
The theorem node remains the original proof dependency. The full Lean module,
including its imports, signature, docstrings and sole sorry, is unchanged from
the independently reviewed delivery. All other node fields match current main.

The definition transportedComparison is the actual composite of natural
isomorphisms eta inverse, muL, and eta prod eta followed by the target tensor.
It has no sorry or choice of new data. The sole theorem
SheafOfModules.ResolvingTensorSigned.resolving_tensor_signed_coherence has proof
sorry, with all seven accepted proof steps in its docstring. It states all the
conclusions for this specified comparison. No source statement or accepted split
has been changed. The new definition node records the existing normalization
interface; no dependency module is repaired.

Hypotheses and objects, clause by clause:

- Ringed sites and relative smallness: C : Type uC, Category.{vC} C,
  EssentiallySmall.{r} C, J : GrothendieckTopology C, and independent uD,vD for
  D,K. R : Sheaf J CommRingCat.{r} and S : Sheaf K CommRingCat.{r} share the
  coefficient/module universe r, just as the node specifies. Neither site
  object universe nor its Hom universe is identified with r or with each other.
- Ordinary module sheaves: KFlatFixedTensor.Modules R and Modules S transparently
  use ringedSiteModules and Mathlib SheafOfModules. This is the dependency's
  category, not Sheaf (ModuleCat Lambda) or an arbitrary abelian category.
- The geometric morphism, finite-limit preservation, structural ring map and
  actual scalar-extension pullback F are the existing CochainPullback.RingedPullback
  f. Its fields uInv,uPush,adj,finiteLimits,I,coefficient,hobj,hmap specify
  exactly these data. f.L is F. Its moduleAdj is the canonical module adjunction
  available from this presentation, not a new mathematical restriction.
  CochainPullback.ringedPullbackPresentation_exists supplies it for every such
  ringed geometric morphism. k : Comparison f specifies the canonical module
  comparison by its insertion-of-one formula, and comparison f k is the actual
  cochain comparison in the node.
- F exact: f.L.Additive is the instance in the existing presentation;
  PreservesFiniteLimits f.L and PreservesFiniteColimits f.L supply the other
  two exactness requirements.
- Unbounded derived categories and q_R,q_S: the two HasDerivedCategory binders
  retain independent localization universes wR,wS; DerivedCategory.Q is the
  complex-localization presentation of the same derived category.
- L = Lu*: the functor L, natural transformation epsilon, and hL asserting
  L.IsLeftDerivedFunctor epsilon (HomologicalComplex.quasiIso ... (.up Z))
  use the complex-localization presentation of the canonical pullback from
  the dependency. Factoring through the homotopy quotient gives its recorded
  homotopy presentation. The computation e_P is epsilon.app P; on resolving
  P this is invertible by the dependency and also by the displayed heta identity.
- Resolving P means precisely P.IsKFlatIndependentCoefficients together with
  forall n, IsFlatOnSite (P.X n). hflat records preservation of flat sheaves;
  hresolving records preservation of that conjunction on all complexes;
  hsums records preservation of all coproducts indexed by I : Type r.
- U = D(F) and kappa are f.L.mapDerivedCategory and
  f.L.mapDerivedCategoryFactors. Integer comparisons s are U.commShiftIso n,
  supplied by exact localization, not arbitrary separately chosen maps.
- The given shift-compatible eta is eta : L isomorphic U with
  NatTrans.CommShift eta.hom Z. Its model normalization is heta:
  eta.hom.app (Q.obj P) followed by mapDerivedCategoryFactors.hom.app P equals
  epsilon.app P for every resolving P. This is kappa_P eta_P = e_P in the
  node's right-to-left composition notation.
- The actual K-flat derived tensors and r maps are KFlatFixedTensor.derivedTensor,
  canonicalDerivedTensor (its transparent published alias), representativeIso
  and canonicalRepresentativeIso. The tensors are never reselected.
- The normalized canonical mu^L is muL : Phi L isomorphic Psi L, with hmuL
  asserting PullbackTensorCanonical.IsNormalized f k L epsilon muL.hom.
  The cited canonical-shift-unit theorem determines this comparison uniquely
  from this property, so quantifying over a muL with this property states the
  assertion for precisely the specified canonical comparison.
- The L and tensor shift data, their canonical normalization and compatibility
  with epsilon are the existing CommShift, CommShift2Int,
  NatTrans.CommShift epsilon, hshiftR and hshiftS binders. These express the
  canonical comparisons already specified by the node's dependencies.
- Derived alpha,alpha' and sigma,sigma' are the natural isomorphisms alphaR,
  alphaS,sigmaR,sigmaS between the existing DerivedTensorConstraints functors.
  hconstraintsR and hconstraintsS use the EXISTING IsNormalized predicate.
  Existentially projecting its shift component retains exactly its unsigned
  reassociation and Koszul braiding normalization clauses. Such a shift witness
  exists by existsUnique_derived_tensor_constraints, for the normalized alpha
  and sigma; this does not add a restriction on the specified constraints.
  That projected witness uses the other extraction order and is NOT used as
  t in the displayed shift conclusion. The shift conclusion expands the node's
  first-then-second extraction explicitly, over both rings.

Conclusions, clause by clause:

- mu = (eta tensor eta) muL eta inverse is transportedComparison f L muL eta.
  It is a natural isomorphism by its TYPE and its construction from whiskering
  and composition of the given natural isomorphisms. There is no existential
  substitution by an arbitrary comparison.
- The first conjunct is PullbackTensorCanonical.IsNormalized for U and kappa.
  Unfolding its existing definition gives U(r_EG) followed by mu then
  kappa_E tensor kappa_G equal to kappa_T(E,G) followed by Q(c_EG) then
  r'_(FE,FG), for every K-flat flat-term pair. Thus it is exactly the displayed
  representative equation, including the comparison at the total V, with the
  standard left-to-right Lean composition order. Its existential resolving
  proof witnesses only permit using r' on FE,FG; no extra data is chosen.
- The second conjunct quantifies over ALL tau : Phi U to Psi U. The very same
  representative condition forces tau equal to transportedComparison.hom.
  This is uniqueness among natural transformations, not just isomorphisms or
  objectwise families.
- The third conjunct is the simultaneous shift equation for every a,b : Z
  and arbitrary A,B. Its left side is mu on shifted inputs, s_a tensor s_b,
  and t' in that order. Its right side is U(t), s_(a+b), and shifted mu.
  Each t is expanded into the first-variable commShiftIso a, shift by a of
  the second-variable commShiftIso b, and shiftFunctorAdd' b a (a+b) inverse.
  Removing a first is unsigned; b then sees original first-factor degree p,
  so the coefficient is (-1)^(bp), as required.
- The fourth conjunct is U(sigmaR) followed by mu_(B,A) equal to mu_(A,B)
  followed by sigmaS_(UA,UB), exactly the symmetry equation.
- The fifth conjunct is U(alphaR), mu_(A,B tensor N), 1 tensor mu_(B,N)
  equal to mu_(A tensor B,N), mu_(A,B) tensor 1, alphaS_(UA,UB,UN).
  Both sides have the prescribed ternary source and target.
- No degree bound appears in any complex or derived-object binder. Every total
  is the existing direct-sum total, also for doubly unbounded complexes.

Dependency declarations read and used:

- def-weil-sheaf-of-modules-category: Sheaf.CategoryTheory.RingedSiteModules,
  CategoryTheory.ringedSiteModules; Mathlib SheafOfModules and its abelian category.
- def-pur-sheaf-tensor-product:
  Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses,
  SheafOfModules.cochainModulesMonoidal and its existing tensor instances.
- def-weil-abstract-derived-category:
  Mathlib.Algebra.Homology.DerivedCategory.Basic, DerivedCategory,
  HasDerivedCategory and DerivedCategory.Q.
- def-pc-kflat-complex: Sheaf.Algebra.Homology.KFlatIndependentCoefficients,
  CochainComplex.IsKFlatIndependentCoefficients.
- def-pc-flat-sheaf-modules:
  Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite, SheafOfModules.IsFlatOnSite.
- lem-weil-pbc-ringed-topoi-derived-pullback:
  Sheaf.Paper.RingedTopoiDerivedPullbackIndependent,
  SheafOfModules.ringedTopoiDerivedPullbackIndependent and
  RingedPullbackResolutionComparisons. The universal derived comparison is
  used through the equivalent complex-localization interface already used by
  the recorded canonical-shift-unit module.
- lem-weil-pbc-exact-functor-derived-factorization (Mathlib match, no Lean record
  required): Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor,
  CategoryTheory.Functor.mapDerivedCategory, mapDerivedCategoryFactors and
  their canonical CommShift instances.
- lem-weil-pbc-site-derived-tensor-descent:
  Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients,
  SheafOfModules.site_derived_tensor_descent_independentCoefficients and
  siteDerivedTensorIndependentCoefficients; the named published representative
  interface is exposed by KFlatFixedTensorTriangulated and the canonical module.
- def-pc-tensor-complex-sheaves: Mathlib.Algebra.Homology.BifunctorShift,
  CochainComplex.mapBifunctor, via KFlatFixedTensor.totalTensor.
- lem-pur-cochain-pullback-tensor-coherence:
  Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence,
  CategoryTheory.CochainPullback.cochainPullbackTensorCoherence and its public
  RingedPullback, Comparison, pull, comparison interfaces.
- lem-weil-pbc-pullback-tensor-canonical-shift-unit:
  Sheaf.Paper.PullbackTensorCanonicalShiftUnit,
  SheafOfModules.PullbackTensorCanonical.Phi, Psi, IsNormalized,
  HasCanonicalTensorShifts, canonicalDerivedTensor, canonicalRepresentativeIso
  and pullback_tensor_canonical_shift_unit.
- lem-weil-pbc-total-tensor-integer-shifts (Mathlib match):
  Mathlib.Algebra.Homology.BifunctorShift,
  CategoryTheory.Functor.instCommShift2IntCochainComplexIntMap2CochainComplex
  (the actual Lean name uses subscript Unicode 2), CochainComplex.mapBifunctorShift1Iso
  and mapBifunctorShift2Iso (also with subscript Unicode). The first-argument
  unsigned and second-argument signed comparisons are the ones transported
  into HasCanonicalTensorShifts, and are composed in the node's stated order.
- def-pur-derived-tensor-constraint-normalization (new definition node with
  existing:true; the theorem node lem-pur-derived-tensor-additive-constraints
  stays only a proof dependency):
  Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints,
  SheafOfModules.DerivedTensorConstraints.leftAssociated, rightAssociated,
  tensor, swapped, shiftedSource, shiftedTarget and IsNormalized. No existsUnique_derived_tensor_constraints conclusion occurs
  in the Lean statement; alpha and sigma remain free binders subject to the
  existing normalization predicate. The theorem is used by the accepted proof
  plan for finite-variable faithful restriction, not to define those binders.

The module publicly imports statement-dependency interfaces and plainly imports
KFlatTotalTensorModel for the accepted proof plan. Transitive public imports
provide the lower tensor, flatness, K-flatness, and shift dependencies.

Sources read: sites-cohomology.tex lemma-pullback-tensor-product at line 3684
(Stacks 07A4), more-algebra.tex item-shift-tensor at line 18385 and
item-flip-tensor-product at line 18405. The current main-20261015
lem-pur-frame-independence.proof.md was also read: the generic comparison serves
its even-degree permutation sign and supported product pullback steps. The
accepted seven-step refinement remains unchanged.

Edge cases checked before and after writing:

- Zero complexes and zero sheaves: all types and comparisons remain valid;
  no nonzero or nonempty hypothesis is present.
- Empty sites and the empty coproduct: no site-object choice is made, and
  hsums includes an empty I.
- a=b=0: both extraction maps are the coherent zero-shift comparisons; no
  unnecessary sign is introduced.
- a,b,p all odd: extracting a before b gives (-1)^(bp); extracting b first
  would differ by (-1)^(ab). The actual conclusion uses a before b on both
  sides, so does not silently import the other convention from the auxiliary
  constraint theorem.
- Negative integer shifts: all binders and shift-addition comparisons use Z,
  with no natural-number restriction.
- Odd p,q in symmetry and triple products: sigma is the localized Koszul
  braiding, whereas alpha is unsigned reassociation.
- Degree-zero flat sheaves and units: the representative equation specializes
  to the insertion-of-one/contraction scalar-extension comparison.
- Nonflat derived inputs and complexes unbounded in both directions: resolving
  hypotheses occur only in representative normalizations, not on A,B,N.
- Independent site object, morphism, coefficient and derived-morphism
  universes: each is an explicitly declared universe parameter; no equality
  identifying these sizes has been imposed. autoImplicit is false.

Searches for an existing statement:

- msearch.py leanfinder, query: "Transport a representative normalized derived
  tensor comparison along a shift compatible natural isomorphism of exact ringed
  site pullback functors, preserving signed shifts symmetry and associativity".
  Result: eight hits on ordinary sheaf pullback composition/conjugacy and
  pullback of free sheaves; none states this derived normalized coherence theorem.
- msearch.py loogle, query: "CategoryTheory.NatIso.prod,
  CategoryTheory.Functor.mapDerivedCategoryFactors, CategoryTheory.Functor.CommShift".
  Result: zero hits.
- msearch.py grep, query "tensor.*[Cc]omparison|[Cc]omparison.*tensor" under
  CategoryTheory/Monoidal. Result: eight hits about cartesian/closed product
  comparison maps, no derived representative-normalized theorem.
- rg in lean/WeilConjectures and lean/Sheaf by the node ID, resolving/signed
  coherence names, and transport/tensor comparison terms. No declaration is
  attached to this node or states the whole assertion. The parent
  ExactPullbackSignedComparison contains a broader existential theorem,
  not the present theorem for a GIVEN eta and muL. Its tensor constraint
  interface cannot be imported here without making a proof-import cycle
  when this child is used by that parent. The existing independently owned
  DerivedTensorAdditiveConstraints interface supplies the required notions,
  now owned as definitions by the new existing:true definition node.
- Existing definitions were opened at full signatures and docstrings; only
  the new transport composite is constructed. No second tensor, K-flatness,
  flatness, localization, cochain pullback or derived constraint is defined.

No STATEMENT-DISPUTED flag is warranted. There is no statement correction and
therefore no statement_change or correction citer audit.

Validation: all compiles use the prescribed scompile.py wrapper and its 60 s
limit. An initial namespace qualification error in whiskering was repaired by
opening CategoryTheory.Functor. The elaboration timeout was repaired by
keeping the transport composite opaque during statement elaboration and avoiding
an expensive redundant sheaf-compose instance search. scompile.py then returned
exit 0: sandbox compilation 38.1 s and library compilation 40.5 s, with no errors
or unexpected warnings. The 60 s limit was unchanged. Delivery results follow
below after validation completes.

## Second reading by Q25

A separate rereading pass by the same dispatched worker compared the item,
source sign rules, existing interfaces and final statement. No second agent was
started, as this dispatch explicitly prohibits it; the maintainer's independent
review remains the independent reading of the delivery.

The pass checked the actual component formula of transportedComparison, the
orientation of the representative equation in IsNormalized, the quantifier over
all natural transformations, and each endpoint of the three coherence equations.
It checked that the two existential constraint-shift witnesses are used only
to express the already prescribed alpha and sigma, and that the conclusion's
shift maps instead extract a before b over both rings. It also checked exactness,
all preservation hypotheses, the given normalized shift-compatible eta, arbitrary
unbounded inputs, and independent site and coefficient universes. No mathematical
mismatch was found. The only changes from the first draft were namespace and
elaboration handling; no hypothesis or clause was removed to address a timeout.

## New nodes

def-pur-derived-tensor-constraint-normalization records the existing
SheafOfModules.DerivedTensorConstraints.IsNormalized definition, its tensor and
shifted/swapped/reassociated functors, resolving model dictionary and representative
helpers in Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints. It uses
existing:true and supplies no second definition or module. Its self-contained
statement expands each of IsNormalized's three clauses: the representative
shift conjugation, unsigned associator conjugation, and Koszul braiding
conjugation. It asserts no existence or uniqueness theorem. Sources: Stacks
06YU and 0FPT, more-algebra.tex section-sign-rules. The helper chainShift removes
the right shift before the left and uses shifted first-factor degree; this is
explicit in the new node and unchanged from the existing predicate. The consumer's
separate shift conclusion still removes the first shift before the second and
uses original first-factor degree. Those two conventions have not been conflated.

New-node searches (all run with msearch.py, exact queries/results in
mathlib_searches and searches.jsonl): LeanSearch queried "Definition of
representative normalization for derived tensor associativity Koszul symmetry
and simultaneous integer shifts on flat term K flat complexes" and found eight
hits on chain associators/free monoidal normalization; LeanFinder queried "A
predicate specifying that derived tensor associator symmetry and shift natural
isomorphisms equal the conjugates of their signed chain maps under K flat
representative isomorphisms" and found eight hits on chain tensor/associator
components; grep queried "IsNormalized|shiftRepresentative|leftRepresentative|
rightRepresentative" in Mathlib Algebra/Homology and found no hits. No Mathlib
predicate provides this exact definition. rg over lean/WeilConjectures found no
DerivedTensorConstraints; rg and full reading of lean/Sheaf locate the existing
public interface above. DAG searches found the theorem node already carrying
these helper declarations in lean.declarations, but no definition node for this
notion. This is exactly the definition ownership repair the return requests.
blueprint_refs.py search "representative normalization" returned zero blueprint
nodes; its ancestor query identified lem-pur-frame-independence. The broader
derived-tensor search showed other tensor definitions, none owning this predicate.
The new node cites the existing tensor descent, model closure, and fixed-tensor
shift nodes its representative helper definitions use. Every cited id appears in
its statement. Its blueprint path starts with the present item and follows the
item's existing path, with the same chapter and unit.

## Repair self-check by Q25

Reread the returned H2 issue against current main, the saved module, and the full
existing IsNormalized signature and implementation from both local read clone
and scompile.py --source. The saved module is byte-for-byte unchanged. The new
node's definition has the same parameters t, alpha, sigma and exactly the three
conjuncts of IsNormalized: all integer a,b and resolving E,F for shifts; all
resolving E,F,G for unsigned reassociation through leftRepresentative and
rightRepresentative; all resolving E,F for Koszul symmetry through representative.
The helpers use the fixed published tensor and Q, not a second choice. The new
node records only definitions/abbreviations, not any theorem declaration. Ringed
site universes, the independent derived Hom universe, zero objects, empty sites,
negative and zero shifts, odd-degree signs, and doubly unbounded representatives
remain as in the existing declarations. The accepted consumer signature and all
five conclusion clauses are preserved. No statement_change is needed: this fixes
statement-dependency ownership without changing the mathematical statement.
The original theorem node remains in proof_deps and its module remains publicly
imported because the newly recorded definition interface lives in that module.
No sub-agent was started; this is a self-check and the maintainer supplies the
independent review.

Repair validation: the prescribed scompile.py compiled the delivered consumer
module cleanly (sandbox 38.1 s, library 40.5 s), within the unchanged 60 s limit.
The first repaired-packet preflight found only four grouped dependency citations
in the new node; these were separated into individual bracketed node IDs as
required by its parser. The item signature was checked byte-for-byte against its
lean.statement record using the actual proof delimiter, and has one named sorry.
The new definition signature likewise matches the existing source verbatim.
The repaired packet passed deliver2.py --no-push: "OK (dry run): commit
a73d83a192f passes the preflight and compiles; nothing pushed". This validates
the existing definition reference and the delivered consumer separately. Final
metadata cleanup updates the stale lean.note to name the new definition node;
no Lean file or mathematical statement changes in that cleanup.
