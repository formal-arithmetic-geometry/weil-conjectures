## Worker report

Repair of returned immutable head f8683cb6bd52. Inspected the saved packet and ran
its required dry run before editing. It failed in BoundaryAlphaMaps.lean with
`unexpected token '/--'; expected ':=', 'where' or '|'`: the saved projection-formula
abbreviation had no body. The saved finite-Tor abbreviation also returned True, its
conclusion was opaque, and its split module/node records were unfinished. Removed
these intermediate experiments, restored the actual finite-Tor predicate and the
explicit theorem conclusion, and consolidated all item-owned helper constructions
into BoundaryAlphaNormalization.lean. There are no new definition nodes. Refreshed
each delivered node from the current shared DAG and retained only its lean repair;
the natural-language statements and statement dependencies are unchanged.
The main module is Sheaf.SixFunctors.BoundaryAlphaNormalization. Its conclusion is
AlgebraicGeometry.Etale.boundaryAlphaNormalization. The additional Lean modules are the §1(B) repairs of Sheaf.Paper.DualityPairing and
Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses. The existing ordinary-etale
finite-Tor predicate is used through one further §1(B) record repair. No new DAG node is needed.

Hypothesis-by-hypothesis correspondence:

- The finite-field datum is D : WeilConjectures.FiniteFieldDatum; its k is D.k and p
  is D.p. The prime is l with Fact l.Prime and _hl : l ≠ D.p.
- The finite extension is E with Field, Algebra (Padic l) E, and FiniteDimensional.
  boundaryCoefficient l E n abbreviates ULift (Padic.coefficientExtensionRing l E
  (n+1)). That recorded quotient uses the chosen uniformizer. Index n+1 covers exactly
  all positive levels. The lift implements the recorded ModuleCat.{u+1} convention;
  it does not identify a site's object and morphism universes.
- T and Z are Scheme.{u}, aT maps T to Spec D.k, and aT has IsSeparated,
  LocallyOfFiniteType and QuasiCompact. The map i : Z → T has IsClosedImmersion.
  Its structure map is i ≫ aT, so Z is also separated of finite type over D.k.
  There is no independently chosen structure map or omitted equation over k.
- The categories are exactly Etale.DerivedCategoryModule A T/Z, where A is the
  preceding lifted quotient; their objects are ordinary unbounded derived complexes
  of small-etale A-module sheaves. All operations in the displayed assertion are
  etale. The pro-etale comparison C_W in the node's introductory conventions does not
  occur in its claimed Hom chain, q, r, alpha, or naturality assertion; no independent
  pro-etale test category or transport is introduced into those assertions.
- F is R(lowerStar (ModuleCat A) i), the ordinary derived closed direct image, equal
  to Ri_! in the stated closed case. boundaryG A i is its actual ambient rightAdjoint,
  using isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion, and every use of
  its adjunction/counit is Adjunction.ofIsLeftAdjoint of this F. The already landed
  node lem-exc-closed-ambient supplies that exact interface through its imported module.
  The compact-support dependency remains imported through the pairing module.
- boundaryOmegaT A aT is the existing dualizingComplex (ModuleCat A) aT, namely
  the structure-map ordinary exceptional inverse image of the tensor unit A.
  boundaryDT is the existing verdierDual. boundaryDZ is precisely derivedHom into
  boundaryG.obj boundaryOmegaT, so omega_Z = G omega_T, as in the node.
- _hDK, hK, _hiK and hGDK are the four stated memberships, using the existing
  finiteTorConstructibleEtale, not predicates supplied by a caller. Its body is
  isBoundedConstructible AND one ordered interval in hasTorAmplitudeIn. The latter
  quantifies over every sheaf placed in degree zero, with one interval for all of them.
- _hdual says exactly that derivedHom into G omega_T preserves this predicate on Z.
- hPF quantifies over bounded constructible B on Z and finite-Tor constructible M
  on T, and says IsIso of boundaryProjection. That definition is literally
  ((rightDerivedLowerStarProjectionMap (ModuleCat A) i).app B).app M. Its tensor
  order is FB tensor M → F(B tensor i^*M). The node's other order is obtained by
  the two specified signed symmetries, as expanded in its proof step 2. Thus hPF
  assumes invertibility of the canonical map, not an arbitrary projection isomorphism.

Construction-by-construction and conclusion-by-conclusion correspondence:

- boundarySigma extracts the standalone normalized symmetry of the pairing dependency.
  etaleKoszulSymmetry fixes every hom component by HEq to DerivedMonoidal.braiding;
  equality of these components determines each component isomorphism and its inverse.
  Its existential proof therefore does not choose undetermined data.
- boundaryEvaluation is symmetry DK,K followed by the tensor-Hom adjunction counit.
  DK is computed as (derivedHom.obj (op K)).obj W. The definition is exactly the
  evaluation normalization of AmbientDualityPairing; there is no ev parameter.
- boundaryAlphaQ applies the actual exceptional homEquiv to F of the Z symmetry,
  inverse of the canonical pi, the T symmetry, and 1 tensor the exceptional counit.
  The first three arrows are the node's PF inverse after resolving the tensor order.
  The argument hPi is only a proof of IsIso of this fixed map.
- boundaryAlphaR is sigma_{GDK,LK}, q_{K,DK}, then G of sigma_{K,DK} followed by
  boundaryEvaluation. Thus its domain and codomain and both signed symmetries agree
  with the displayed r_K. DK cannot be changed independently of K and W.
- boundaryAlpha transposes r through the actual derivedTensorHomAdjunction at LK,
  after the required interchange from LK tensor GDK to GDK tensor LK.
- boundaryAlphaHomChain is an Equiv, built independently of alpha by seven explicit
  Equiv.trans factors: exceptional homEquiv inverse, tensor-Hom inverse, source
  symmetry via Iso.homCongr, projection via Iso.homCongr, exceptional homEquiv,
  the second source symmetry, then tensor-Hom. In particular it is NOT defined as
  b followed by alpha. The normalization equality is a substantive theorem clause.
- The first conclusion is IsIso of the specified boundaryAlpha with W = omega_T.
- The second conclusion quantifies over every finite-Tor constructible B and every
  b : B → G(D_T K), and equates the independent Hom-chain value to b ≫ alpha_K.
- The third conclusion quantifies over every other K' satisfying all four membership
  conditions and every u : K → K'. It states G(D_T u) ≫ alpha_K =
  alpha_K' ≫ D_Z(i^*u). This is the required contravariant naturality in K.

Dependency declarations used and read:

- Sheaf.Paper.FiniteFieldFiber: WeilConjectures.FiniteFieldDatum.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite (and CoefficientExtension):
  Padic.coefficientExtensionRing and finite_coefficientExtensionRing.
- Mathlib morphism modules: IsClosedImmersion, IsSeparated, LocallyOfFiniteType,
  QuasiCompact; finite type has exactly the recorded conjunction encoding.
- WeilConjectures.SixFunctors.Etale.Derived.Coefficients:
  Etale.DerivedCategoryModule; Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes:
  DerivedCategory.isBoundedConstructible.
- Sheaf.Paper.FiniteTorAmplitudeSites: finiteTorConstructibleEtale, whose two factors
  are that recorded bounded-constructible predicate and Etale.hasTorAmplitudeIn.
- WeilConjectures.SixFunctors.Etale.Derived.Hom: derivedHom and
  derivedTensorHomAdjunction, publicly available with the original ringed-site
  derivedInternalHomOfUniverses through Sheaf.Paper.DualityPairing.
- WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection:
  rightDerivedLowerStarProjectionMap. Its full signature, tensor order and mate
  description were checked; FlatModuleCat supplies the exact pullback flatness instance.
- Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint:
  isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion.
- WeilConjectures.SixFunctors.Etale.Derived.Dualizing: dualizingComplex, verdierDual;
  their ordinary rightDerivedUpperShriek and compact-support definitions were read.
- Sheaf.Paper.DualityPairing: AmbientDualityPairing, ambient_duality_pairing and the
  new component interface etaleKoszulSymmetry, retaining every original declaration.

Edge cases: K = 0 and B = 0 are allowed; both sides are the corresponding unique
morphisms and no nonzero hypothesis is introduced. Z may be empty. For i = identity,
the functors and their adjunctions retain their actual unit/counit identifications;
there is no unsupported claim that chosen right adjoints are definitionally identities.
Degree shifts use the descended Koszul symmetry in both tensor interchanges; their
cancellation is described in the proof plan, not replaced by an unsigned swap. Every
positive coefficient level occurs (including level one). No inverse is formed until
its particular projection component has its supplied IsIso proof. The Hom-chain
tests are exactly finite-Tor constructible B, not all ambient pro-etale objects.

Searches: msearch.py leanfinder "evaluation normalized costalk duality projection
formula internal Hom natural isomorphism" returned eight generic smooth-sheaf
stalk/evaluation declarations, no costalk theorem. Loogle "CategoryTheory.Adjunction.homEquiv,
CategoryTheory.ihom" returned seven currying/equivalence declarations, no exact statement.
Mathlib grep "expComparison|rightAdjointProjectionMap" in CategoryTheory returned the
Cartesian exponential-comparison constructions; those do not give this derived module
statement. rg for the item's id in WeilConjectures had no hit. rg over lean/Sheaf
found the established finiteTorConstructibleEtale interface, the closed ambient adjoint,
and neighboring costalk/duality interfaces, but no evaluation-normalized Hom-chain
and naturality theorem. These were reused rather than privately recast. The returned head's abstract q/r/alpha organization is retained, with its parameter choices
replaced by canonical constructions. No natural-language statement correction or
STATEMENT-DISPUTED flag is needed.

## Dependency modules

lem-weil-duality-pairing: retained its entire published module and all old declarations,
and added etaleKoszulSymmetry, the standalone normalized symmetry already constructed
in its proof step 1. The original geometric theorem exposes the symmetry only after
choosing its dualizing object and invertible-exponent datum; direct specialization of
the raw DerivedMonoidal.braiding expression to the fixed-coefficient derivedTensor
interface hit a kernel deterministic timeout (isolated with a bounded diagnostic).
The added interface exposes exactly the independently constructed symmetry, with its
HEq normalization of each component isomorphism. It requires no extra assumption in the item and determines its data
uniquely. Its postponed proof and source are explicitly documented and it is included
in the dependency's lean.declarations.

def-pur-derived-internal-hom: the old primary API has domain D(SheafOfModules R), so
it cannot be applied directly to the recorded DerivedCategoryModule of fixed scalar
module-valued sheaves. The dependency module retains every original generic definition,
resolution comparison and representative comparison unchanged, and adds only a public
import of WeilConjectures.SixFunctors.Etale.Derived.Hom. The imported ordinary-etale
derivedHom and derivedTensorHomAdjunction are recorded alongside the generic primary
interface. The item uses that existing canonical closed derived Hom and its actual
counit. No MonoidalClosed hypothesis or private Hom construction is introduced.
The import probe and preflight require this defining module to expose all listed
interfaces; the one-line public-import repair supplies exactly that API.

def-weil-finite-tor-amplitude: the old primary declaration is on the intrinsic
pro-etale derived category. The lean-only existing-declaration repair records the
already published finiteTorConstructibleEtale for the ordinary-etale presentation
required by this item. Its finite-value constructibility and uniform Tor interval
are unchanged existing definitions. The original pro-etale, integral, and field-stage
notions stay available in their original module.

## Second reading by NW

A separate second pass in this worker session checked the node and the repaired Lean
clause by clause; no additional agent was started. The maintainer's independent review
remains separate. The original report's claim that arbitrary category parameters stood
for the canonical objects was rejected during this pass and removed.

H3: the finite-field datum, coefficient extension, positive level, aT and closed i now
appear explicitly. Categories, F, G, omega_T, omega_Z, D_T, D_Z, evaluation, symmetries
and projection are fixed by existing declarations. The four membership assumptions
and duality-preservation assumption were individually matched above. hPF is restricted
exactly to the stated inputs. The naturality clause now includes all four admissibility
conditions on K' and the correctly directed contravariant square. The categories carry
the actual small-site universes; no arbitrary C,D or equality of their universes is a
hypothesis.

H5/H6: inspected every factor in boundaryAlphaHomChain. Its endpoints are respectively
Hom(B,GDK), Hom(FB,DK), Hom(K tensor FB,omega_T), Hom(FB tensor K,omega_T),
Hom(F(B tensor LK),omega_T), Hom(B tensor LK,Gomega_T), Hom(LK tensor B,Gomega_T),
and Hom(B,RHom(LK,Gomega_T)). None of these factors refers to boundaryAlpha.
The theorem compares this independent bijection with postcomposition by the r-defined
alpha; that comparison is postponed, not discharged by reflexivity.

H4/H13: checked the existing-declaration repair, the generic Hom module export,
and the component extraction
in the retained pairing module. No abstract predicate, arbitrary evaluation, arbitrary
projection isomorphism, or assumed MonoidalClosed structure survives in the theorem.
The standalone family of component isomorphisms is fixed componentwise by HEq; its choice is therefore
of determined data, just as the recorded AmbientDualityPairing's own witness.

H11: rechecked every hypothesis, all three conclusion clauses, both signed symmetry
changes, and the zero, empty, identity and positive-level cases against the literal
Lean definitions, not just their names. The source is the current blueprint's second
proof paragraph and the current node's expanded steps 1--6. The repaired proof docstring
follows those six steps, including the explicit inverse and the naturality computation.


## Saved-packet repair self-check

The current item module contains all fourteen recorded declarations. The removed
BoundaryAlphaCanonical and BoundaryAlphaMaps files are retained only under scratch/,
outside the delivered Lean tree, for diagnostic history. No True predicate, opaque
conclusion, arbitrary category/functor/evaluation parameter, or existence-only symmetry
choice appears in the delivered item. boundarySigma uses the normalized witness of
etaleKoszulSymmetry, whose HEq condition fixes every hom to the actual Koszul braiding.
The conclusion is written out as IsIso, the independent Equiv equality for all tests,
and the naturality square. Every postponed theorem has a source and proof docstring.
The three proof-source imports are reachable through the original dependency closure;
RingedInternalHomExactRestriction and RhomGlobalSections are also imported directly
for the stated proof plan. All node changes are lean-only, so no statement_change or
citer correction is needed.

Refreshed searches in this repair session: leanfinder query "evaluation normalized
costalk duality comparison via tensor Hom projection formula" returned eight generic
smooth-sheaf evaluation facts; loogle query "CategoryTheory.Adjunction.homEquiv"
returned twelve generic adjunction facts; Mathlib grep "expComparison|rightAdjointProjectionMap"
in CategoryTheory returned five exponential-comparison hits, whose Cartesian
hypotheses do not fit derived module tensor. The source/project rg search for
boundaryAlpha found no exact declaration; the source tensor-symmetry search found
nonempty_iso_derivedTensor_flip, which gives no component normalization and hence
cannot replace the normalized pairing interface.


Compiler diagnosis and repair: a bounded diagnostic with #check after each helper
located the sole deterministic kernel timeout at boundarySigma; subsequent helper
and theorem elaboration completed once that rejected constant was abstracted by the
error recovery. The cost was the large inline HEq predicate passed implicitly to
Classical.choose. Added IsEtaleKoszulSymmetry in the pairing dependency to name
exactly that predicate, and made etaleKoszulSymmetry refer to it. Its body is the
original componentwise HEq to DerivedMonoidal.braiding, unchanged. No hypothesis,
object, normalization, or coefficient universe changes. This retains a real, uniquely
determined symmetry construction and keeps all item helpers in one module. The
profile, bounded heartbeats and #check commands stay exclusively in scratch/.


## Validation

The final prescribed scompile.py command compiled all three delivered files together
successfully (exit 0), with no error or non-sorry warning. Each file passed its
sandbox and actual-library checks. The reported actual-library elapsed times,
including wrapper bookkeeping/slot wait, were 11.5 seconds for the generic internal
Hom module, 27.6 seconds for Pairing, and 28.6 seconds for the item. The item therefore
validates both repaired dependency interfaces as an actual consumer. No global build,
increased file timeout, diagnostic option, extra agent, or direct shared-repository
write was used.

Final second reading of the compiled files confirms: boundaryCTF/True and
boundaryAlphaConclusion/opaque are absent; the theorem visibly contains all original
membership assumptions, canonical projection hypothesis, IsIso clause, independent
Hom-chain postcomposition clause and naturality equation. IsEtaleKoszulSymmetry is
literally the original HEq normalization, so extracting the symmetry determines the
same map as the pairing dependency. No proof was filled: the item theorem and the
standalone symmetry theorem remain sorry, as required for stage 2.


The dry-run import probe required the generic Hom defining module to expose both the
generic and ordinary-etale declarations; preflight also required the primary declaration
in its defining file. The final minimal public-import repair satisfies both checks,
retaining the full generic construction and all its comparison statements. The live
finiteTorConstructibleEtale declaration is a def (without noncomputable); its
existing-declaration signature record was aligned with that live source.
