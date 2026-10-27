## Worker report

The module Sheaf.Paper.FiniteCtfRetractEtaleImages states the entire node as
AlgebraicGeometry.ProEtale.finiteCtfRetractEtaleImages, with one named sorry.
finiteCtfComparisonHomologyIso is an actual construction: the existing exact
comparison homology isomorphism followed by homology of the given alpha.
It contains no proof hole and introduces no alternative comparison functor.

Clause-by-clause correspondence:

- X is Scheme.{u}; CompactSpace X and QuasiSeparatedSpace X state precisely qcqs.
- B : Type u, CommRing B, Finite B, TopologicalSpace B and DiscreteTopology B
  state finite discrete commutative coefficients. IsTopologicalRing B is inferred
  from discreteness, rather than added as a redundant hypothesis.
- FiniteDiscreteOrdinary.coefficient B is the existing continuous-function
  condensed ring. Internal B X is the module category over its actual p_X pullback.
  The existential E : Encoding B X records exactly its normalized identification
  with the constant ring B_X, and section-action equivalences to ordinary module
  sheaves. E.fixedDerived is the actual termwise unbounded derived equivalence.
  It is conclusion data, not an assumed equivalence or a descent hypothesis.
  ULift.{u+1} B places the same coefficients in the small sites' module universe.
  Scheme/site universes are unchanged; no equality of the object and morphism
  universes of a small site is imposed.
- C and J are in the ambient unbounded DerivedCategory (Internal B X). hC is
  exactly bounded finite-constant-model constructibility and finite Tor amplitude.
  i : J -> C, r : C -> J, hri : i ≫ r = identity J is r composed with i = 1_J.
  There is no prior boundedness or descent assumption on J or either arrow.
- C₀ belongs to the ordinary unbounded derived category of etale B-module sheaves;
  isBoundedConstructible gives D^b_c and the following existential ordered Tor
  interval gives finite Tor amplitude. The existential alpha identifies the
  actual comparison inverse image of C₀ with C in the specified ordinary coordinates.
- For every integer q, e is an endomorphism of H^q(C₀). e ≫ e = e is idempotence.
  The comparison-map equation conjugates the pullback of e to H^q(r) ≫ H^q(i),
  which is the source's H^q(i) composed with H^q(r). Its conjugating isomorphism
  is finiteCtfComparisonHomologyIso, not an arbitrary cohomology identification.
  The universal e' clause gives uniqueness among exactly the idempotents with
  this comparison image.
- Scheme.IsConstructibleEtaleModuleSheaf (image e) states constructibility of the
  actual categorical image I_q. The ensuing Nonempty is an isomorphism
  H^q(E(J)) ≅ comparisonUpperStar(I_q), retaining the B-module action.
- The next conjunct uses the recorded IsConstantModelConstructible on every
  H^q(J). Thus the pulled-back image sheaves are constructible in the required
  finite-constant-model sense, with the identification to H^q(J) just stated.
- For all integers a,b, vanishing of H^q(C) outside [a,b] implies identical
  vanishing of H^q(J). This includes empty intervals.
- For every ordered a,b, the recorded DerivedCategory.torAmplitudeIn for C
  implies the same interval for J, testing all modules in degree zero.
- The final intersection predicate says J belongs to exactly the recorded Dctf.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.Topology.Defs.Filter: CompactSpace (no separation axiom).
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated: QuasiSeparated and its
  quasiSeparatedSpace characterization; QuasiSeparatedSpace X is the scheme form.
- Sheaf.Topology.ProfiniteCondensedRing: Profinite.CondensedRing, reexporting the
  actual continuous coefficient construction used by coefficient B.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic: coefficientRing,
  coefficientRing_X and condensedRingObj (the p_X inverse-image ring object).
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and Scheme.ProEt.topology.
- Mathlib.AlgebraicGeometry.Sites.Etale: Scheme.smallEtaleTopology.
- Sheaf.AlgebraicGeometry.ProEtaleSiteComparison: proEtaleSiteComparison and
  proEtaleSiteComparisonModules; the latter is the existing comparisonAdjunction
  for the same comparisonUpperStar used by the statement.
- Sheaf.CategoryTheory.RingedSiteModules: ringedSiteModules, the transparent
  general-site SheafOfModules presentation of ordinary module sheaves. The finite
  coefficient encoding already supplies its fixed-ModuleCat presentation.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory,
  HasDerivedCategory and Q; derived cohomology is DerivedCategory.homologyFunctor.
- Sheaf.Paper.ConstantModelTorAmplitude, public-importing
  Sheaf.Paper.CondensedConstantConstructibility: constantModelBoundedConstructible,
  IsConstantModelConstructible and ConstantModelConstructibleFiniteTor; generic
  DerivedCategory.torAmplitudeIn and finiteTorAmplitude are the recorded tensor tests.
- WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf:
  Scheme.IsConstructibleEtaleModuleSheaf, using constructible Scheme.Stratification
  and finite locally constant module values.
- Sheaf.Paper.FiniteDiscreteOrdinaryEncoding: coefficient, Internal, Encoding,
  Encoding.fixedDerived, owned by def-pe-finite-discrete-presentation-encoding.
  Its canonical constant-section ring
  normalization fixes the identification of coefficients and both forward functors.
- WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes:
  Etale.DerivedCategory.isBoundedConstructible, with the preceding constructibility.
- Sheaf.AlgebraicGeometry.EtaleTorAmplitude and its upstream coefficient import:
  Etale.DerivedCategory.hasTorAmplitudeIn.
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor:
  Functor.mapDerivedCategoryHomologyFunctorIso, read in its full signature.

The three additional stmt_deps are existing landed nodes owning the normalized
encoding, etale bounded constructibility, and etale Tor amplitude. No new node,
dependency repair, or mathematical statement correction is needed. All eight
recorded proof dependencies are imported; the Mathlib leaf
lem-sp-exact-functor-preserves-homology is imported by its matched module.
The theorem docstring carries the five proof steps and their exact dependency ids.

Edge cases checked before writing: empty X (zero sheaves and the empty finite
stratification); the zero ring (no Nontrivial binder); C=0 and its necessarily zero
retract; J=0 (zero projector); J=C with identity maps (identity projector); all q,
including outside the support; singleton and empty cohomological intervals; and
ordered Tor intervals a=b. Idempotents are lifted on sheaves only: the statement
does not infer full faithfulness of the unbounded derived comparison. The image
argument uses kernels between constructible sheaves, not arbitrary subobjects.

Searches made on 2026-10-24:

- msearch.py leanfinder: "A retract of a finite coefficient constructible derived
  proetale complex has cohomology given by etale images of idempotents". Eight
  results about etale rings and algebras; no matching statement.
- msearch.py loogle: '"constructible", "retract"'. Zero results.
- msearch.py grep: '[Cc]onstructible.*([Rr]etract|[Ii]dempoten)|([Rr]etract|[Ii]dempoten).*[Cc]onstructible'.
  Zero Mathlib results.
- msearch.py leansearch: "A retract of a constructible derived complex over a
  finite ring has constructible cohomology as the images of etale idempotents".
  Eight results, including Module.Flat.of_retract and generic Retract.map and
  quasi-isomorphism retract lemmas; none gives etale constructible images.
- rg over lean/WeilConjectures and lean/Sheaf for the item id and combinations of
  retract, finite, idempotent and constructible found only related finite-flat
  retract results and coefficient-encoding infrastructure. No exact theorem exists.
  Further targeted source searches found and reused FiniteDiscreteOrdinary.Encoding,
  its fixedDerived equivalence and the exact-functor cohomology isomorphism.

No mathematical statement fault or STATEMENT-DISPUTED flag was found.
The returned H2 dependency ownership fault is repaired below.

## Second reading by Q155

Re-read the JSON and final Lean side by side. Checked especially the direction
of the retraction (i ≫ r), the opposite composite on C (r ≫ i), the direction
of the exact cohomology isomorphism, uniqueness only among idempotents with the
specified comparison image, and use of image e rather than an arbitrary subobject.
Removed the redundant IsTopologicalRing hypothesis, inferred from discreteness.
The encoding is a normalized existential witness in the conclusion. Every named
object and every vanishing assertion refers to that same encoding. All source
clauses are present. This is a worker self-audit; the maintainer performs the
independent review prescribed by the dispatcher brief.

Validation: the final module passed server compilation and maintainer preflight
through deliver2.py --no-push (OK dry run, 542d196f47b), with no remaining compiler
or style diagnostic. Earlier whitespace/line-length warnings were repaired.

## Repair of return H2 (2026-10-25)

The independent review of immutable delivery head 9e7f5e738501 found one
dependency ownership fault. Replaced lem-sf-finite-discrete-normalized-encoding
in stmt_deps with def-pe-finite-discrete-presentation-encoding, the existing
reviewed Q05 definition node. Read that node and the full source definitions of
coefficient, Internal, Encoding and Encoding.fixedDerived in its recorded module,
Sheaf.Paper.FiniteDiscreteOrdinaryEncoding. These are exactly the supplied-data
definitions used in this statement. encoding_exists is an existence theorem:
E is existential in the conclusion, so that theorem is not a statement dependency.
No theorem dependency is introduced into stmt_deps.

Compared the retained delivery node against current main: all fields outside
lean and stmt_deps coincide. The delivery wrapper rebases the repaired record
on current main. The original two other added definition dependencies are retained.
No statement, proof, proof_deps, signature, import or Lean file content changes.
The Lean SHA256 before and after repair is
9f20061b0c4cdeaf57b17da479eefac4037fa8b8f1d19bde6272b9cd1dcac74e.
The reviewer accepted every mathematical clause; the repair is precisely the
requested definition-owner substitution.
