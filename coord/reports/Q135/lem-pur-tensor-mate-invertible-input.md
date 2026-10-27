## Worker report

The module Sheaf.Paper.TensorMateInvertibleInput states the canonical counit-defined
exceptional tensor mate theorem, with its naturality equation. The theorem is
AlgebraicGeometry.ProEtale.tensorMate_invertibleInput; its whole proof is sorry.
Four concrete helper definitions provide its canonical source, target, symmetry
and component. They belong to this same node, and all have real data.
No node statement, dependency or proof plan was changed.

Hypothesis and clause correspondence:

- The finite coefficient setting is S : WeilConjectures.PurityFiniteSetting.{u}.
  Its field and coefficients package p, a, q, the fixed algebraic closures, ell
  prime distinct from p, the actual finite subextension E, and positive level.
  S.Coefficient is the standard ULift of O_E/(varpi_E^n). No divisibility of the
  level by a ramification index is required.
- X and Y are Scheme.{u}, with Over (Spec (.of S.field.k)); local finite type
  and quasi-compactness of each structure morphism say finite type over k.
  Neither structure morphism is assumed separated.
- f : X ⟶ Y has IsOver for the same base, IsSeparated f, LocallyOfFiniteType f,
  and QuasiCompact f: exactly a separated finite-type k-morphism.
- K is an arbitrary etale representative. hK applies the recorded pro-etale
  constructibleFiniteTor predicate to its comparisonUpperStar image: bounded
  constructible of finite Tor amplitude on the small pro-etale site.
- hKi is finiteComparedInvertibilityClause S Y on that image. It explicitly
  requires an inverse in the SAME pro-etale Dctf category, with BOTH tensor
  inverse isomorphisms to the coefficient unit. It is not invertibility with
  an arbitrary ambient inverse.
- The canonical arrow is invertibleInputTensorMate S.Coefficient f K. Its source functor
  is etale derived pullback, tensor on the right with etale omega_f, then
  comparisonUpperStar. Its target is the etale exceptional inverse image,
  then comparisonUpperStar. These are precisely the comparison coordinates
  already used by def-pur-co-smoothness. Every pro-etale Dctf input has an
  etale origin; comparison is fully faithful on these origins, so all their
  morphisms are included. The canonical tensor, pullback and unit comparisons
  identify these endpoints with Lf^*K tensor omega_f and G_f K.
- The component applies comparisonUpperStar.mapDerivedCategory.map to the
  canonical Koszul symmetry followed by Etale.dualizingComplexTensorMap.
  The latter is explicitly the projection-formula inverse/counit transpose,
  followed by the left unitor. Hence the helper uses the specified theta
  in pullback-first source order, with no arbitrary endpoint isomorphism.
  invertibleInputTensorSymmetry specializes the published derivedBraidedCategory,
  whose construction descends the Koszul symmetry; it chooses no braiding.
- The first conjunct is IsIso of this actual component, not Nonempty of an
  abstract isomorphism. The second conjunct quantifies every L satisfying
  the same Dctf and two-sided invertibility conditions and EVERY a : K ⟶ L.
  Its equation is theta_L after (H(a) tensor identity_omega) equals G(a)
  after theta_K, expressed using the two explicit source/target functors.
- There is no cohomological smoothness or dualizing base-change assumption.
  beta is only contextual notation in the node; it is not an additional
  conclusion. The canonical compactification is constructed by the existing
  finiteComparedCompactification; no compactification choice is assumed.

Dependencies read and used:

- Sheaf.Paper.PurityFiniteSetting: WeilConjectures.PurityFiniteSetting,
  Coefficient and its existing ring structure.
- Sheaf.Paper.FiniteTorAmplitudeSites (publicly imports the recorded native
  TorAmplitude module): AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor.
- Sheaf.Paper.DerivedPullbackTensorHom: finiteDerivedPullback and
  finiteIntrinsicDerivedTensor provide the recorded intrinsic model; the
  statement uses the published fixed-ModuleCat comparison presentation
  already used by its cohomological-smoothness dependency, rather than
  declaring alternative operations.
- Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients: the recorded
  transported constructible exceptional interface. The target in comparison
  coordinates is nu_X^* of the ordinary etale right adjoint, with the same
  unit normalization as the recorded finiteComparedDualizing.
- Sheaf.Paper.CohomologicalSmoothnessFiniteComparison:
  finiteComparedCompactification, finiteComparedInvertibilityClause,
  finiteComparedDualizing and finiteComparedTensorClause.
- Its public upstream UpperShriekCanonicalMaps supplies
  Etale.dualizingComplexTensorMap; Dualizing supplies
  Etale.derivedBraidedCategory. Etale.upperStar.leftDerivedFunctor and
  Etale.rightDerivedUpperShriek are fully qualified to avoid the similarly
  named pro-etale notation.
- Proof-only imports are FiniteCoefficientTensorCtf, DerivedPullbackTensorIso,
  CompactSupportProjectionFormula and Mathlib.CategoryTheory.Equivalence.
  For lem-sf-quasi-inverse-hom-bijection, the recorded Mathlib match is
  Equivalence.fullyFaithfulFunctor with FullyFaithful.map_bijective;
  Equivalence.mk adjusts the unit, without imposing triangle equations on
  the originally supplied quasi-inverse isomorphisms.
- lem-pur-all-stage-ctf-pullback-unit has no Lean record or Mathlib match;
  it is a proof-only dependency and its import is therefore omitted. Its
  finite-level pullback and unit role is retained in the proof docstring.

Edge cases checked before writing: the identity morphism and coefficient unit
are included; arbitrary positive coefficient levels, including level one and
levels not divisible by the ramification index, are included. Empty source and
empty target schemes require no nonemptiness, dimension maximum or chosen chart.
No absolute separatedness is added. All invertible shifts/lines are allowed,
with Koszul rather than sign-free symmetry. Naturality includes zero and arbitrary
noninvertible morphisms between invertible objects, not just isomorphisms.
The site retains object universe u+1 and morphism universe u, and coefficients
and ModuleCat live in u+1 as in the recorded definition. No independent small
coefficient/site universe or extra universe equality is imposed.

Searches for an existing complete statement:

- msearch.py leanfinder, query "Canonical exceptional tensor mate on an invertible
  complex is an isomorphism": eight hits including exactPairingCongrLeft,
  tensorRightHomEquiv and a reflective-monoidal instance. None is this
  pro-etale Dctf canonical mate with its naturality conclusion.
- msearch.py loogle, query '"projectionTensorMap"': zero hits.
- msearch.py grep, query projectionTensorMap|dualizingComplexTensorMap under
  Mathlib CategoryTheory: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for tensor mate, tensor invertibility,
  dualizingComplexTensorMap, and the item id. The item id has no upstream hit.
  UpperShriekCanonicalMapsCoherence.isIso_rightDerivedUpperShriekTensorMap_of_isInvertible
  is a related generic etale result. It does not itself state the node's finite
  setting, pro-etale Dctf inverse, pullback-first canonical component and
  naturality clause, so it is not an exact existing binding for the full node.
  The definition of the component is reused from UpperShriekCanonicalMaps.

No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q135

The dispatcher explicitly prohibits starting other agents. This is a separate
self-reading of the node and final file, not a claim of an independent agent's
review; the maintainer supplies the independent review.

I checked the finite setting, both schemes' finite-type structure maps, the
k-morphism condition, separated finite-type arrow, Dctf membership and the
inverse's Dctf membership against the original node. Section-variable inference
would omit hypotheses unused in the constructions, so the main theorem binds
ALL scheme and morphism hypotheses explicitly. I also checked both tensor inverse
clauses, the actual canonical arrow, and naturality for arbitrary morphisms.
The source order is corrected by the canonical derived symmetry before the
published counit transpose. The symmetry helper is generic in the coefficient
category to avoid an expensive comparison of two concrete monoidal elaborations;
its actual construction remains the published Koszul braiding. No abstract
isomorphism replaces the arrow. No smoothness/base-change condition, absolute
separatedness, nonempty assumption, or coefficient-level restriction was added.

## Validation

scompile.py Q135 lem-pur-tensor-mate-invertible-input
lean/Sheaf/Paper/TensorMateInvertibleInput.lean passed both its sandbox compile
(4.7 s) and library-module compile (4.6 s), without errors or warnings.
The final source preserves every main theorem hypothesis explicitly. The map
helpers are generic in the finite ring, with a HasCompactification instance;
the theorem supplies that instance from the existing canonical compactification.
This avoids the elaboration timeout caused by specializing the constructions to
the bundled setting too early. The Koszul symmetry is concrete published data,
not a choice from a Nonempty isomorphism. No timeout limit was changed.
The final module contains one sorry, the entire proof of the named theorem.

The required deliver2.py --no-push dry run passed: commit 9d1d6e24d79
compiles and passes the server preflight. Nothing was pushed by the dry run.
