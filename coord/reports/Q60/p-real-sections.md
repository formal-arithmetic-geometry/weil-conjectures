## Worker report

Repair of immutable returned head c85cef32788f, H3. The required initial saved-packet
dry run passed as f1b3461f6c. That mechanical pass did not resolve H3: the old theorem
used pro-etale WeilSheaf, pro-etale sections, and pro-etale monodromy without a
comparison to the node's etale adic category. This delivery replaces those inputs
with the actual etale adic category throughout and repairs both affected dependency
interfaces in the same packet. It does not assert an unconstructed site comparison.
The natural statement and proof of p-real-sections are unchanged.

The main module Sheaf.Paper.RealSheafSections states
AlgebraicGeometry.WeilGroup.ordinarySections_eq_geometricInvariants. The representation
is now Scheme.etaleFundamentalRep, its fibre is Scheme.lisseAlgebraicFiber, and its
source is Scheme.etaleAlgebraicSectionsAt. All three use the integral systems,
rational models and coefficient localization of the recorded def-pod definition.
There are no representation-defined sections. Each postponed theorem has a source,
blueprint tag and proof plan; definitions have explicit data or uniquely normalized
maps, with separate named existence theorems.

Hypothesis and clause correspondence:

* The standing finite field is K with Field and Finite. l is prime and different
  from ringChar K. Q is a specified algebraic closure of the l-adic field, with
  IsAlgClosure. Its universe u+1 is the universe required by the existing etale
  coefficient category; the fixed PadicAlgCl is covered by its canonical ULift.
  No topology is arbitrarily imposed on Q: continuity in the repaired dictionary
  is the recorded finite coefficient-field predicate Representation.IsLAdic.
* C and U are arithmetic schemes over Spec K. IsCurve C, relative smooth dimension
  one and GeometricallyConnected give exactly the chapter's smooth separated
  finite-type geometrically connected curve. IsCurve U is the inherited open-curve
  interface used by the existing WeilGroup API. There is no properness assumption.
* j is an open immersion over Spec K and Nonempty U is exactly nonempty U_0.
  sectionsGeometricOpen j is its actual base-changed etale object on the geometric
  curve. The curve's Noetherianity, separatedness and invertibility of l are
  consequences supplied by sectionsGeometricCurve_properties and its instances;
  they are not additional hypotheses in the main theorem.
* W, WU and R : Restriction j WU W are the recorded Weil groups and actual finite
  etale restriction. The target uses R.restrict and WU.geometric.subtype. Thus the
  subgroup acting is precisely the geometric subgroup of W(U_0), not all of W(U_0).
* B and D are the existing coefficient-free geometric base point, finite-fibre
  Frobenius path and homotopy-exact-sequence data. D.toEtale reuses D.geomEquiv,
  B.frobPath and D.geomEquiv_conj without choosing another group map or lift.
* F is EtaleLisseWeilSheaf: an IsoAlgebra for the recorded
  lisseAlgebraicAutomorphismPullback along geometric Galois Frobenius. Its carrier
  is literally LisseAlgebraicSheaf on the etale site. Its invertible structure map
  is the actual etale adic descent datum. No stable integral lattice for Frobenius
  is requested; this map lives in the rational/coefficient-localized category.
* t is any geometric point of the nonempty open with values in AlgebraicClosure K.
  tau is any finite-etale fibre path from its image to B.t. The representation fibre
  and both evaluation clauses use the actual etale adic stalk at B.t. The source's
  geometric generic stalk is identified by the same normalized base-point transport.
* The source of e is inverse limit of sections of F's integral model on the actual
  etale open, then E tensor over O_E, then Q tensor over E. These are ordinary
  etale adic sections in precisely the convention in proof Step 3. There is no
  condition of preserving the Weil structure on a section.
* The target is Mathlib Representation.invariants of the restriction of the actual
  etaleFundamentalRep to WU.geometric. It is exactly the vectors fixed by every
  geometric element, as in def-real-weil-representation-operations.
* e is a Q-linear equivalence. Its first equation specifies evaluation followed by
  tau transport. etaleIntegralEvaluation is fixed by every finite-level germ
  projection. etaleAlgebraicEvaluation is its two actual scalar extensions.
* The final equation intertwines etaleSectionsFrobenius with rho(D.frobLift).
  The former is uniquely specified on every geometric stalk by pullback followed
  by F.str, using the recorded pullback-fibre iso. This fixes the actual residual
  action; it is not an arbitrary automorphism chosen to make equivariance true.
  sectionsGeometricOpen_stable supplies the arithmetic open's Frobenius stability.

Dependencies used, with declarations and modules:

* def-wf-fundamental-representation: repaired in
  Sheaf.Paper.EtaleWeilFundamentalRepresentation, main declaration
  AlgebraicGeometry.Scheme.etaleFundamentalRep. The finite germ normalization,
  inverse-limit extension, rational and algebraic transports, geometric action,
  Weil descent operator, uniquely determined extension, continuity, lift-change
  equality and change-of-base-point intertwining are all listed in lean.
  The general EtaleWeilDegreeData construction is independent of dimension.
* prop-wf-weil-sheaf-representation-equivalence: repaired in
  Sheaf.Paper.EtaleWeilSheafEquivalence, theorem
  AlgebraicGeometry.Scheme.etaleWeilSheafRepresentationEquivalence. It uses the
  actual etale coefficient-pair source, a target of continuous finite-dimensional
  representations, natural normalization on objects and morphisms to etaleFundamentalRep, exactness in both
  directions, the abelian structures, and tensor compatibility with the recorded
  underlying tensor and unit.
* def-wf-weil-group: upstream
  WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup, the recorded
  constantCover/arithmeticFrobenius/constantCoverAction/geometricFrobenius/
  weilGroup/weilGroupDeg declarations. The existing curve WeilGroup and Restriction
  wrappers retain those actual finite-cover data.
* def-real-weil-representation-operations: upstream RealSheaves.LinearAlgebra,
  detLine and semisimplification; its invariants are Mathlib Representation.invariants
  from Mathlib.RepresentationTheory.Invariants, used verbatim.
* def-pod-lisse-l-adic-sheaves: Sheaf.Paper.LisseIntegralSmallCoefficients publicly
  retains LisseAdicSheaves and its LisseIntegralSheaf, LisseRationalSheaf,
  LisseAlgebraicSheaf, lisseAlgebraicPair, lisseCoefficientPairModel and fibres.
* The etale pullback and its finite, integral, rational and algebraic fibre isos are
  the declarations of Sheaf.Paper.LisseAdicAutomorphismPullback. The actual map on
  adic fibres is the recorded lisseAlgebraicFiberFunctor, with its object equality,
  in Sheaf.Paper.LisseAdicFiberFunctors. No private replacement category is used.
* The proof uses Sheaf.Paper.GaloisLisseRepresentations and its finite evaluation
  and adic equivalence clauses. The original geometry, dense-open and algebraic
  proof imports are retained in the main module, including DenseOpenPiOneSurjective.

Edge cases checked:

* Rank zero: the compatible systems, fibres, section spaces and invariants are zero.
* Constant line with Frobenius scalar different from 1: all geometric sections
  survive, with that scalar as Frobenius. No equation F(s)=s is imposed.
* Nontrivial geometric character: sections and geometric invariants both vanish.
* Identity open and arbitrary nonempty proper open are included. Curves may be
  proper or nonproper. Empty opens are excluded exactly by the node.
* Arbitrary etale Weil descent may be rational and need not preserve the chosen
  integral lattice. The section Frobenius construction works over a common finite
  coefficient field before rationalization; no integral stability is silently added.
* The finite path normalization includes disconnected finite covers and torsion
  finite modules, and never assumes a nonzero rank or a free integral model.
* Every universe and variable is explicit; autoImplicit is disabled. Site and
  coefficient universes are those of the existing etale adic definitions.

Searches and sources checked:

* The saved packet's leanfinder query about global sections and geometric invariants
  gave only general Galois fibre results; loogle on Representation.invariants and
  CategoryTheory.Sheaf gave no hits; grep for globalSections/invariants found only
  the representation-defined upstream LocalSystems theorem. Its full source was
  read and it is still not an attachment for ordinary etale adic sections.
* Repair leanfinder query: "Path transport on finite etale sheaf stalks extended to
  lisse adic fibres by inverse limits and scalar extension". Eight unrelated etale
  or spreading-out hits, no path normalization on these adic fibres.
* Repair loogle query: "AlgebraicGeometry.Scheme.lisseAlgebraicFiber,
  Representation.invariants". No hits; the service does not index the side-project
  fibre name. Local source signatures were therefore inspected directly.
* Repair LeanSearch query: "Geometric fundamental representation on actual etale
  lisse adic sheaf fibres and global sections as geometric invariants". Eight general
  global-sections hits; no theorem about these adic fibres and invariants.
* rg in Mathlib, upstream WeilConjectures and shared lean/Sheaf for etaleFinitePathIso,
  etaleAlgebraicPath, etaleFundamentalRep, etaleAlgebraicSectionsAt and
  etaleWeilSheafRepresentationEquivalence found no existing declarations.
* Opened LisseAdicSheaves, LisseAdicFiberFunctors, LisseAdicAutomorphismPullback,
  GaloisLisseRepresentations and FundamentalGroup.LocallyConstantEquivalence;
  the last's finite-cover representability and fibre description justify precisely
  why finite-cover germs determine the new path map. Reused all existing objects.
* Reread the current main-20261015 p-real-sections node and unit, the equivalence
  source, the fundamental-representation source, and all four statement dependencies.

No STATEMENT-DISPUTED or natural-language statement correction is needed.

## Dependency modules

`def-wf-fundamental-representation`: the old recorded fundamentalRep accepts a
pro-etale WeilSheaf and pro-etale LisseMonodromy and returns an action on a pro-etale
stalk. Those are not the etale adic objects specified by the dependency. Its repaired
module provides the same construction on actual etale adic fibres. The generic
construction takes the coefficient-free degree datum and its geometric finite-path
conjugation rule and specifies the representation uniquely by its geometric action
and degree-one operator. The curve adapter uses the existing B and D. In particular
the repair does not replace the source's general notion by a curve-only definition.

`prop-wf-weil-sheaf-representation-equivalence`: the closed upstream audit was
about the pro-etale source category. Its repaired theorem states the exact tensor
correspondence for the actual etale adic IsoAlgebra source and records normalization
to the repaired representation. Exactness is preservation of finite limits and
colimits in both directions; this also retains both directions of the source's
subobject, quotient and subquotient correspondence. The tensor predicate fixes the
underlying etale tensor and unit, and requires monoidal forgetful functors on both
sides and a monoidal equivalence. The rest of both dependency JSON files is unchanged.

## Second reading by Q60

The dispatcher prohibits starting other agents. This is my separate source-to-type
rereading; the maintainer supplies the independent reading.

The returned mismatch was real: an ordinary pro-etale section space with an informal
claim of agreement was insufficient. Both dependency interfaces and the consumer
now use actual etale integral systems, rationalized morphisms and coefficient pairs.
The main theorem no longer mentions LisseMonodromy or accepts a pro-etale WeilSheaf.
Its evaluation map is the limit of finite etale germ maps, with both scalar extensions
written out. Finite-level path transport explicitly requires finite underlying stalks; the adic
level theorem derives this from finite generation and uniformizer-power annihilation.
This avoids confusing finitely generated modules with finite sets over an infinite ring.
The repaired monodromy path is fixed on finite-cover germs, preventing
an unspecified stalk isomorphism from replacing the source's finite-fibre action.

Reread each binder against the node: finite field, coefficient prime, smooth
geometrically connected arithmetic curve, nonempty open, Weil restriction and lisse
Weil sheaf are all present. The technical etale-category instances are supplied from
the curve properties rather than assumed. Reread each conclusion: ordinary sections,
geometric subgroup invariants, canonical evaluation and residual Frobenius are all
present. The constant-line nontrivial-Frobenius example confirms that ordinary
sections have not been confused with Weil-fixed sections. No natural statement,
proof route, unit statement or target has been changed.

Validation: scompile.py compiled all three delivered modules in dependency order,
both in their sandbox envelopes and at their library module paths, against the
published library/private overlay. Exit status 0; no errors or warnings. No global
build was run. A structural self-check confirms that only lean changes in each of
the three copied DAG records, all module variables are explicitly bound with
autoImplicit disabled, and recorded signatures are extracted verbatim from the files.
The final delivery dry run is run on this repaired packet before pushing.
