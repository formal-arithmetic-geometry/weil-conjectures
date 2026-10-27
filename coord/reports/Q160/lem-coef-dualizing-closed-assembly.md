## Worker report

Item: lem-coef-dualizing-closed-assembly. Module:
Sheaf.SixFunctors.CoefficientDualizingClosedAssembly.
The only postponed theorem is WeilConjectures.coefficientDualizingClosedAssembly.
The definition CoefficientDualizingClosedAssembly assembles its full assertion from
published ordinary small-etale functors, adjunctions and canonical coefficient maps.
There is no new independent mathematical notion and no statement correction.

Hypotheses and clauses, checked against the node:

- The global field k, its characteristic and algebraic closure are D : FiniteFieldDatum;
  l with Fact l.Prime and _hl : l ≠ D.p supplies the distinct coefficient prime.
  E, Field E, Algebra (Padic l) E and FiniteDimensional (Padic l) E give the finite
  extension. Padic.coefficientExtensionRing uses its recorded valuation ring and
  uniformizer. Positive node levels m,n are indexed in Lean by m+1,n+1, with hmn;
  every pair 1 ≤ m ≤ n is represented, including m=n and level 1.
- A and B are precisely ULift of those quotient rings, in the established coefficient
  universe u+1. RingHom.ulift of Ideal.Quotient.factor is their actual reduction map.
  The explicit finite-instance arguments are proofs of finiteness, not extra assumptions.
- Y, IsAffine Y, aY, IsSeparated aY, LocallyOfFiniteType aY and QuasiCompact aY give
  the affine separated finite-type k-scheme. The target of i is precisely affine
  r-space over Spec k, indexed by ULift (Fin r), including r=0. IsClosedImmersion i
  and _hi say it is the stated closed k-embedding. The compactification c fixes the
  canonical ordinary compact-support candidate for p:P→Spec k; any c is permitted.
- FA/FB in the assertion are rightDerivedLowerShriekOfCompactification; JA/JB are
  rightDerivedLowerStar along i; T is Etale.scalarExtension. All categories are
  Etale.DerivedCategoryModule on the small etale sites, not pro-etale categories.
- GA,GB,IA,IB and adjPA,adjPB,adjIA,adjIB range over presentations of their specified
  right adjoints. They are not unconstrained functors: the exact geometric left functors
  and the four adjunction types constrain them. The node explicitly works under
  counit-compatible structural identifications, so adjYA=adjIA.comp adjPA and
  adjYB=adjIB.comp adjPB implement these identifications directly. No structural
  comparison or counit compatibility is silently assumed of an arbitrary isomorphism.
- M=GA(oneA), N=IA(M), MB=GB(oneB), NB=IB(MB) are exactly the four named dualizing
  objects under those identifications. The eight implications require separately for
  each object DerivedCategory.isBoundedConstructible and an interval a≤b with
  hasTorAmplitudeIn. The latter tests every degree-zero module sheaf. There is no
  hypothesis on boundedness, constructibility or Tor amplitude of JA(N).
- epsPA/epsPB and epsYA/epsYB are the actual counit components of the named
  adjunctions at Etale.constantComplex. The scalar unit is the canonical normalized
  ExceptionalCoefficients.unitIso, realizing T_s A_s≅B_s.
- d is finiteCoefficientDirectImageMap at N. h and t are the actual ordinary-etale
  ExceptionalCoefficients.compactSupportMap at JA(N) and M. cY=h≫FB.map d is the node's normalized
  compact-support composition. Its use is precisely under the structural identifications
  stipulated in the node. The initial existential witnesses hd,ht,hcY make only these
  three canonical components invertible; no inverse of h occurs.
- uP is quantified with the node's defining counit equation and IsIso uP. That equation
  uniquely determines it by adjPB.homEquiv; quantification retains the actual map,
  rather than replacing the canonical map by an arbitrary invertible map.
- b is quantified with IsIso b and the exact required closed counit equation:
  JB.map b≫adjIB.counit = inv d≫T_P(adjIA.counit). This uniquely fixes the arrow
  by adjIB.homEquiv, so it is precisely the assumed closed comparison.
- uY is defined as adjYB.homEquiv applied to inv cY≫T_s(epsYA)≫unit. It is the
  unique map with the node's defining counit equation, without a theorem-hole choice.
- The three conclusions are uY=b≫IB.map uP, IsIso uY, and the normalized transpose
  identity cY≫(JB⋙FB).map(b≫IB.map uP)≫epsYB=T_s(epsYA)≫unit. Lean composition
  order is left to right, the reverse of the node's right-to-left composition notation.

Dependency declarations read and used:

- Sheaf.Paper.FiniteFieldFiber: WeilConjectures.FiniteFieldDatum.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  Padic.finite_coefficientExtensionRing; quotient data come from CoefficientExtension.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  AlgebraicGeometry.LocallyOfFiniteType, QuasiCompact.
- Mathlib.AlgebraicGeometry.Morphisms.Proper/Separated:
  AlgebraicGeometry.IsSeparated (the node uses separatedness, not properness of aY).
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek:
  AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification.
- WeilConjectures.SixFunctors.Etale.Derived.Tensor and Coefficients:
  derivedTensor, DerivedCategoryModule, constantComplex, hasTorAmplitudeIn.
- Sheaf.AlgebraicGeometry.EtaleTorAmplitude reexports hasTorAmplitudeIn, rather than
  making a second bounded Tor predicate.
- WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes:
  Etale.DerivedCategory.isBoundedConstructible (finite-value constructibility).
- WeilConjectures.AlgebraicGeometry.DerivedCategories supplies the recorded ordinary
  derived-category presentation; no alternate derived-category instance is chosen.
- Mathlib.CategoryTheory.Adjunction.Basic: Adjunction.comp, comp_counit_app,
  comp_homEquiv and homEquiv; the latter defines the actual adjunct.
- Sheaf.Paper.FiniteCoefficientDirectImage: Etale.finiteCoefficientDirectImageMap
  and its counit characterization, together with rightDerivedLowerStar.
- Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint:
  isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion establishes the closed
  adjoint existence; the assertion quantifies all presentations of this adjunction.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint:
  isLeftAdjoint_rightDerivedLowerShriekOfCompactification establishes ambient adjoint
  existence; again all presentations with that left functor are covered.
- Sheaf.Paper.EtaleCompactSupportCoefficientChange:
  compactSupportCoefficientComparisonPlus and CoefficientTensorModel were read.
  The unbounded canonical coefficient component needed at the intermediate input
  is ExceptionalCoefficients.compactSupportMap from
  Sheaf.Paper.ExceptionalCoefficientMaps, owned by the existing:true definition
  node def-per-exceptional-coefficient-maps, now explicitly in stmt_deps.
  It requires no finite-Tor witness for JA(N).
- Sheaf.Paper.WitnessCompatibility:
  ProEtale.pbcFixedScalarExtension is the published chosen left adjoint to scalar
  restriction. Its owning definition node def-weil-pbc-witness-compatibility is
  in stmt_deps. Etale.scalarExtension, reexported by the existing imports, is a
  plain abbreviation for this exact functor; OrdinaryDerivedChangeOfRings is not
  used, so lem-pur-derived-change-of-rings is removed from stmt_deps.
- Sheaf.Paper.ExceptionalCoefficientMaps: ExceptionalCoefficients.unitIso supplies
  the canonical scalar unit normalized by multiplication on representatives,
  owned by def-pur-exceptional-coefficient-normalizations, retained in stmt_deps.

Edge cases: empty Y gives the zero derived category and its unique maps; r=0 is
allowed by Fin r; m=n is the identity reduction; m=0 in Lean means level 1, never
zero coefficients. Nonflat reductions are allowed; no tensor-exactness assumption
or finite-Tor claim about i_*N occurs. Scheme objects remain in universe u, etale
site objects in u+1, and coefficients/modules in u+1. No universe equality imposed.

Searches for an existing statement:

- msearch.py leanfinder, query "coefficient reduction of dualizing objects for a
  closed immersion and affine space is composite of closed shriek comparison and
  dualizing coefficient map": eight hits, affine-space map identities, no match.
- msearch.py loogle, "CategoryTheory.Adjunction.comp, CategoryTheory.Adjunction.homEquiv":
  comp_homEquiv, the generic adjunction composition fact, not this geometric statement.
- msearch.py leansearch, "dualizing coefficient comparison composite adjunction
  closed immersion compact support": eight unrelated support/adjunction hits, no match.
- msearch.py grep, "dualizing.*(coefficient|closed)|coefficient.*dualizing" in
  Mathlib CategoryTheory: zero hits.
- rg over lean/WeilConjectures and lean/Sheaf for the node id, closedAssembly,
  closed_assembly and dualizing.*assembly: no statement. Sibling FiniteDualizing,
  CoefficientDualizingClosedDescent and CoefficientDualizingOpenAdjoint were read;
  the first constructs global maps but does not state this closed assembly equality,
  the second supplies b, and the third concerns open restriction. Reusing their
  generic underlying interfaces avoids a duplicate definition of any operation.
- rg in dag/lean_names_upstream.json for closedAssembly/ClosedAssembly: no match.

Validation: scompile.py compiled the delivered module in module mode, sandbox and
library passes, exit 0, no diagnostics. The theorem proof is exactly sorry; all
definition data are explicit. No STATEMENT-DISPUTED issue found.

## Second reading by Q160

Reopened the complete node and generated module after compilation. Checked the
four coefficient/dualizing objects separately, and expanded the assertion's local
aliases to verify their sites and coefficient actions. M and MB live on affine space;
N and NB are their closed exceptional pullbacks, exactly as required under the
structural identification. All four bounded-constructible and all four Tor-interval
conditions are retained. The comparison direction is d:T_P i_*N→i_*T_Y N;
the closed counit equation uses inv d, while cY=h≫F_B(d) goes forward.
The equality conclusion is b then I_B(uP), not its inverse, and the final transpose
identity precomposes with cY. The unit comparison occurs on both right-hand
counit expressions, so the coefficient object is B_s throughout. The explicit
existential invertibility witnesses are outside the supplied uP and b hypotheses;
therefore no circular assumption of the desired comparison occurs. Checked again
that no hypothesis on i_*N or preservation of all D+ by scalar extension occurs.
No mismatch or statement correction found. This rereading was performed in this
worker session, following the instruction not to start other agents; the maintainer
performs the independent delivery review.

## Returned delivery repair

F1: replaced the added theorem dependency lem-pur-derived-change-of-rings with
its actual definition owner def-weil-pbc-witness-compatibility. Read the full
pbcFixedScalarExtension definition and the scalarExtension abbreviation: the
latter is exactly the former on W.smallEtaleTopology, with the same universes.
Added the explicit public import of Sheaf.Paper.WitnessCompatibility.

F2: replaced both h and t by Etale.ExceptionalCoefficients.compactSupportMap φ c
at JA.obj N and M, and added its existing definition owner
def-per-exceptional-coefficient-maps to stmt_deps. Removed the direct import of
EtaleProEtaleCoefficientCompatibility. Read the current server source with
scompile.py --source: etaleCoefficientMap_eq_compactScalarMap identifies the old
component with (Etale.compactScalarMap φ c).app, whose app is compactSupportMap.
This confirms equality of the canonical maps; no hypothesis or conclusion changes.
No dependency node record is changed. Also removed the advisory unused private
CompactCoefficientComposition import; its mathematical use remains in the proof
plan docstring and the unchanged DAG proof.

Second reading of the repaired packet in this worker session: h and t still have
sources T_s F_A(J_A N), T_s F_A(M), and targets F_B T_P(J_A N), F_B T_P(M).
Thus cY=h≫FB.map d and every counit equation retain their original types and
meaning. Rechecked the four bounded-constructible conditions and four Tor
intervals, positive levels m+1≤n+1, the closed embedding over k, the explicit
adjunction presentations, all three conclusions, and absence of a Tor assumption
on J_A N. Only interface ownership and equal canonical map expressions changed.
The theorem signature and mathematical node statement are unchanged.
