## Worker report

The delivered module Sheaf.Paper.LisseLatticePotentialKummerTameness states
AlgebraicGeometry.ProEtale.lisseLattice_potential_kummer_tame with sorry.
It follows the current reviewed NF split, without changing its statement or proof.
NF's merged delivery was stage 1: it supplied the eight-step argument and the finite
prime-to-p torsor splitting node, but no Lean statement. The local sandbox contained
only dispatcher marker files when this stage-2 retry began.

The module's helper definitions have actual data. latticeIntegralCondensedRing and
latticeResidualCondensedRing bundle the already recorded continuous-map ring objects
of Padic.coefficientExtensionIntegers and Padic.coefficientExtensionRing at exponent 1.
Their multiplication is exactly continuousMapRingObjOfUniverseMonObj, and their
commutativity instances are existing canonical proofs. latticeResidualCondensedMap
is postcomposition by Ideal.Quotient.mk; latticeRationalCondensedMap is postcomposition
by the valuation-ring subtype inclusion. Both use the existing universe-polymorphic
continuous-map functoriality and its monoid-map theorem. The two module abbreviations
apply the existing Mod.extendScalars to those actual maps after p_X^*. No arbitrary
map, alternative coefficient model, or choice of an unspecified object occurs.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Distinct primes p, ell | Section parameter ell with Fact ell.Prime; theorem parameter p with Fact p.Prime and _hpell : p != ell. |
| A field k of characteristic p | k : Type u, Field k, CharP k p. |
| Finite E/Q_ell with the extended norm topology | E : Type u, NormedField E, NormedAlgebra Q_[ell] E, FiniteDimensional Q_[ell] E. The normed algebra condition fixes the extension of the p-adic norm; it is not an extra restriction on finite extensions. |
| Valuation ring, chosen uniformizer and residual quotient | The recorded Padic.coefficientExtensionIntegers and Padic.coefficientExtensionRing ell E 1; its defining ideal is (span {coefficientExtensionUniformizer ell E})^1. The integral ring has the subspace topology, and the quotient the quotient topology. |
| Pulled continuous-map coefficient rings | The two bundled helpers have exactly Profinite.continuousMapRingObjOfUniverse as their underlying objects. condensedRingObj and (upperStarFromPoint X).mapMon give the existing pulled coefficients. Rational coefficients are the landed normContinuousRing E. |
| Internal module M_0 | M0 : Mod (Sheaf (Scheme.ProEt.topology S) Ab) (condensedRingObj ... S). |
| M_0 lisse finite rank, rank zero allowed | _hM0 : IsLisseCoefficientModule ... M0. The recorded definition uses finiteFree on a pro-etale cover and allows n=0 and variable local ranks. |
| S nonempty connected | ConnectedSpace S includes Nonempty S. |
| S separated finite type over k | S.Over (Spec (.of k)), LocallyOfFiniteType, QuasiCompact and IsSeparated of S's structure map. |
| M = A_E tensor over A_O_E M_0 | latticeRationalModule ell E S M0 is Mod.extendScalars along the actual inclusion transported by p_S^*. |
| One connected finite etale surjection c:H -> S | Existentials H,c followed by ConnectedSpace H, IsFinite c, Etale c, Surjective c. |
| c^*(M_0/varpi M_0) constant | Mod.IsFree of CondensedRing.upperStar for residual coefficients applied to latticeResidualModule. Ordinary scalar extension by O_E -> O_E/(varpi) is exactly this quotient. A constant finite projective fibre is finite free here because the given residual local models are finite free on a connected base. |
| H is chosen before any Y,D,g | The existentials H,c enclose the subsequent universal quantifiers. |
| Every regular separated finite-type k-scheme Y | Universal Y and Y.Over, then LocallyOfFiniteType, QuasiCompact, IsSeparated of its structure map and IsRegularScheme Y. |
| Every reduced SNC D in Y | D : Y.IdealSheafData, IsStrictNormalCrossingsBoundary D, using the existing reduced Cartier boundary definition. |
| W=Y minus D | An arbitrary W and open immersion w:W -> Y whose range is the complement of D.support; this allows every presentation of that open subscheme. |
| Every g:W -> S factoring through H | Universal g with the premise exists h:W -> H, h >> c = g. No extra restriction on g or h is imposed. |
| Pullback g^*M | CondensedRing.upperStar (normContinuousRing E).X g applied to latticeRationalModule. |
| Every geometric point and every boundary parameter choice | IsStrictLocalKummerTameModule quantifies over every algebraically closed field kappa, geometric point s, natural r and tuple t satisfying IsStrictLocalBoundaryParameters. This tuple extends to a regular system of parameters and its product cuts out the pulled boundary. |
| The full divisibility root tower | The existing tameRootAlgebra has variables (i,n) for all positive orders coprime to p, equations x_(i,n)^n=t_i, and equations x_(i,m)^(m/n)=x_(i,n) for n dividing m. strictLocalTameRootProjection restricts its spectrum to W by the specified fibre product. |
| Finite free constant A_E-module on the tower | Mod.IsFree in that predicate means an isomorphism with finiteFree of some natural rank. This is A_E tensored with the constant finite-dimensional E-vector space E^d. |
| r=0 identity tower | Fin 0 has no variables; the empty product is 1, so the presented root algebra is canonically the original ring, and restriction is the strict-local complement. The predicate quantifies over r=0. |
| No properness or generation assertion | The conclusion consists exactly of residual constancy and the universal strict-local tameness property. |

Sources read: Bhatt--Scholze Definitions 6.8.1/6.8.3, Lemma 6.8.2 and Proposition
6.8.4(1), PDF pp.59--60; ILO IX Proposition 2.1 and its proof on printed pp.133--134,
including the strict-local simultaneous root-algebra normal form and its power maps.
The main-20261015 direct-image proof paragraph (3) was read. This node is the
agent-formulated residual-cover consequence, as the node's source record already says.
It does not claim this entire consequence is a verbatim theorem of either source.

Dependency declarations used (their full signatures and docstrings were read):

- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite: Padic.finite_coefficientExtensionRing;
  it reexports Sheaf.NumberTheory.Padics.CoefficientExtension and its actual integer
  subring, ideal, uniformizer, and quotient constructions.
- Sheaf.Topology.ContinuousMapCondensedRing: Profinite.continuousMapRingObjOfUniverse,
  continuousMapRingObjOfUniverseMonObj, isCommMonObj_continuousMapRingObjOfUniverse.
- Sheaf.Topology.ContinuousMapCondensedRingMap:
  Profinite.continuousMapRingObjMapOfUniverse and its isMonHom theorem.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic:
  AlgebraicGeometry.ProEtale.coefficientRing, condensedRingObj, upperStarFromPoint;
  Mathlib.CategoryTheory.Monoidal.Mod: CategoryTheory.Mod, ModObj and Mod.Hom;
  WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars: Mod.extendScalars.
- Sheaf.Paper.CoefficientHeartStratificationDefs:
  AlgebraicGeometry.ProEtale.IsLisseCoefficientModule.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact;
  Mathlib.AlgebraicGeometry.Morphisms.Separated: IsSeparated;
  Mathlib.AlgebraicGeometry.Morphisms.Etale: Etale;
  Mathlib.AlgebraicGeometry.Morphisms.Finite: IsFinite;
  Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap: Surjective.
- Sheaf.AlgebraicGeometry.IsRegularScheme: AlgebraicGeometry.IsRegularScheme;
  Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary:
  AlgebraicGeometry.IsStrictNormalCrossingsBoundary.
- Sheaf.RingTheory.StrictHenselizationPresentationIn:
  Algebra.StrictHenselizationPresentationIn was read. The actual pointwise strict
  henselization in the reused tameness predicate is Scheme.strictHenselizationRing
  from the published geometric strict-henselization construction, with its canonical
  Scheme.strictHenselizationStructuralMap. No new strict-henselization definition.
- Sheaf.Paper.StrictLocalKummerTameModule:
  IsStrictLocalKummerTameModule, IsStrictLocalBoundaryParameters, tameRootAlgebra,
  tameRootRelations and strictLocalTameRootProjection.
- Sheaf.Paper.NormContinuousMonodromyData: normContinuousRing and its commutativity.
  Only the coefficient construction is used; no monodromy datum is assumed.

All recorded proof-dependency modules available in the base are plain imports.
The two proof dependencies without a Lean module, lem-weil-valued-dvr-finite-quotients
and lem-sfb-strict-local-prime-to-p-kummer-splitting, have no import to add. Their
role remains explicit in the eight-step proof docstring. No proof prerequisite is
silently substituted with an assumption of the result.

Edge cases checked: M_0=0 (the rank may be zero throughout); r=0 and n=1 root order;
empty Y (the universal geometric-point assertion is vacuous); disconnected Y;
nonreduced or singular S (no normality or regularity is added there); ramified finite E;
ell=2 and all other primes different from p; all component parameter choices and
all factorizations through the single residual cover. No common finite root order is
asserted for all coefficient levels. Scheme, base field, coefficient field and
geometric residue fields are in arbitrary Type u; the small site's object/morphism
universes stay u+1/u and the abelian sheaf values stay u+1. No equality of the site's
different universes is imposed.

Searches (actual launcher msearch.py results are retained in searches.jsonl):

- LeanFinder: "A finite etale residual frame cover makes an integral l adic local
  system constant on each prime to p parameter root tower"; eight hits, including
  BDeRham/BDeRhamPlus and etale algebra residue lemmas; no matching statement.
- Loogle: "IsLisseCoefficientModule", "IsStrictLocalKummerTameModule"; zero hits.
- Mathlib grep: (lisse|Lisse).*(tame|Tame)|(tame|Tame).*(lisse|Lisse); zero hits.
- LeanSearch: "An integral l adic local system is trivial on the prime to p Kummer
  tower after a finite etale cover trivializing its residue"; eight hits about
  Krull topology, etale algebras, Witt vectors, PadicInt and BDeRhamPlus; no match.
- rg in lean/WeilConjectures and lean/Sheaf: the exact item id has no declaration.
  Name/concept searches found StrictLocalKummerTameModule, FullParameterRootTower,
  NormContinuousMonodromyData and ContinuousMapCondensedRingMap, which are reused.
  The proposed helper and main names have no collision in Mathlib, Sheaf or
  WeilConjectures. The upstream name inventory was also searched.

No statement correction, dispute, new definition node, or dependency-module repair
is needed. Three already-landed definition nodes are added to stmt_deps to record
the actual interfaces reused. The helper bundlings and maps belong to this node's
coefficient instantiation; each is listed in lean.declarations and has a source and
blueprint docstring. They neither define another notion of lisse nor another root tower.

Validation: scompile.py compiled the module alone in required module mode against
the published live server library, including all available proof imports, with no
errors or warnings (the expected sorry marker is allowed). The only postponed proof
is lisseLattice_potential_kummer_tame. Delivery dry run follows.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
