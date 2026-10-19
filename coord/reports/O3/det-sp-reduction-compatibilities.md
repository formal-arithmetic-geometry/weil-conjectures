## Worker report

The retained draft is completed as `Sheaf.SecSmoothPurity.ReductionCompatibilities`.
It contains three theorem statements, each with proof `by sorry`, and no new definitions:
`AlgebraicGeometry.ProEtale.reductionCompatibilities_unit`,
`AlgebraicGeometry.ProEtale.reductionCompatibilities_composition`, and
`AlgebraicGeometry.ProEtale.reductionCompatibilities_purity`.
The item's statement, proof, and dependency lists are unchanged. Only `lean` is set.
The primary recorded signature is the first theorem verbatim; `lean.declarations` lists all
three. The module docstring and theorem docstrings identify the blueprint source and carry
the full proof route, including the compact-support projection step and common exponent.

Source read: current main-20261015 blueprint
`sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-compatibilities.md`, the current
DAG statement and its eight proof steps; dependency statements, signatures and docstrings.
No `blueprint_update` supersedes this source.

Hypotheses and objects, clause by clause:

* The global field and its characteristic are `D : WeilConjectures.FiniteFieldDatum`.
  This contains the specified finite field and its fixed algebraic closure `D.k`.
  `(ℓ : ℕ) [Fact ℓ.Prime]` and `hℓ : ℓ ≠ D.p` express the prime and invertibility condition.
* `X,Y : Scheme`, their `Over (Spec (.of D.k))` instances, and the three instances
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on each structure map express
  separated finite-type k-schemes. `f.IsOver` makes f a k-morphism. `[IsSeparated f]`
  and `(d : ℕ) [SmoothOfRelativeDimension d f]` give exactly the stated smooth separated
  map of pure nonnegative dimension, using Mathlib's recorded definitions.
* In clauses 1 and 2 `cpt : Compactification f` fixes the coefficient-independent
  factorization; its Z, open i, proper g and commutation are genuine compactification data.
  Its Z is over k, separated and finite type, and both factors are over k, as in the
  definition of b. In clause 3 `[HasCompactification f]` supplies the common selected
  compactification used by the recorded exceptional and purity constructions. This
  presents the chosen compactification from the source, whose existence follows in the
  standing scheme setting, rather than assuming any new geometric property.
* `{A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]` and `φ : A →+* B`
  give arbitrary finite commutative rings and a unital homomorphism. `hA,hB` in clauses
  1 and 2 state existence of an ell-power annihilating every element. Clause 2 adds C,
  its finiteness, `hC`, and `ψ : B →+* C`. Neither nontriviality, flatness, nor a DVR
  presentation is assumed.
* `spFiniteConstructibleTorCategory T R` is the recorded FULL subcategory defined by
  bounded cohomology, intrinsic constructibility of each cohomology sheaf, and finite
  Tor amplitude. The Tor interval tests EVERY degree-zero module sheaf. This is the
  uncompleted constant-ring category, not a condensed or completed category.
* The hF and hS families certify restriction of the actual compact-support and scalar
  functors to these full subcategories. `reductionCtfCompactSupport` and
  `reductionCtfScalar` leave their objects and arrows unchanged. These are the witnesses
  already furnished by `reductionExceptional_isIso` and scalar preservation. Their use
  makes the statements work for every choice of these proof witnesses. They are not
  replacement functors or stronger coefficient assumptions.
* GA, GB (and GC) with adjA, adjB (and adjC) are precisely the constructible right
  adjoints of the compact-support functors stipulated in the node. Giving these
  adjunctions explicitly retains their actual units and counits; no arbitrary
  unnormalized exceptional map is substituted.
* c (and cAB, cBC, cAC) is a NATURAL transformation between those specified functors.
  The hc equations fix it to the comparison in `det-sp-reduction-exceptional`:
  `b ≫ P_B(c) ≫ ε_B = T_Y(ε_A)`. This is its defining equation multiplied on the left
  by b. On the stated Dctf input b is invertible by `reductionDirectImage_isIso`, so it
  is equivalent to the recorded equation involving inverse b. Adjunction transposition
  determines c uniquely; it is not an unconstrained comparison. The exceptional
  dependency supplies its existence and invertibility.

Clause 1 is `reductionCompatibilities_unit`. Its M is an object of the full Dctf category
on X. The three factors on the left are, in order, `(η_A(M))_B` rendered by
`(scalarExtensionFunctor φ X).map (adjA.unit.app M).hom`, c at `P_A M` rendered by
`(c.app ((reductionCtfCompactSupport ...).obj M)).hom`, and `G_B(b(M))` rendered by
`(GB.map (ObjectProperty.homMk ((reductionDirectImageComparison ...).app M.obj))).hom`.
The right side is `(adjB.unit.app ((reductionCtfScalar ...).obj M)).hom`. Lean uses
left-to-right composition `≫`. The equality is in the ambient category; because the
subcategory is full, it is exactly the displayed equality in Dctf. No conclusion about
invertibility needs to be repeated from the dependency.

Clause 2 is `reductionCompatibilities_composition`. The input K is in Dctf(Y,A).
The left side first applies scalar change ψ to cAB, then cBC at K_B, then GC applied to
the Y scalar associator `scalarExtensionFunctor_composition φ ψ Y`. The right side is
the X scalar associator `scalarExtensionFunctor_composition φ ψ X` at GA K followed by
cAC. Multiplying the source-identified equation in the node by the invertible X
associator gives exactly this square, so no additional equation or clause is imposed.
All three c maps satisfy their separate counit equations. All six scalar-restriction
witnesses and all three compact-support witnesses name the recorded functors.

Clause 3 is `reductionCompatibilities_purity`. It uses exactly the fixed-coefficient
presentation chosen in `finiteGeneralRingSmoothPurity`:

* A and B remain the same arbitrary finite rings; `ULift.{u+1,u}` only places their
  fixed modules at the site coefficient universe. `RingHom.ulift φ` is the same ring map.
* A single `n : ℕ`, `hn : 1 ≤ n`, and `hA,hB` saying the casts of ell^n vanish give a
  common annihilator. Every pair of ell-primary rings has such a positive n. Computing
  at a common n is valid by the exponent-independence clause of the general-ring node.
* `geometry` is the actual diagonal normal-cone/Rees geometry used by that node.
  `alphaA,alphaB` orient the actual ordinary dualizing complexes to the actual shifted
  Tate lines. `_ha,_hb : OrientationNormalized ...` specify precisely the diagonal
  mate, the t=1-normalized deformation comparison and the integration-transposed
  bundle arrow from that dependency. Thus alpha is not an arbitrary orientation.
  The is-unit proof comes from `finiteGeneralRingPrimeSetting D ℓ hℓ n hn`, exactly as
  in general-ring purity. IsNoetherian X is constructed from finite type over D.k;
  `QuasiCompact f` is constructed from compactness of X and quasi-separatedness of Y.
  Neither is an extra hypothesis. The same witnesses apply to both rings.
* e is the published `CoefficientLineComparison (RingHom.ulift φ) (ℓ^n) (ℓ^n) ...`.
  Its roots_power equation, at the SAME positive exponent, forces the root map to be
  identity through the monic root inclusion. Its generators and derived_normalization
  fix the ordinary scalar tensor identification. It includes no freely chosen scaling
  of the Tate line. `proLambda f d e K` is exactly the canonical scalar/pullback/shifted
  Tate source identification from the node.
* K has type `Etale.FiniteSmoothPurity.proCategory (ULift A) Y`; `_hK : IsCtf ...`
  is bounded INTRINSIC constructibility and finite Tor amplitude on that same ordinary
  pro-etale category. `sfIntrinsicDerivedEquivalence` identifies it with the intrinsic
  constant-ring encoding of clauses 1 and 2. This equivalence realizes the same modules,
  rather than imposing an etale-origin hypothesis. The bounded origin property used
  by the formula follows from the finite-ring origin dependency.
* The left side is scalar extension of `proGamma A f _ alphaA K`, then the actual
  counit-transpose `proCoefficientMap (RingHom.ulift φ) f K`. The right side first
  applies `proLambda`, then `proGamma B f _ alphaB K_B`. These are the precise gamma,
  c and source balancing used by `finiteGeneralRingSmoothPurity`. The explicit source
  arrow writes out the identification implicit in the node's formula.

Dependency declarations used (owning module followed by declarations):

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  `AlgebraicGeometry.SmoothOfRelativeDimension`. The scheme-properties node is a
  convention collector, with no declaration: its named Mathlib scheme property classes
  are used directly. `QuasiCompact.compactSpace_of_compactSpace`,
  `quasiSeparatedSpace_of_quasiSeparated`, and `quasiCompact_of_compactSpace` supply
  proof witnesses without adding a hypothesis.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: finite constant-coefficient module
  category conventions, with `Scheme.proEtaleDerivedCategory` and its constant ring.
* `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `scalarExtensionFunctor`,
  `scalarExtensionFunctor_preserves_constructible_tor`,
  `scalarExtensionFunctor_composition`.
* `Sheaf.SecSmoothPurity.ReductionDirectImage`: `reductionDirectImage_isIso`,
  `reductionDirectImage_cocycle`; its public imported canonical arrows are
  `reductionCompactSupport` and `reductionDirectImageComparison`.
* `Sheaf.SecSmoothPurity.ReductionExceptional`: `reductionCtfCompactSupport`,
  `reductionCtfScalar`, `reductionExceptional_isIso`, and its canonical realization
  and site/scalar identifications. `spFiniteConstructibleTorCategory` is the actual
  full subcategory publicly imported from `Sheaf.Paper.SmoothPurityNormalizedTowers`.
* `Sheaf.SecSmoothPurity.FiniteGeneralRing`: `finiteGeneralRingPrimeSetting`,
  `finiteGeneralRingSmoothPurity`, `FiniteGeneralRingAt`, `finiteGeneralRingScalarIso`.
* `Sheaf.Paper.ProEtaleConstructibleSheaf`: `Scheme.IsConstructibleProEtaleModuleSheaf`;
  `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude` retains the original
  `Scheme.HasProEtaleTorAmplitude`, `Scheme.HasFiniteProEtaleTorAmplitude` alongside
  its coefficient-sized interface. We use the already recorded intrinsic Dctf model.
* `Sheaf.Paper.FiniteSmoothPurityMaps`, public through the general-ring dependency and
  `Sheaf.Paper.FiniteSmoothCoefficientArrows`: `OrientationNormalized`, `proCategory`,
  `IsCtf`, `proGamma`, `CoefficientLineComparison`, `proCoefficientMap`, `proLambda`.
  These are existing public constructions used by the dependency itself; no duplicate
  helper or private notion is introduced.

Proof-only imports retain every stated proof dependency: the scalar and exceptional
modules above; `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`;
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`;
`Sheaf.Paper.RingedExchangeTensorCoherence`;
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`;
`Sheaf.Paper.FiniteRingCompactSupportProjection`.

Searches (the retained `searches.jsonl` records the original exact results):

* msearch Loogle `CategoryTheory.Adjunction, CategoryTheory.NatTrans`: zero hits.
* msearch LeanFinder `Change of coefficients preserves adjunction units, composes for
  exceptional inverse image, and preserves smooth purity`: eight hits, including
  `Scheme.Modules.pseudofunctor`, `pseudofunctor_map_adj`, module pullback adjunctions,
  and conjugation of pullback composition. These concern ordinary module pullback,
  not the three canonical exceptional/purity comparison identities here.
* msearch LeanSearch `Derived coefficient change preserves compact support adjunction
  units and smooth purity`: eight hits, including `CategoryTheory.Adjunction.derived_unit`,
  `derivedη`, and compact-support calculus lemmas. None states the node's three identities.
* msearch grep `purity|upperShriek|exceptionalInverseImage|TateTwist` in Mathlib's
  CategoryTheory: zero hits. Direct Mathlib Mates source search finds
  `mateEquiv_vcomp` and `mateEquiv_hcomp`, general tools with different statements.
* Direct rg for `reductionCompatibilities|det-sp-reduction-compatibilities` in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and shared `lean/Sheaf`: no hits.
  Dependency declarations and their exact signatures were read at the paths above;
  the normalized finite smooth coefficient and purity constructions already exist
  and are reused. No new definition node or dependency repair is needed.

Edge cases checked by reading the definitions and equations: A,B,C may be the zero ring;
no Nontrivial binder is present. An exponent 0 in the annihilator convention forces that
zero-ring case and is covered by the positive common exponent presentation. Empty X or Y
is not excluded; relative dimension is the recorded pointwise notion. Dimension d=0 uses
the actual empty tensor power and shift zero, and the source root comparison is its
canonical unit comparison. Identity coefficient maps and two successive identity maps
use the same scalar associators and canonical tensor unitors, rather than arbitrary
identifications. Nonflat finite ring maps, for example Z/ell^2 to Z/ell, remain allowed.
K=0 and zero complexes remain in the full subcategory. Every universe and variable is
explicit; both auto-implicit options are disabled.

Validation: the interrupted sandbox had no node copy or report, so there was no complete
delivery to repeat. The first resumed scompile diagnosed the missing QuasiCompact f
proof witnesses in the two orientation predicates. They were derived explicitly using
Mathlib's compactness and quasi-separatedness lemmas. The corrected file passed both
sandbox and library-module checks through scompile.py (7.6 s and 6.9 s). The final delivery
is then checked by deliver2.py --no-push, including its fresh per-file compile.
No STATEMENT-DISPUTED flag and no statement correction are necessary.

## Second reading by N3

Author's second reading, following the dispatcher instruction not to start agents; the
maintainer supplies the independent review. I reopened the node statement, all three
signatures, and the definitions of OrientationNormalized, CoefficientLineComparison,
proCoefficientMap, proGamma, IsCtf, and spFiniteConstructibleTorCategory. Clause 1 has the
three unit factors in the correct order and the B-unit as target. Clause 2 has BOTH
scalar associators, at X and inside GC at Y; its square is the node's composite equation
multiplied by the X associator. Each counit equation is the equivalent b-multiplied
version of the exceptional dependency's defining transpose. Clause 3 retains the actual
diagonal/DNC normalization, the canonical root-generator comparison and the same
finite-ring purity maps; it does not assert compatibility of arbitrary orientations.
Its K hypothesis is intrinsic Dctf, and the finite-ring comparison only supplies the
etale origin needed to evaluate the canonical transported arrows. I checked every
standing geometric and coefficient hypothesis against the explicit binders above.
The only defect found in the retained draft was the two missing quasi-compactness proof
terms; explicit derivations repair them without adding a binder or changing the node.
No definitions are duplicated, no proof is supplied, and all three sorries belong to
the three clauses of this single node with their proof route in the docstrings.
