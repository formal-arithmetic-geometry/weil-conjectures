## Worker report

This repairs the returned head `7fe9d6f020e7`, retaining its ordered refinement,
source-only cutoff, and source-based statement correction. The initial required dry run
of the retained packet passed as commit `deb89aef7e`; the mathematical self-check still
found both returned defects, so the packet was repaired before pushing. Compared with the
current shared DAG, only the item's existing `statement`, `statement_change`, and `lean`
delta is delivered. No dependency nodes, proof plans, or citers are edited.

The module `lean/Sheaf/Paper/UniformConstructibleExtRational.lean` states
`AlgebraicGeometry.ProEtale.uniformConstructibleExtRational`. Its only theorem proof is
`sorry`. The helper record `RationalExtIntegralLattice` bundles the typed integral module,
local freeness, inclusion, monicity, and adjoint-isomorphism conditions from the
recorded lattice theorem. It has real data fields and no postponed proof. Its only
purpose is to reuse that triple in the source family and the global antecedent.
The helper definition `rationalExtIntegralInclusion` is the actual condensed
map induced by `(Padic.coefficientExtensionIntegers ℓ E).subtype` and
`continuous_subtype_val`; it introduces neither an arbitrary map nor a choice.
`RationalUniformExtStrata` packages the witness of this node, rather than a new
independent notion. All of its data and assertions are typed and used.

Clause-by-clause correspondence:

* The standing field and characteristic are `k`, `[Field k]`, `p`, `[Fact p.Prime]`,
  `[CharP k p]`, `ℓ`, `[Fact ℓ.Prime]`, and `hpℓ : p ≠ ℓ`.
* The rational coefficient alternative is `Λ`, its commutative ring-object instance,
  and `hΛ`, with either a finite intermediate field or `padicAlgClCondensedRing`.
  These are condensed topological coefficients, not constant discrete fields.
* The separated finite-type ambient scheme is `X` over `Spec k` with
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`. The source immersion is
  `u₀ ≫ i₀`, with open `u₀` and closed `i₀`; `j₀` is the open complement by `hij`.
  `CompactSpace S`, `QuasiSeparatedSpace S`, and `QuasiCompact j₀` make the recorded
  cohomological-dimension interfaces applicable. The schemes are Noetherian in this
  standing finite-type setting, so these size/compactness conditions exclude no case.
* `L` is an internal module over the pulled condensed coefficient ring on the small
  pro-etale site; `hL` is precisely `IsLisseCoefficientModule ... L`.
* The finite coefficient model is now actual data: `E₀ :
  PadicAlgCl.FiniteIntermediateField ℓ`, the condensed ring map `f`, and `Lmodel`.
  The disjunction requires `f` to be an equality transport of the identity in the
  finite case or of `Profinite.padicSubfieldCondensedRingToPadicAlgCl ℓ E₀` in the
  algebraic-closure case. It cannot be an arbitrary coefficient action.
  `IsLisseCoefficientModule ... Lmodel` asserts lissity; the following `Nonempty`
  contains an actual isomorphism from its scalar extension along the pulled map `f`
  to `L`. In the finite case this is the identity model up to equality transport and
  module isomorphism. In the Qbar case this is exactly finite coefficient descent.
* After choosing `W`, the first explicit conjunct asserts lissity of restrictions of
  `C₀ = i₀,* u₀,! Lmodel`, **the finite model's lower shriek**, on every stratum,
  including complementary strata. This is adaptedness to the finite model itself,
  not merely to its Qbar extension. W packages the geometric refinement separately.
* `W.stratification` is the dependency's `FiniteLocallyClosedStratification`.
  `sourceStratum`, `source_subset`, and `complement_subset` give the refinement of
  source and complement. `successive_unions_open` gives the required order.
  Empty strata are discarded by `stratum_nonempty`; empty X permits `n = 0`.
* The open/closed factors, complement maps, and `factorization` identify each actual
  immersion with its open-then-closed factorization. `hclosure` gives exactly the
  closure of its stratum, and `hcomplement` gives its complementary open. Compactness
  and quasi-separatedness fields supply the dimension API instances.
* The next explicit conjunct supplies, for every source stratum, a bundled
  `RationalExtIntegralLattice` with module `N` over
  the pulled `continuousMapRingObj (coefficientExtensionIntegers ℓ E₀)`,
  `CondensedRing.LocallyFree _ N`, and `ι : N ⟶ (Mod.comap aT).obj LT` with
  `Mono ι` and `IsIso (((Mod.extendRestrictAdjunction aT).homEquiv N LT).symm ι)`.
  Here `LT` is the restriction of `C₀`, and `aT` is the pulled actual integral
  inclusion. This is the same lattice triple as `exists_stratified_lisse_integral_lattice`.
* `cutoff_eq` gives `c_a_k = relativeCohomologicalDimension j_k +
  cohomologicalDimension S_k + 2`. The formula for `d` takes the supremum only over
  strata contained in `Set.range (u₀ ≫ i₀)` and includes zero via `max 0`.
  Nonempty strata ensure that empty source gives an empty index and hence `d = 0`.
* `IsConstantModelConstructible ... (i₀,* u₀,! L)` records constructibility for the
  original coefficients as well. The subsequent source-stratum restriction clause
  records their lissity, in addition to finite-model adaptedness in `W`.
* The quantifiers `T,B,V,v,kb,j,hjb,M,hM,q` cover every locally closed target,
  every lisse target module and every nonnegative degree. `Abelian.Ext` is the
  recorded derived shifted-Hom model, and `Subsingleton` says its group is zero.
  The implication `(q : WithTop ℕ) > d` is the uniform bound. All source data occur
  before these target quantifiers, so they are independent of `b,M`.
* The final global-lattice antecedent is `Nonempty (RationalExtIntegralLattice
  ((upperStarFromPoint S).map (rationalExtIntegralInclusion ℓ E₀)) Lmodel)`: it uses **the same finite `Lmodel`** and an
  integral module `N`, `LocallyFree`, a monomorphism into its integral restriction,
  and the isomorphism of the adjoint induced by that inclusion. Its coefficient
  ring is O_E₀, not Λ. This handles both finite and Qbar cases. Its conclusion
  quantifies all targets again and gives Ext zero above the original
  `relativeCohomologicalDimension j₀ + cohomologicalDimension S + 2`.
  It does not equate that cutoff to the refined maximum.

Dependencies used (module and declaration):

* `Sheaf.Paper.UniformConstructibleExtTorsion`:
  `AlgebraicGeometry.ProEtale.CondensedRing.uniformConstructibleExtTorsion`, with
  the dimension convention from its imports.
* `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`:
  `CategoryTheory.Abelian.Ext` and its derived shifted-Hom interpretation.
* `Sheaf.Paper.FiniteCoefficientDescentTwoColimit`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientDescentTwoColimit`; its imported
  canonical condensed finite-field maps and ordinary scalar extension are used.
* `Sheaf.Paper.CondensedConstantConstructibility`:
  `IsConstantModelConstructible` on the pulled condensed coefficients.
* `Sheaf.Paper.CoefficientHeartCommonStratification`:
  `coefficientHeart_commonStratification`, `IsLisseCoefficientModule`,
  and `coefficientHeartRingObj`.
* `Sheaf.Paper.StratifiedLattice`:
  `CondensedRing.exists_stratified_lisse_integral_lattice`. Its exact integral
  inclusion and extension/restriction-adjoint interface is used in both lattice clauses.
  `CondensedRing.LocallyFree` is read from its public dependency
  `Sheaf.Paper.ContinuousLocallyFreePullback` using `scompile.py --source`.

The proof-only imports now include UniformConstructibleExtIntegral,
ConstructibleExtContinuity, CoefficientHeartFiltration, PadicIntegersInvertEll,
CartesianCoefficientsFiniteFree, FilteredColimitsTensor, ProEtaleOpenClosedSequenceRingSheaf,
LocallyClosedExtensionCoherence, ChangeOfCoefficients, Ext.ExactSequences, and Noetherian.
They provide the recorded integral, continuity, filtration, tensor-colimit, scalar,
restriction, exact-sequence, and Noetherian inputs for the docstring's ten proof steps.
The DAG's scalar-six-pullback node has no recorded Lean declaration; the available
canonical change-of-coefficients and locally-closed extension interfaces are imported.
No proof of that independent node is fabricated here.

Edge cases: zero rank is permitted by LocallyFree. For empty source no nonempty stratum
can be contained in its image, so the cutoff is zero. Empty X has empty stratification.
An infinite dimension gives a vacuous degree condition. Every finite target rank and
finite extension degree is independently quantified. In the old antecedent the identity
on L always witnessed a global lattice; in the new one L is an E₀-module whereas N must
be a locally finite free O_E₀-module. Restricting L to O_E₀ does not make it a finite free
integral module. The nodal monodromy-by-ell example therefore no longer supplies a
spurious global lattice.

Searches: retained previous searches and repeated `msearch.py` leanfinder for
“uniform Ext vanishing for extension by zero lisse E or Qbar sheaves with stratified
integral lattice cutoff”: 8 unrelated/generic hits (Ext/cohomology/complex extension).
`msearch.py` loogle for `Abelian.Ext, IsLisseCoefficientModule`: no hits, unknown
identifier `Abelian.Ext` in the search service. `msearch.py` grep for
`uniformConstructibleExtRational|rationalExtIntegralInclusion`: no Mathlib hits.
`rg` for those names and the node ID over upstream WeilConjectures and shared lean/Sheaf
found only the downstream UniformConstructibleExt proof docstring. Searches for the
integral map found the lattice theorem's local `a` and other sheaf-valued lattice
interfaces; none is a named condensed inclusion for this precise coefficient ring.
The helper therefore constructs the existing ring-sheaf map directly, without a second
lattice predicate or private copy of a dependency definition.

## Statement corrected

The correction retained from the returned packet replaces the false claim that the
refined maximum equals `c_a` in the global-lattice case by Ext vanishing above `c_a`.
The node's prior TeX already required an actual integral lattice; the returned Lean
had failed to express it. This repair changes no further natural-language statement.
The source is the rational proof's global-source-lattice argument and the DAG's
reviewed fixed-source, refined-cutoff proof. The statement_change retains its original
old_statement verbatim. The only citer, `sk-lem-uniform-constructible-ext`, is marked
`holds: false`: its proof claims the unrefined bound for arbitrary rational lisse
sources. It must use the refined bound or supply a global lattice. It is not edited.

## Self-check of returned findings

Self-check performed with the saved node, current shared node, returned findings, and
revised file open; no separate reader or sub-agent is claimed. Finding 1 is repaired:
the final antecedent is existence of the bundled integral LocallyFree module,
mono into Mod.comap of Lmodel, plus
adjoint IsIso, and applies to the fixed finite model in Qbar. Finding 2 is repaired:
finite_model_data : Prop is removed and replaced by E₀, a canonical f, actual Lmodel,
lissity, and scalar-extension iso; the two explicit conjuncts following W give actual
integral lattice triples on each source stratum and adaptedness to a_!Lmodel. The minor H8 findings are repaired by the module
docstring, all ten proof steps, and the available proof-dependency imports. The check
also replaced mere equality of factorization images by equality of the actual maps and
discarded empty strata to enforce the empty-source cutoff convention. Each hypothesis
and clause is matched above. The original source-only cutoff and global-lattice
vanishing implication are retained; no arbitrary map, assumed global lattice, or
statement weakening is introduced.

Validation note: the first expanded stratification record hit Lean's default 200000
heartbeat limit. Bundling its repeated integral-lattice triple in
RationalExtIntegralLattice, generic in its two coefficient rings and their map,
reduces repeated geometric coefficient elaboration. Both theorem uses specialize it
to the pulled actual O_E₀ -> E₀ inclusion. The geometry is packaged separately in W;
adaptedness and the stratum-lattice family are explicit theorem conjuncts. The
inclusion is a named definition with its existing IsMonHom instance. No heartbeat
or 60-second limit is raised, and no lattice condition changes.

Final compiler validation: `scompile.py NE det-uniform-constructible-ext-rational
lean/Sheaf/Paper/UniformConstructibleExtRational.lean` passed on the server in both
sandbox (9.2 s) and library-module (7.5 s) checks, with no warnings or errors.
All temporary diagnostics were removed. The only postponed theorem is the item itself.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
