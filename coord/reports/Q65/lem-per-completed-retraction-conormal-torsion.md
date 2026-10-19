## Worker report

The module `Sheaf.RingTheory.CompletedRetractionConormalTorsion` states
`AdicCompletion.exists_pow_annihilates_completed_retraction_conormal`, with proof
`sorry`. No definitions, extra nodes, dependency replacements or statement corrections
are needed. Q39's reviewed PASS concerns the stage-1 split only: the current node has
no `lean` record. This delivery retains that split and all other node fields.

The node and Lean correspond as follows:

- The commutative Noetherian base is `(R : Type u) [CommRing R]
  [IsNoetherianRing R]`; the ideal is `(J : Ideal R)`.
- The commutative R-algebra is `(S : Type u) [CommRing S] [Algebra R S]`;
  finite type is `hS : RingHom.FiniteType (algebraMap R S)`. No module-finiteness,
  domain, nonzero, local or proper-ideal assumption is imposed.
- The structural map of spectra is `Spec.map (CommRingCat.ofHom (algebraMap R S))`.
  The target open is the complement of `PrimeSpectrum.zeroLocus (J : Set R)`.
  `hetale` asserts `Etale` of the restriction of this map over precisely that open.
- The base completion is `AdicCompletion J R`; the source completion is
  `AdicCompletion (J.map (algebraMap R S)) S`. Its nth coordinate is S/(JS)^n,
  and `(JS)^n = J^n S`, so this is precisely the node's completed algebra.
- The retraction is written as an R-algebra map `σ` from the latter completion to
  the former. This is an equivalent encoding of the completed-base-algebra maps,
  not a choice of an arbitrary structural map. Here is the equivalence in detail.
  Write C = completion(R), B = completion(S), and let i : C to B be induced by the
  structural map. Every C-algebra map restricts to an R-algebra map. Conversely,
  an R-algebra map σ sends J^n B into J^n C, by expanding generators of the
  extended ideal, and therefore is continuous. For each n, C/J^n C = R/J^n,
  since R is Noetherian and J is finitely generated. For t in C choose a in R
  representing t modulo J^n C. Then σ(i(t)) and t both equal a modulo J^n C.
  Separatedness of C gives σ(i(t)) = t. Multiplicativity now implies
  σ(i(t)b) = t σ(b), precisely C-linearity. Thus the quantifier in Lean describes
  exactly all the retractions of the node. This is also the R-algebra-map
  formulation used by Stacks 0AKJ and the landed hom-lifting consumer.
- The kernel is `RingHom.ker σ.toRingHom`; its quotient K/K^2 is Mathlib's
  `Ideal.Cotangent`, whose definition is K modulo K times the top submodule of K.
  This submodule has image K^2 in B (`Ideal.map_toCotangent_ker`).
- The nonnegative exponent is `∃ c : ℕ`. The quantifiers `∀ r ∈ J ^ c, ∀ x :
  (RingHom.ker σ.toRingHom).Cotangent` and the equality
  `algebraMap R (AdicCompletion (J.map (algebraMap R S)) S) r • x = 0`
  express exactly that every element of J^c kills the conormal, with the R-action
  through R to the completed S. This explicitly avoids an unrelated scalar action.

All universe variables are bound explicitly and `autoImplicit` is disabled. The
schemes use one common universe for R and S, as required by `Spec.map`; the theorem
is polymorphic in that universe and imposes no cardinal bound or test-object
quantifier. Both rings can always be viewed in a common larger universe.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (and `Ideal.fg_of_isNoetherianRing` for the proof plan).
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `RingHom.FiniteType`, instantiated at the structural ring map.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`, available through the
  public Etale import.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`, with its actual ring and algebra structures from
  `Mathlib.RingTheory.AdicCompletion.Algebra`.
- For the stated proof dependencies, `lem-weil-pbc-adic-completion-mod-ideal` is a
  Mathlib leaf: `AdicCompletion.isAdicComplete_self` from
  `Mathlib.RingTheory.AdicCompletion.LocalRing`, `ker_evalOneₐ_eq_map` from
  Completeness, and `evalOneₐ_surjective`, `evalOneₐ_comp_algebraMap_eq_mk` from
  Algebra. These modules are imported via LocalRing/Algebra.
  `def-weil-pbc-module-tensor-product` is the Mathlib `TensorProduct` and
  `LinearMap.rTensor` API; its Map module is a proof-only import.
- The proof nodes `lem-per-etale-away-completed-cotangent-torsion` and
  `lem-per-completed-cotangent-transitivity` have neither Lean records nor Mathlib
  matches in the current DAG. They are proof dependencies, not prerequisites for
  stating this theorem, so there is no module to import yet. Their uses are written
  out in the proof docstring; the maintainer can add imports when those nodes land.

Source checked: `literature/stacks-project/restricted.tex`,
`lemma-fully-faithful-etale-over-complement` (Tag 0AKJ), the existence paragraph
for A = C, explicitly concludes that ker(φ)/ker(φ)^2 is killed by a power of I,
using `lemma-rig-etale` and `lemma-exact-sequence-NL` (0ALQ and 0ALM).
The docstring follows the node's four steps: complete finite-type reduction;
surjectivity and continuity; zero-variable presentations in the completed
transitivity sequence; tensor annihilation and injectivity.

Edge cases checked before writing:

- J = 0: choose c = 1; its zero power ideal acts trivially. There is no assumption
  that the conormal itself vanishes.
- J = R: the completions are zero rings, hence so is the conormal.
- c = 0 is allowed and means the whole conormal vanishes.
- S = R with the identity retraction gives zero kernel.
- Zero rings and empty spectra are allowed; no Nontrivial assumption is present.
- R = k[t], J = (t), S = R[x]/(tx,x^2), with x mapped to zero: the algebra is
  etale after inverting t, while its completed kernel conormal is nonzero and is
  killed by t. This checks the necessity of a torsion conclusion.
- Finite type is not finite as a module: R[x]/(tx^2-x) over k[t] is etale away
  from t and has a retraction, but is not finite over R. The statement covers it.

Searches made (2026-10-19):

- `msearch.py`, LeanFinder: "The conormal module of the kernel of a retraction
  from the adic completion of a finite type algebra etale away from an ideal is
  annihilated by a power of that ideal". Eight hits include
  `Ideal.isTorsionBySet_cotangent`, `Ideal.mem_toCotangent_ker`,
  `Algebra.Extension.ker_infinitesimal`, and formal-etale lifting. None assert
  annihilation by a power of the base ideal for a completed retraction.
- `msearch.py`, Loogle: `AdicCompletion, Ideal.Cotangent`. Zero hits.
- `msearch.py`, LeanSearch: "Conormal module kernel retraction adic completion
  finite type algebra etale away from ideal annihilated ideal power". Eight hits
  on completion constructions and formally smooth splittings, none this statement.
- `msearch.py`, Mathlib grep: `conormal|[eE]tale.*[cC]ompletion|[cC]ompletion.*[eE]tale`
  in RingTheory. Two ordinary cotangent hits, neither the completed assertion.
- `rg` of the upstream WeilConjectures sources for the node id, completed
  retraction and conormal-power patterns found no declaration of this statement.
- `rg` of `lean/Sheaf` found `ConormalTorsionAlgebraization` (uses conormal torsion
  as an assumption), `OneDimensionalComponentConormal` (a different
  one-dimensional setup), and `EtaleAwayCompletionHomLifting` (cites the node in
  its proof docstring). None duplicates the present theorem.

Validation: the prescribed `scompile.py Q65
lem-per-completed-retraction-conormal-torsion` compiled both sandbox and library
views of this single file cleanly, about 2.5 seconds each, without warnings.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
