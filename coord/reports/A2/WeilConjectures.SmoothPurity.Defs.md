## What changed

Partial proof work in WeilConjectures.SmoothPurity.Defs, preserving every existing
public signature, attribute, import and definition body. Added one private proof
import, Sheaf.Paper.CondensedTateIntegralTower, and eight proved private helpers:

- smoothTrace_reconstructionInputs instantiates the declared finite/integral tower
  theorem on f.left. It supplies the scheme-over and morphism-over instances,
  transports finiteness from the native Over objects, and uses prime characteristic
  to obtain positivity. Its conclusion retains all normalized finite purity data,
  integral Tate/unit reconstructions and specified finite identifications.
- smoothTrace_openComparison_counit identifies the actual inverse open right-adjoint
  comparison as the mate of the actual compactification comparison. The mate-counit
  equation proves the counit square for every bounded constructible K.
- smoothTrace_openUnit_counit includes the actual monoidal unit map and transports
  it through the left comparison by naturality.
- smoothPurityMap_eq_of_trace_formula recovers an arbitrary specified input arrow
  from its counit transpose. The existing private isIso helper now consumes it.
- smoothPurityMap_of_reconstructed_trace lifts the supplied ambient Tate realization
  through the full constructible inclusion, constructs the comparison isomorphism,
  identifies its hom with the actual adjunct from an explicit trace formula, and
  proves the ambient inverse formula. This helper precedes the disputed instance.
- smoothPurityIso_eq_of_reconstructed_trace identifies that inverse with the actual
  defined smoothPurityIso.
- smoothPurityIso_comp_of_reconstructed_traces proves the last composition step:
  from the two explicit trace formulas and common-source comparison square, cancel
  the comparison isomorphism and map the inverse equation through the inclusion.

- smoothPurityIso_zero_of_trace_formula specializes the inverse formula to the
  coefficient unit and the exact zero-twist and zero-shift maps, giving the original
  zero-dimensional normalization from its explicit trace formula.

Three attached route nodes record these partial proofs. Change record:
coord/changes/A2-smooth-purity-native-trace-glue.md.

## Proved and sorry left

Original holes closed: 0 of 4. Holes added: 0. Split off: 0. This delivery proves
parts of the existing plans, not a complete proof or decomposition of an original
hole. The eight private helper proofs above and the refactored private invertibility
helper contain no sorry.

Every original hole remains, with its existing attachment:

- AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace:
  def-route-smooth-trace. The normalized finite and integral inputs are available;
  constructing the matching condensed exceptional Context/Datum and the prescribed
  comparison and Tate realization, and installing their actual counit composite as
  the definition, remains unresolved.
- AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothPurityMap:
  lem-route-is-iso-smooth-purity-map. The existing missing-smoothness statement
  dispute and independently proved counterexample remain. The reconstructed
  comparison and actual trace formula are still needed for the intended smooth case.
- AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_zero_of_isOpenImmersion:
  lem-route-smooth-purity-iso-zero-of-is-open-immersion. The native open counit square
  and the zero-twist/zero-shift inverse algebra are now proved; identifying the
  geometrically reconstructed trace with that counit remains.
- AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_comp_openImmersion:
  lem-route-smooth-purity-iso-comp-open-immersion. The last inverse-comparison algebra
  is proved; constructing the normalized comparisons and proving their square remain.

No arbitrary isomorphism witness is selected, no definition is replaced by zero,
and no contradiction from the disputed instance is used. The native input lemma
retains smoothness through its proof. The formal comparison lemmas do not assert
geometric existence: their data and trace equations are explicit hypotheses. They
work also on empty schemes and at d = 0; no nonzero-unit assumption is added.

## No longer needed

None. No import, declaration, node or module is withdrawn or pruned. The existing
geometric dependency lists and unit route are retained: the formal last steps do
not remove the need to construct their inputs. In particular finite smooth purity,
normalized Tate reconstruction, exceptional reconstruction, Tate realization, open
counit realization, coefficient compatibility and compositor realization remain
needed by the unresolved geometric steps.

Searches made with msearch.py: LeanFinder for full-faithful lifting and counit
transposes, Loogle for FullyFaithful and Iso, and grep for preimageIso,
homEquiv_counit and mapIso_injective. Mathlib already provides the lifting and
adjunction primitives, so those primitives are used directly. Local source searches
found no normalized condensed trace constructor independent of this module. The
current blueprint smooth trace definition and purity-transport/composition routes
were read; the blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The existing STATEMENT-DISPUTED remains material: the elaborated purity instance
omits SmoothOfRelativeDimension d f.left. The source already proves, before that
instance, a contradiction to its conclusion at an identity separably closed point
with proposed dimension one. A proof of that universal signature would be false.
There is no SmoothPurity.Defs exception in upstream-statement-exceptions.tsv, so
this packet does not alter its signature or use it to derive False.

The route's words "apply exceptional reconstruction" still require a concrete
Context/Datum, its normalized finite identification maps and the coefficient/site
comparisons linking the native Tate tower to the specified realization family.
The native input and formal inverse/counit lemmas delivered here do not silently
assume that construction is complete. This is not a claim that admitted dependency
theorems are unusable: the input lemma uses the declared reconstruction theorem
as intended, regardless of its transitive proof holes.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
