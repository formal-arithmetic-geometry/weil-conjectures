## What changed

The statement and public imports of `Sheaf.Paper.FinitePerfectAdicRealization` are
unchanged. Its theorem `AlgebraicGeometry.Scheme.finitePerfectModels_adic_realization`
now has a complete Lean proof combining compatible algebraic stalk extraction,
perfect algebraic inverse-limit reconstruction, and a specified strict-limit
comparison. The reconstruction uses `DerivedCategory.rlim_perfect_complete` and
transports its actual reduction maps, with their unit equations, to a bounded
finite-projective representative. No completeness of the original M is assumed.

`Sheaf.Paper.FinitePerfectAdicTowerExtraction` supplies explicit constant and derived
constant functors, the small Grothendieck algebraic localization, and structures
recording normalized algebraic quotient diagrams and whole-diagram local markings.
The constant functor's exactness is proved. The geometric extraction theorem is
retained as one separately sourced obligation.

`Sheaf.Paper.FinitePerfectAdicMarkedRoos` proves the finite-projective quotient
Roos calculation displayed in Stacks Tag 09C6 from an explicit representative
comparison and the proved coefficient-complex computation. Its input contains
only P and specified quotient adjunctions; transitions are defined by transposing
their units. Its public transport and exact-restriction lemmas are also proved
and reused by the specified-limit assembly.

`Sheaf.Paper.FinitePerfectAdicCanonicalComparison` retains the representative
comparison as the second separate obligation. It constructs an ordinary complex
tower and cone with compatible finite-free retracts in each degree, and identifies
the localized diagram and cone point with their specified derived realizations.
It asserts no inverse-limit or Roos property, local trivialization, or existence
of a perfect A-model. Those parts are proved separately in this packet.

`Sheaf.Paper.FinitePerfectAdicTowerLimit` proves the assembly of that calculation
with the actual total right derived inverse limit and exact slice restriction.
Its private helpers establish the Roos description of the specified
`reconstructionRlim` via a K-injective resolution, and apply the public transport
and exact derived restriction results of the marked-Roos module. The latter is proved by localizing
the exact localized extension/restriction adjunction, rather than assuming a
restriction/limit comparison. Level evaluation inverts the resolution map using
`pbcComplexEvaluation_inverts`.

`Sheaf.Paper.FinitePerfectAdicComplexRoos` proves that an ordinary inverse limit
of a termwise epimorphic complex tower localizes to a Roos limit. Its proof constructs
the kernel/one-minus-shift short exact sequence, invokes the existing pro-etale
epimorphic-tower theorem degree by degree, and identifies the localized product with
the derived product. It also proves exact countable products for completed modules.
This theorem isolates and proves the homological computation needed by the retained
canonical finite-projective calculation.

`Sheaf.Paper.FinitePerfectAdicQuotientDiagram` constructs canonical algebraic quotient
transitions from adjunction units. Its proved marking theorem turns the given unit
equations into an isomorphism of entire sequential diagrams. The limit assembly
uses this theorem. A second proved theorem identifies canonical diagrams for any
two choices of left adjoints, using their unit-preserving uniqueness isomorphisms.
Thus compatibility of arbitrary markings is no longer part of the
retained completion obligation.

`Sheaf.Paper.FinitePerfectAdicCoefficientLimit` proves the coefficient-unit case.
Its explicit module cone uses the actual completed-ring projections. Its limit
property is proved by forgetting to module presheaves, evaluating, and comparing
with the defining ring limit. A continuous set section of each surjective discrete
quotient map proves local surjectivity after sheafification, hence epimorphism of
the actual module transition. The degree-zero complex tower therefore has the
completed coefficient unit as its Roos limit. Finite powers preserve the computed
cone and epimorphic transitions, proving the finite-free case. Compatible retracts
of both the diagram and the computed cone inherit its universal property; their
transitions are epi by cancellation against the split projection. The final theorem
applies this degree by degree to complexes and then uses the complex Roos theorem.
These results have no retained holes. They prove the limit part of the marked
theorem. The remaining canonical comparison identifies its specified algebraic
derived quotient diagram with this explicit coefficient complex and its completed
realization; exact restriction is proved in the marked-Roos module.

All eight modules compile cleanly with `lcompile.py --all`. The quotient-choice
comparison also compiles independently in 2.6 seconds. All delivered Lean lines have at most
100 characters. Existing definitions and statements, source-library declarations,
consumer modules and unit realizations are unchanged. The change record
`coord/changes/W3-finite-perfect-adic-proof-instances.md` documents the two new
module-local instance attributes and the unchanged consumer interfaces. No forced
consumer adaptation is needed.

## Proved and sorry left

Closed in the assigned module: the one explicit hole of
`AlgebraicGeometry.Scheme.finitePerfectModels_adic_realization`.
There are zero explicit holes left in that module.

New proved public theorems:

- `AlgebraicGeometry.Scheme.finitePerfectAdicConstant_exact`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicTower_limit`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicMarked_roos`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicRoos_changeObject`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicRoos_changeDiagram`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicRestriction_rightAdjoint`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicRestriction_roos`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicModules_exactProducts`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicComplex_roos`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicQuotientDiagram_marking`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicQuotientDiagram_changeAdjunction`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicCoefficient_isLimit`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicCoefficientStep_epi`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicCoefficient_roos`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicFiniteFree_roos`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicRetract_roos`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicProjectiveComplex_roos`.

The private algebraic reconstruction, representative restriction
and K-injective Roos helpers are also proved without explicit holes.

Two new explicit holes remain:

- `AlgebraicGeometry.Scheme.finitePerfectAdicTower_extraction`, node
  `lem-weil-pbc-finite-perfect-adic-tower-extraction`.
- `AlgebraicGeometry.Scheme.finitePerfectAdicCanonical_comparison`, node
  `lem-weil-pbc-finite-perfect-adic-canonical-comparison`.

Both are public named theorems with source, a full proof in words and a DAG node.
There is no hole in a definition or private declaration. This packet is a
**decomposition, not a complete proof independent of sorry**: one original explicit
hole is closed and two strictly smaller, separately sourced obligations are added
(net minus one hole closed before other closure changes). The assigned theorem
still depends on those obligations and on any existing holes in the invoked
library declarations. In particular the algebraic reconstruction theorem is used
as an existing declared dependency, not claimed as newly proved here.

## No longer needed

Removed private imports from the assigned module:

- `Sheaf.Paper.CompatibleFiniteDerivedTrivializations`.
- `Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy`.
- `Sheaf.RingTheory.RlimPerfectComplete` (available through the new public interface).
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral` (available through the new
  public interface).
- `Sheaf.Paper.ConstantModuleSectionProperties`.
- `Sheaf.Paper.CompletedConstantSheafReduction`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.

The original strict-tower comparison dependency
`lem-weil-pbc-ringed-strict-tower-homotopy-limit` is replaced in this route by the
proved direct K-injective/triangle argument and the derived exact adjunction.
The countable-product wrapper `lem-weil-derived-countable-products-core` is replaced
by `lem-weil-derived-limit-products-core` plus
`lem-weil-derived-limit-existence`, the declarations actually applied in the proof.
No statement or proof step realized by `sk-thm-properbasechange` is bypassed.

The geometric and finite-projective dependencies removed as direct imports are
still needed by the retained geometric extraction and canonical comparison nodes; the new
nodes record them. They are not declared globally obsolete. No module is withdrawn
or claimed pruned from the target closure, and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The existing dependency declarations are
usable inputs, even where their proofs still contain sorry. Their current concrete
interfaces do not directly state either the whole compatible local marking of the
actual completed quotient diagram or its ordinary-to-derived finite-projective
representative comparison at the coefficient universes of this item. The separate new nodes make those two
source steps explicit instead of treating the interface comparisons as definitional
equalities. Algebraic reconstruction and the passage to the specified strict limit
are implemented in Lean, rather than included in either retained obligation.

The blueprint-ancestor helper returns None for this item's existing created.item
chain, which uses a module name at one link. The new nodes follow the existing
parent's explicit blueprint reference to `thm-weil-pbc-finite-extension`, recording
the intervening nodes and the local lifting place. Blueprint searches for compatible
trivializations, stalk perfectness, finite projective limits and Roos comparisons
found no duplicate of the new statements. A further direct Mathlib search found
`Module.Finite.exists_comp_eq_id_of_projective`, which supplies the exact algebraic
finite-free splitting for the canonical comparison; its remaining work is the
functorial coefficient realization and derived mate, not the existence of a splitting.

Edge cases checked in reading the new statements: empty schemes and empty slices
use zero diagrams/empty covers; zero complexes and finite-projective zero terms
are allowed; I=0 gives the constant quotient system; I=A gives zero quotients
(and, in the assigned theorem, completeness forces the zero coefficient ring).
The canonical comparison and marked Roos calculation need no complete A: its limit uses the completed
coefficient sheaf by construction. The extraction theorem takes no inverse limit
and chooses no A-perfect representative. No arbitrary witness is hidden inside a
definition; all diagram and functor data are explicit constructions or structures.

## New nodes

`lem-weil-pbc-finite-perfect-adic-tower-extraction` records the geometric part of
Stacks Tag 09C6, with the compatible marking input from Tags 09B1/09BV. Its Lean
attachment includes the explicit supporting constant functors and tower structures.
Its one retained theorem is strictly a local trivialization statement; it does not
assert a completed realization or existence of a perfect A-model.

`lem-weil-pbc-finite-perfect-adic-marked-roos` records the finite-projective
inverse-limit calculation displayed in Tag 09C6, with Tags 0940/0941. Its proved
theorem takes P and quotient adjunctions as input and asserts the canonical quotient
Roos triangle, independently of any geometric extraction or arbitrary input complex M.
It combines the canonical comparison, explicit coefficient-complex Roos computation,
and exact derived restriction. Its four public transport/restriction helpers are proved.

`lem-weil-pbc-finite-perfect-adic-tower-limit` records the fully proved comparison
from the specified strict total right derived limit to the completed realization
of a compatibly marked P. Its proof separately proves restriction, specified-limit
identification and transport, and invokes the preceding marked calculation.

`lem-weil-pbc-finite-perfect-adic-complex-roos` records the proved degreewise
one-minus-shift argument of Tags 0940/0941. Both its general complex-tower theorem
and the exact-products helper are proved, with no explicit holes.

`lem-weil-pbc-finite-perfect-adic-quotient-diagram` records the proved passage from
adjunction-unit equations to isomorphisms of entire sequential quotient diagrams.
Its transition construction is explicit. Both the marking theorem and the theorem
comparing any two choices of quotient adjunctions have no holes.

`lem-weil-pbc-finite-perfect-adic-coefficient-limit` records the proved ordinary
limit and epimorphic-transition assertions for the actual coefficient unit tower,
its degree-zero Roos limit, finite-free powers, compatible retracts and the
corresponding complex-tower computation. These are the explicit coefficient-complex
steps used by the proved marked-Roos theorem. Both the marked-Roos node and the
canonical-comparison statement record the appropriate coefficient dependency; these
coefficient results are all proved.

`lem-weil-pbc-finite-perfect-adic-canonical-comparison` records the separate ordinary
finite-projective representative and derived scalar comparison in Tag 09C6 and
Tags 093J--093M. Its retained theorem constructs a complex diagram and cone with
compatible coefficient retracts and their derived identifications. It does not
assert the limit property, which the preceding coefficient and complex nodes prove.

All new nodes include their actual Lean statement, proof dependencies, sources,
LeanSearch, Loogle/LeanFinder and source-grep records, and the blueprint reference. The original node's
proof, proof_deps and proof_origin follow the implemented argument. The change
record `coord/changes/W3-finite-perfect-adic-proof-instances.md` covers the local
instance attributes flagged by preflight; no existing definition or statement changes.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
