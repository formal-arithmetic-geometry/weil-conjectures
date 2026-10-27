## Worker report

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-positive-monoid-convolution-length.json`: item, split into ten elementary proof steps; not a Mathlib leaf.
- `citations.json`: empty list, because no proof step cites a DAG node. The statement retains `def-weil-pbc-free-module`; its definition was read, but the proof does not need freeness.
- `report.md`: this report. The search command owns the accompanying `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. Searches of `lean/WeilConjectures/` by blueprint tag and by positive monoids, weight and convolution found no declaration proving this item. The related `lean/Sheaf/RingTheory/FinitePatternFactorization.lean` is a sorried theorem about a larger coefficient-factorization assertion, not an attachment.

WANTED: none.

What was wrong: the imported item was statement-only. Its ILO source correctly labels the coefficient argument as agent-supplied; ILO does not assert this whole auxiliary theorem. No mathematical error in the statement was found, and the statement, hypotheses, source and ancestry are unchanged. In particular, finite low-length sets must not be deduced by reversing the bound on maximal length: step 4 gives a separate generator-coordinate proof. No completeness, Noetherianity, domain hypothesis, saturation, or independence of the generators has been introduced.

Unfinished: none at stage 1. This is a natural-language split, not a Lean proof or a compiled declaration.

## Source and search record

I read ILO, *Travaux de Gabber*, Exposé VI §1.6(i)--(ii), printed p. 70 / PDF p. 76: the equal- and mixed-characteristic formal monoid models motivate the branch, but their coefficient calculation is not stated there. The proof is therefore marked `proof_origin.by = agent`. I also read the current main-20261015 `lem-trf-local-term-locality.md`, the chapter and unit records, the parent coefficient branch, and the existing free-module definition. This does not change the locality unit or its route. There are no new-node sources to check and no SGA source is used.

The live DAG was searched by convolution, bounded weight, maximal decomposition, finite boxes and the relevant declaration names. The whole blueprint was searched with `blueprint_refs.py search` for convolution, monoid, positive monoid, and decomposition length; the latter two return no match. The broader hits concern Fourier/Day convolution and toric/formal-monoid definitions, not this assertion. The positive-monoid parent and completion nodes are downstream users, not permissible proof citations here. `blueprint_refs.py ancestor` confirms `lem-trf-local-term-locality`.

All eight new Mathlib search records were taken from this sandbox's actual msearch log, retaining tool and exact query text; the pre-existing records are retained. Both semantic phrasings and both Loogle patterns were read. I checked `Finsupp.finite_of_nat_weight_le` at `Data/Finsupp/Weight.lean:189` and its coordinate bound at line 134, the finite-support definition of `AddMonoidAlgebra` at `Algebra/MonoidAlgebra/Defs.lean:60`, the ordered-support convolution formula in `RingTheory/HahnSeries/Multiplication.lean:402`, and the analogous finite-sum associativity calculation in `RingTheory/MvPowerSeries/Basic.lean:286`. These do not state the item for all families over an arbitrary possibly nonfree lattice submonoid. Their elementary coordinate and finite-sum arguments are supplied explicitly, rather than creating unnecessary helper nodes. All search services used in this attempt returned results.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish. The parent finite-pattern and completion assertions assume or use the present elementary facts; citing them here would be circular.

## Review by Q53

I checked each step against delivery-errors B--E with the item and source open. Every proof step is a short elementary argument and none imports a non-elementary theorem or another node's proof. For C4, there are no proof citations to overread, and `citations.json` is consequently empty. The statement's single definition citation really defines free modules by existence of a basis; the finite-rank condition is stated separately in the item. The proof uses only the explicitly assumed ambient group, finite list of generators and positive integral weight. Freeness and finite rank are allowed extra hypotheses, not hidden inputs.

Step 1 uses exactly positivity at nonzero monoid elements and additivity of the weight: integer positivity gives weight at least one. Step 2 explicitly makes the bounded set of lengths nonempty, then takes the largest of its finitely many members, including the empty decomposition for zero. Neither step cites a node or assumes attainment in advance. Step 3 uses the definition of generation to write nonnegative generator coefficients, bounds each coordinate by M, and counts the finite box; it does not assume unique generator expressions. Step 4 separately bounds the generator coordinates by the attained maximal length, proving finiteness of S_n even though its weight upper bound was not assumed. These are complete finite-set arguments, not postponed lemmas.

Step 5 uses the already proved nonnegative weights and finite sublevel set, and embeds pairs and triples in its finite square and cube. Step 6 defines all operations on the literal family set and verifies additive inverses, the additive laws, both distributive laws and zero multiplication coefficientwise; it states why finite-sum expansion is elementary induction. Step 7 gives the exact swap bijection for commutativity and the sole surviving pair for the unit. Step 8 explicitly writes both nested sums and their bijections, with inverse formulas, to the same finite triple set; associativity in A identifies their summands. Thus it hides no infinite rearrangement or comparison theorem. None of these steps cites a DAG statement or uses an assumed convolution ring structure.

Step 9 computes the delta coefficients, constant homomorphism laws and the single-coefficient family explicitly. Step 10 computes the shift coefficient and uses only cancellation in the assumed group to prove uniqueness. All ten steps are below 2000 characters (maximum 615), and none is an inline non-elementary lemma in disguise. A new node for a finite box, a finite maximum, or reindexing the displayed finite sums would be one of the elementary-node faults B/D warn against. No clause has been outsourced to a new node, and proof_deps is exactly the empty union of all uses.

I tested the small cases P={0} (s=0 and rank zero), n=1 (S_1={0}), M=0 (only exponent zero), the zero coefficient ring, and coefficient rings with zero divisors. For the nonfree monoid generated by 2 and 3 in Z, nu(6)=3 while 6 also has a two-term decomposition, and S_2={0,2,3}; the box proof does not identify exponent vectors with monoid elements. Redundant or repeated generators likewise cause no problem because only images of finite boxes are used. A positive weight may have a kernel on the ambient lattice: the proof uses strict positivity only on P minus zero. At p=0 positivity forces every summand to be zero, so the unit and constant calculations include that endpoint. An exponent outside s_0+P has zero shifted coefficient, and a residual exponent inside it is unique by cancellation. Arbitrary coefficients cause no convergence issue: all coefficient sums are finite. No source correction or statement dispute was necessary.
