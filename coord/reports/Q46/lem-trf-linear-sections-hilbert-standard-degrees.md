## Worker report

Delivered module: `Sheaf.RingTheory.LinearSectionsHilbertStandardDegrees`.
Main declaration: `Hironaka.linearSectionsHilbertStandardDegrees`.
The statement has one postponed proof, `by sorry`. Its docstring gives all ten
steps of the node's proof. The five auxiliary declarations have concrete data:
`linearSectionIdeal`, `linearSectionRing`, `linearSectionMaximalIdeal`,
`linearSectionGradedMap`, and `linearSectionInitialQuotient`.
The returned H2 ownership fault is repaired by one existing:true definition-only
node and explicit citation of the two landed numerical-definition owners. No
mathematical statement correction or disputed statement is needed.

Source checked: Hironaka, Certain numerical characters of singularities (1970),
Propositions 5--6 on printed pp.157--159, Lemma 7 on p.160, and the first part of
Remark (12.2) on p.167. The online PDF named by the node was opened and these
passages read. The definition of the initial ideal and the padded degree sequence
was checked on pp.154--155. The current blueprint ancestor and unit under
`literature/blueprint/latest/` were also read; this is a supporting refinement,
not a unit statement.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- The arbitrary nonzero commutative regular local ring V is
  `{V : Type u} [CommRing V] [IsRegularLocalRing V]`. Mathlib's regular-local
  class includes the local and Noetherian structures; a local ring is nontrivial.
  The residue field used by `nuStar` is literally `V / maximalIdeal V`.
- `q : ℕ` includes q = 0. The family `x : Fin q → maximalIdeal V` gives the
  displayed parameters as elements of V with their maximal-ideal membership.
  `hx` gives an actual list `t` satisfying the dependency's
  `IsLocalRing.IsRegularSystemOfParameters t`, an injection
  `positions : Fin q ↪ Fin t.length`, and `t.get (positions i) = (x i).val`.
  Thus the positions are distinct, arbitrary, and retain the given order. This
  neither assumes they are an initial segment nor assumes the parameter list
  has pairwise distinct values beyond the source's requirements.
- `b : Ideal V` and `hb : b ≤ maximalIdeal V` are exactly the ideal hypothesis.
- `linearSectionIdeal x` is the span of the parameter values;
  `linearSectionRing x` is the actual quotient V/(x).
  The displayed bar-b is `b.map (Ideal.Quotient.mk (linearSectionIdeal x))`.
  D and F occur as the actual quotient rings inside `quotientHilbertFunction`.
- `linearSectionMaximalIdeal x` is the image of the original maximal ideal.
  Because the parameter ideal lies in that maximal ideal, this is precisely
  the induced maximal ideal of bar-V. There is no separately supplied local
  structure or hypothesis on any quotient.
- The conclusion `∃ hregular : IsRegularLocalRing (linearSectionRing x), ...`
  asserts the regular-local conclusion and supplies its induced local structure
  for the final `nuStar`. This is an output, never an extra input hypothesis.
- `quotientHilbertFunction l c n` is the already published
  `(Module.length (W/c) ((W/c)/(l.map mk)^(n+1))).toNat`.
  In these Noetherian local quotients the truncations have finite length, so
  conversion to Nat loses no information. Thus this gives exactly h_D and h_F.
- Inclusive summation is the existing `AlgebraicGeometry.HilbertSamuel.summation`;
  its function iterate `summation^[q]` gives Λ^q. The first conjunct quantifies
  over every `n : ℕ` and uses the pointwise natural-number inequality. It is
  not the lexicographic Hilbert--Samuel ordering.
- The equality hypothesis is equality of the whole functions,
  `quotientHilbertFunction ... = (summation^[q]) (...)`.
- E is the published `Hironaka.adicInitialIdeal l b`, whose degree-d classes
  come from b intersect l^d, equivalently the kernel in the node. No new
  initial-ideal definition is introduced.
- The degree-one classes are inlined as `DirectSum.of ... 1
  (Submodule.Quotient.mk ⟨(x i).val, ...⟩)`, using the canonical class of x_i
  modulo l² in the degree-one summand. No theorem-owned linearForm is used. `linearSectionInitialQuotient` is
  literally E divided by `(Ideal.span (range x*)) • (⊤ : Submodule S E)`,
  where S is gr_l V. Thus the denominator is (x*)E, not E intersect (x*)S.
- The equality conclusion supplies an additive equivalence from this module
  quotient to the actual initial ideal in gr_(l bar-V) bar-V. For EVERY a in E,
  the value of its quotient class must equal `linearSectionGradedMap x a.val`.
  This map is the existing associated-graded map for the actual quotient ring
  homomorphism. Hence the equivalence is induced by the quotient map, not an
  arbitrary isomorphism. Scalar compatibility is also stated explicitly:
  `e [s • a] = grMap s * e [a]` in the ambient target graded ring. Together
  with additivity, this is the module isomorphism over the original tangent
  ring; the representative formula gives its degree preservation because
  `Ideal.associatedGradedMap` is the direct sum of degree-preserving piece maps.
  Surjectivity and injectivity are part of `≃+`, and no map is chosen by a
  definition from a mere existence theorem.
- For every `m`, family `ξ : Fin m → gr_l V`, and degree function `d`,
  `IsMinimalGeneratingFamily E ξ` means generation and irredundance, and
  `HasDegrees l d ξ` means membership in each specified homogeneous summand.
  The next conclusion uses exactly the images `fun i ↦ grMap x (ξ i)` with
  both predicates and the SAME d. Minimality excludes zero generators, so
  this asserts their exact degrees, not merely homogeneity of possibly zero
  elements. Every finite minimal generating family is covered; all such
  families are finite here because the tangent ring is Noetherian.
- The final conclusion is `nuStar b = @nuStar ... hregular.toIsLocalRing bar-b`.
  This reuses the published multiplicities
  `dim E_d / sum_{j=1}^d S_j E_(d-j)` and the increasing enumeration padded
  with infinity. It does not replace the sequence by a finite list.

Dependency declarations read and used:

- `def-weil-regular-scheme`: its retained Mathlib ring match is
  `IsRegularLocalRing` (`Mathlib.RingTheory.RegularLocalRing.Defs`). The newer
  `Sheaf.AlgebraicGeometry.IsRegularScheme` declaration was read; it implements
  the scheme clause and does not replace the node's retained ring clauses.
- `def-weil-pbc-associated-graded-ring`:
  `Ideal.associatedGraded`, `Ideal.associatedGradedPiece`, their ring/module
  structures, and canonical summand inclusions, from
  `WeilConjectures.RingTheory.AssociatedGradedRing` (publicly imported).
- `def-weil-pbc-module-length`: Mathlib `Module.length` in
  `Mathlib.RingTheory.Length`, used by `quotientHilbertFunction`.
- `def-weil-pbc-mv-polynomial-ring`: Mathlib `MvPolynomial`, `MvPolynomial.aeval`,
  and `MvPolynomial.algHom_ext` were read. No polynomial presentation has to be
  chosen in the statement: it uses the intrinsic associated graded ring.
- `def-pc-standard-graded-algebra`: `GradedAlgebra.IsStandard` and its docstring
  in `WeilConjectures.RingTheory.GradedAlgebra.Standard` were read; the finite
  graded-generation notion underlies the published generator multiplicities.
- `def-weil-pbc-regular-system-of-parameters`:
  `IsLocalRing.IsRegularSystemOfParameters` from
  `WeilConjectures.RingTheory.IsRegularSystemOfParameters`, used verbatim in hx.
- The following definition nodes are added to stmt_deps, as authorized:
  `def-trf-local-standard-basis-invariants` supplies
  `Hironaka.IsMinimalGeneratingFamily` and `Hironaka.HasDegrees`;
  `def-trf-hilbert-samuel-invariant` supplies
  `AlgebraicGeometry.HilbertSamuel.summation`;
  the NEW `def-trf-ideal-preserving-associated-graded-maps` supplies
  `Ideal.powerQuotientMap`, `Ideal.associatedGradedPieceMap` and
  `Ideal.associatedGradedMap` in `Sheaf.RingTheory.FormallyEtaleAssociatedGraded`;
  the theorem node `lem-sfb-augmented-etale-associated-graded` is dropped.
  The existing owners `def-trf-local-quotient-hilbert-function` and
  `def-trf-adic-initial-ideal-generator-degrees` are cited for the numerical
  definitions used below.
- Reused concrete helper definitions from
  `Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees` are `adicInitialIdeal`,
  `quotientHilbertFunction`, `nuStar` and their graded-multiplicity helpers.
  Its projective-cone COMPARISON THEOREM is not a prerequisite or used here;
  it is downstream via the simple-residue-extension comparison. In particular,
  no cyclic DAG dependency on that downstream theorem has been added merely
  to cite its reusable definitions. The `GradedNormalizationFractionMap` import is removed altogether; the
  degree-one representative is inlined directly in the relation submodule.
- The stated proof dependency
  `IsRegularLocalRing.isRegular_and_quotients_of_generators` is privately
  imported from `WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence`.
  Its full signature and docstring were read. The quotient-local-structure,
  Noetherian-image, and length-additivity matches are Mathlib declarations.
  The maximal-adic length bridge and regular-hypersurface initial-form nodes
  currently have no Lean record; their proof imports are therefore absent.

Edge cases checked against the constructions:

- q = 0: the parameter span is zero, the relation ideal on E is zero, and
  the canonical quotient maps are the identity after the usual V/(0) identification.
  The summation iterate is the zeroth iterate.
- V a field: its parameter list is empty; hx excludes q > 0 without imposing
  an additional dimension hypothesis, and b ≤ 0 forces b = 0.
- b = 0: E = 0; the minimal generating family is empty, every e is the
  zero-module equivalence, and both nuStar sequences consist entirely of infinity.
- b equal to the maximal ideal: the quotients remain nonzero. For a nonempty
  section the equality premise generally fails; it has not been assumed.
- A full regular system as the selected family gives a field as bar-V and is
  included. Unsorted and repeated generator degrees are retained, as are m = 0
  and n = 0. No characteristic, coefficient-field or completeness assumption
  is present, so mixed characteristic is included.

Searches performed before writing:

- `msearch.py leanfinder`, query "quotient by regular parameters Hilbert Samuel
  bound equality preserves degrees minimal homogeneous generators": 8 hits,
  including `Module.supportDim_add_length_eq_supportDim_of_isRegular` and
  homogeneous localization/polynomial order results; no statement match.
- `msearch.py loogle`, query "Ideal.associatedGraded, Module.length,
  IsRegularLocalRing": no hits; the service does not index the project's
  `Ideal.associatedGraded`. Its actual source was inspected directly.
- `msearch.py leansearch`, query "Hilbert Samuel inequality quotient by regular
  system of parameters equality initial ideal generators": 8 hits concerning
  homogeneous cores and ideals, not this comparison theorem.
- `msearch.py grep`, query
  `hilbertSamuel|standardDegrees|tangentIdeal|associatedGradedMap` in RingTheory:
  18 Mathlib hits about cotangent ideals and Kaehler differentials; no match.
- `rg` of the same names plus `nuStar` and `hilbertFunction` in both the live
  `lean/WeilConjectures` and `lean/Sheaf` found the existing Hironaka numerical
  definitions and canonical graded-map API, which are reused. Search for the
  item id in `lean/WeilConjectures` found no existing declaration.
- Further `rg` for minimal homogeneous generators found
  `LocalStandardBasisInvariants` (used); search for degree-one initial forms
  found `GradedNormalization.linearForm` (inlined after the return, so its
  owning comparison theorem is no longer imported).
  The six new declaration names were searched across Mathlib, WeilConjectures
  and Sheaf without any existing match.

Validation: the prescribed scompile.py compiled the module in sandbox and actual
module-name modes with no error or warning. All universes and variables are
explicit, every declaration has a source/blueprint docstring, and only the main
theorem contains sorry. The node's lean.statement is the exact multiline
signature from the theorem keyword through its result, excluding `:=`.

## Second reading by Q46

No independent worker reading: this assignment explicitly prohibits starting
other agents and specifies direct delivery followed by the maintainer's
independent review. A second self-audit compared the node and final Lean clause
by clause as above. It checked the relation submodule (x*)E rather than an
intersection, the actual representative formula, the output local structure,
arbitrary distinct parameter positions, universal minimal-family clause,
pointwise bound, and the infinity tail. After the return it checked that the inlined degree-one class is precisely
the former linearForm value, and that the theorem signature is unchanged.


## Returned delivery repair

Return L at immutable head `968a7b6e74ff`, H2, is repaired as follows:

1. Replaced the theorem statement-dependency
   `lem-sfb-augmented-etale-associated-graded` with the definition-only node
   `def-trf-ideal-preserving-associated-graded-maps`. Its existing:true record
   owns precisely the three plain canonical map definitions in the published
   module, without claiming the formal-etale isomorphism theorem. All three
   definition bodies and their signatures were read. The new node states only
   their actual construction, including semilinearity of the piece map and
   additivity of the direct-sum map.
2. Removed `Sheaf.RingTheory.GradedNormalizationFractionMap`. Inlined the
   degree-one class as `DirectSum.of ... 1 (Submodule.Quotient.mk ⟨x_i, ...⟩)`
   in `linearSectionInitialQuotient`, as the return explicitly permits.
3. Added the existing definition owners
   `def-trf-local-quotient-hilbert-function` and
   `def-trf-adic-initial-ideal-generator-degrees` to stmt_deps. Their records
   and the unchanged source definitions were read against the current main.
4. Reconstructed the item node from the current main node (which has no Lean
   record), retaining its statement, proof, proof_deps and other fields verbatim.
   The returned sandbox theorem signature is unchanged; only the helper body
   and import changed. The delivery wrapper supplies a fresh commit on current
   main rather than an unchanged re-push of the returned head.

Maintainer advisories: the two inherited unused stmt_deps for mv-polynomial and
standard-graded remain unchanged, since no mathematical statement correction is
required. The published numerical definitions still reside in
`ProjectiveConeHilbertStandardDegrees`; both newly cited landed owner records
point there. Consequently a future stage-3 proof import of simple-residue by
that existing module would close the reported cycle. The repair follows the
requested existing:true ownership pattern and does not move, copy, or edit the
published definitions. This source-module extraction remains a maintenance
advisory, independent of the repaired DAG statement-dependency ownership.

## New nodes

`def-trf-ideal-preserving-associated-graded-maps`: definition-only ownership of
`Ideal.powerQuotientMap`, `Ideal.associatedGradedPieceMap`, and
`Ideal.associatedGradedMap`, all existing in
`Sheaf.RingTheory.FormallyEtaleAssociatedGraded`. For arbitrary commutative rings
and an ideal-preserving ring homomorphism, these are the representative maps
on power quotients, successive power quotients, and their direct sum. Source:
Stacks 0H1D's natural maps, read in `literature/stacks-project/algebra.tex`.
No formal-etale assumption or isomorphism claim is included. New LeanSearch,
LeanFinder and Mathlib grep searches are recorded with their exact output in
the node. Project and DAG searches found the plain existing definitions but no
definition-only owner. No module, duplicate definition, or proof is delivered
for this existing:true node. The statement cites the quotient-ring,
quotient-module, associated-graded-ring and direct-sum definition nodes it uses.
The boundary cases n=0, zero ideals, zero rings, independent universes and
arbitrary non-surjective f are included by the recorded signatures.
