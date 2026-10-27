## Worker report

The item states Stacks dga.tex Tag 09K4, lemma-hom-into-shift-dual-free,
both displayed identifications, by the theorem
`CategoryTheory.DgAlgebra.shiftedCharacterDualHom` in
`Sheaf.CategoryTheory.DgShiftedCharacterDualHom`. Its proof is `sorry`.
The coordinate constructions in `Sheaf.CategoryTheory.DgCharacterDualCoordinates`
have real data; none uses a postponed existence theorem. The item's natural-language
statement, proof, proof dependencies and source are unchanged. Its statement dependencies
gain the new definition node described below.

Hypothesis and clause correspondence:

- The metatheoretic size convention is the universe-polymorphic `universe u`.
  Its recorded `lean.convention` has no importable declaration. I also read the
  audited `AlgebraicGeometry.ProEtale.ModuleDerivedCategory` and its universe docstring;
  that scheme-specific definition is not a hypothesis on these arbitrary DG algebras.
- The associative unital DG integer algebra is `A : Algebra.{u}`. This is the
  existing monoid object in integer cochain complexes over `ULift ℤ`, with no
  commutativity assumption. Multiplication being a chain map gives exactly Leibniz.
- All right DG modules are `M : RightModule A`; their action, square-zero
  differential and degree-zero maps use the existing `underlying`, `act`, and
  `regular` of `Sheaf.CategoryTheory.DgAlgebraDerivedCategory`. I read their complete
  signatures and docstrings, as well as `DerivedStructure`, `ShiftComparison`,
  and the existing action-preserving `homotopyRel` in DgAlgebraHomotopyStructure.
  No triangulation or HomotopyStructure instance is assumed.
- Every integer shift is the unrestricted `k : ℤ`; in the coordinate groups the
  target in degree p is `CharacterModule (A.X.X (-(p+k)))`. Its differential has
  sign `(p+1).negOnePow`, since (-1)^k(-1)^(p+k+1)=(-1)^(p+1).
  `characterDualLinear` pins the unchanged right action by exactly
  phi(m a)(b)=phi(m)(a b). Associativity uses `act A (regular A)` in that order.
- The dual of the underlying complex uses Mathlib's `CharacterModule`, namely
  additive maps into `AddCircle (1 : ℚ) = ℚ/ℤ`, not a finite or continuous dual.
  `characterDualDifferential C r s` is `(r+1).negOnePow` times
  `CharacterModule.dual (C.d (-s) (-r))`. At s=r+1 this is the node's formula.
  `characterDualCycles` is its kernel; `characterDualBoundaries` is the incoming
  range pulled back to that kernel; `CharacterDualCohomology` is their quotient.
- `characterDualMaps A M k` is precisely the degree-zero right-linear additive
  families satisfying the chain-map equation. It is a concrete coordinate
  presentation of Hom_DG(M,A-dual[k]); it neither chooses a replacement module
  nor assumes an arbitrary action. The null subgroup uses a degree-minus-one
  right-linear `h` with exactly f=d h+h d, so its quotient
  `CharacterDualHomotopyMaps` is the required Hom_K group. Subgroup closure does
  not enlarge the null maps: zero has the zero homotopy, and sums and negatives
  have the sum and negative homotopies. This is elementary, not an added axiom.
- `E` is the family of additive equivalences from those map groups to dual cycles;
  `F` is the family of additive equivalences from their homotopy quotient to H^k.
  Both are existentially asserted by a theorem, not selected as definition data.
- The first conjunct fixes E on every f and every `m : M.X (-k)` by evaluation
  at `characterDualUnit A`, with only an equality transport from degree 0.
  The unit is actually `(MonObj.one ...).f 0` applied to the integer 1 via the
  single-complex degree-zero isomorphism. It is not an arbitrary distinguished point.
- The second conjunct fixes F on every quotient representative to be the class
  of E(f). Thus evaluation, rather than an unspecified additive isomorphism,
  induces the cohomology equivalence, and every class is covered.
- The last conjunct gives contravariant naturality for every DG map `u : N ⟶ M`,
  with `g=f u` expressed in coordinates. No assumption is made that g has a
  special form beyond this equation. Such g exists by ordinary precomposition:
  u preserves both the action and differential. On quotient representatives the
  second conjunct then implies naturality of F under the induced dual map;
  precomposition sends h to h u and therefore respects the quotient relation.
  The E/F formulas uniquely determine the families, so their existential
  formulation is equivalent to specifying the canonical natural isomorphisms.
- There is no boundedness, acyclicity, nonzero, characteristic, finite generation,
  injectivity of ℚ/ℤ, or finiteness binder in the theorem.

Source and edge checks: read the discussion preceding 09K4 and its full statement
and proof ("clear from the discussion above"). Rechecked all six node proof steps.
For A=ℤ concentrated in zero and M in degree -k, the map group and cycles are
Hom(M^(-k),ℚ/ℤ); the quotient has no extra boundaries. M=0 and the zero algebra
produce zero groups. Both even and odd k give the shifted sign above, including
negative k. In a nonzero two-term complex, the chain equation becomes the dual
cycle condition and dh+hd gives the dual boundary with the (-1)^k correction
in the proof. Unbounded M is allowed because the coordinate object is a full
product over every integer, not a finite direct sum. Empty homogeneous pieces
cause no exception. The new null subgroup and dual-boundary constructions have
exactly the zero/sum/negative closure required of their quotient groups.

Searches actually run through msearch.py (recorded in searches.jsonl):

- leanfinder: "Evaluation identifies maps from a right differential graded module
  to the shifted character dual of a dg algebra with dual cohomology". Eight
  ordinary double/single-complex and Ext hits; no DG-algebra dual identification.
- loogle: `"CharacterModule", "HomComplex"`: zero hits.
- leansearch: "Character dual of a differential graded module and homotopy classes
  of maps into the character dual of its algebra": eight hits headed by
  CharacterModule.dual. Read CharacterModule's definition and dual/homEquiv:
  ordinary commutative-ring character-module duality, not this DG-linear statement.
- leanfinder: "Coordinate groups of chain maps into shifted character duals of a dg
  algebra with quotient by right linear homotopies": ordinary HomComplex and
  HomComplex.CohomologyClass.homAddEquiv, which do not impose a DG A action.
- grep Mathlib: `DGModule|DGAlgebra|DifferentialGraded|dual.*HomComplex` and
  `characterDual|CharacterDual|HomComplex.*dual|dual.*HomComplex`: zero hits.
- Project searches: `rg` in both lean/WeilConjectures and lean/Sheaf for
  CharacterDual/characterDual/character.dual and the item id; no exact match.
  Existing CharacterDualShiftProduct and CompleteDualFreeFiltration specify
  product coordinates on supplied DG modules, not the cycle/map/quotient groups.
- DAG searches: character dual, character-dual, CharacterDual, and 09K4;
  blueprint_refs.py searches "character dual", "dual free", and "09K4" all
  return zero blueprint matches. Ancestor prints None, inherited through the
  item's existing source-support chain, and retained in the new node metadata.

Validation: both modules compiled separately in dependency order against the
live published library using scompile.py; no errors or warnings. The only
postponed theorem is the item's `shiftedCharacterDualHom`.
No statement correction or STATEMENT-DISPUTED issue was found.

## New nodes

`def-sfb-dg-character-dual-coordinates` defines the missing concrete coordinate
presentation of shifted-dual cochains, right linearity, chain maps, null maps,
cycles, boundaries, dual cohomology, and the homotopy quotient, together with
the actual algebra unit used for evaluation. Its source is Stacks dga.tex,
the conventions before 09K4 and definition-homotopy. It builds on the existing
`def-sfb-dg-derived-category` rather than redefining DG algebras or modules.
The existing character-dual product interfaces do not supply any of these
groups; the Mathlib, project, DAG, and blueprint searches above found none.
All definitions use additive subgroups, equalizers, signed dual linear maps,
and actual additive quotients. It is one definition node for the coherent
coordinate presentation needed to state both clauses, with all declarations
listed in lean.declarations. The explicit equations leave no arbitrary maps,
actions, universal properties, or existence choices to fill in.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
