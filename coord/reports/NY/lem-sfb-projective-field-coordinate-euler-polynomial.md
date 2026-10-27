## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveFieldCoordinateEulerPolynomial` states
`AlgebraicGeometry.exists_projectiveField_coordinateEulerPolynomial`, with its sole proof
`sorry`. It introduces no definition and no new mathematical assumptions.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| n >= 0 | `(n : ℕ)`; zero is included |
| A scheme X | `{X : Scheme.{u}}` |
| Closed immersion into Proj(k[z_0,...,z_n]) | `i : X ⟶ Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) k`, `[IsClosedImmersion i]` |
| O_X(d) = i^* O_P(d), for integer d | `(Scheme.Modules.tensorPullback i).obj (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k) d)` |
| X proper over k | `IsProper (i ≫ Proj.projectiveSpaceOverAffineToSpec ... k)` |
| X Noetherian, meaning quasi-compact and locally Noetherian | `IsNoetherian X`, the Mathlib class extending `IsLocallyNoetherian X` and `CompactSpace X` |
| O_X coherent | `RingedSpace.IsCoherent X.toRingedSpace (SheafOfModules.unit X.ringCatSheaf)` |
| A rational polynomial Q_X | `∃ Q : Polynomial ℚ` |
| Euler equality at every integer | First conjunct `∀ d : ℤ, Q.eval (d : ℚ) = (@Scheme.Modules.eulerChar ... (tensorPullback i ... ) : ℚ)` |
| Unique with those Euler values | Second conjunct quantifies over every `R : Polynomial ℚ`, assumes those same equalities for every integer, and concludes `R = Q` |
| Numerical at all integers | `∀ d : ℤ, ∃ z : ℤ, Q.eval (d : ℚ) = (z : ℚ)` |
| Existence of a homogeneous defining ideal | Existential `J : HomogeneousIdeal ...` and `e : Proj (coordinateQuotientPiece J) ≅ X` satisfying `e.hom ≫ i = coordinateQuotientImmersion J` |
| Every such ideal, as the same closed subscheme of the fixed P | Universal `J` with the same existential isomorphism over P; this is scheme-theoretic identification, not equality of point sets |
| Quotient grading | `coordinateQuotientPiece J`, with the public `coordinateQuotientGrading` instance |
| Eventual equality with coordinate dimensions | `∃ b : ℕ, ∀ d : ℕ, b ≤ d → Q.eval (d : ℚ) = (Module.finrank k (coordinateQuotientPiece J d) : ℚ)` |
| Unique rational polynomial with that eventual equality | For every such J and every R, its own eventual equality implies `R = Q` |
| Unsaturated ideals, unit ideal, empty X allowed | No saturation, proper-ideal, nontrivial-quotient, reducedness or nonempty hypothesis occurs |

The `ULift` coordinate indices are in bijection with Fin(n+1); they permit the polynomial
ring, the projective spectrum, X and module sheaves to share the same arbitrary universe u.
This changes no geometric input. The k-structure is the composite of the given immersion
with the polynomial-Proj structure map. The Euler function is explicitly supplied
`OverClass.ofHom` of this composite, so no unrelated structure morphism is assumed.

Recorded dependency declarations read and used:

- `Field` (Mathlib.Algebra.Field.Defs); `AlgebraicGeometry.Scheme` and its Hom
  (Mathlib.AlgebraicGeometry.Scheme).
- `AlgebraicGeometry.IsClosedImmersion`
  (Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion).
- `AlgebraicGeometry.Proj` (Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme),
  used through the real polynomial specialization `Proj.projectiveSpaceOverAffine` and
  `Proj.projectiveSpaceOverAffineToSpec` (WeilConjectures.AlgebraicGeometry.ProjectiveSpace).
- `AlgebraicGeometry.ProjectiveSpace.twist`
  (WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist) is the base-change model's twist.
  For the actual polynomial Proj the statement uses the existing `AlgebraicGeometry.Proj.twist`
  (WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules). Its locally homogeneous
  fractions on degree-one charts give exactly the bases and transitions of the node, for all
  integers. No second twist is defined. Its existing definition node
  `def-weil-pbc-proj-twisting-sheaf` is added to stmt_deps and its module publicly imported.
- `AlgebraicGeometry.Scheme.Modules.tensorPullback` exposed by the recorded
  Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction module; its source definition in
  WeilConjectures.AlgebraicGeometry.TensorPullback is inverse image followed by change of rings.
  No adjunction witness is needed in this signature.
- `AlgebraicGeometry.IsProper` (Mathlib.AlgebraicGeometry.Morphisms.Proper),
  `AlgebraicGeometry.IsLocallyNoetherian` and `AlgebraicGeometry.IsNoetherian`
  (Mathlib.AlgebraicGeometry.Noetherian).
- `AlgebraicGeometry.RingedSpace.IsCoherent`, exposed by the recorded
  Sheaf.AlgebraicGeometry.CoherentFiniteType module. The exact coherence predicate is used,
  rather than the weaker IsQuasiCoherentFiniteType conjunction.
- `AlgebraicGeometry.Scheme.Modules.eulerChar`
  (WeilConjectures.AlgebraicGeometry.Cohomology.Defs): the recorded integer-valued alternating
  cohomology-dimension sum. This follows the node's accepted Euler interface.
- `AlgebraicGeometry.coordinateQuotientPiece` and `coordinateQuotientGrading`
  (Sheaf.RingTheory.CoordinateQuotientGrading).
- `AlgebraicGeometry.coordinateQuotientImmersion`
  (Sheaf.AlgebraicGeometry.ProjectiveCoordinateRingEulerPolynomial), induced by the actual
  quotient graded homomorphism, not an arbitrary immersion. The new definition node
  `def-sfb-coordinate-quotient-immersion` references these existing declarations in stmt_deps.
  Their module is public; its Euler-polynomial theorem stays exclusively in proof_deps.

The remaining recorded proof dependencies are imported with plain `import`: projective
morphisms, invertible modules, affine Proj scalar extension, Snapper's theorem, homogeneous
ideal presentation, twist/Euler uniqueness, coherence over locally Noetherian schemes and
polynomial scalar extension. Properness and finite-type-over-Noetherian preparation are
available through the already public proper/Noetherian modules. All seven natural-language
proof steps are included in the theorem docstring, naming their DAG prerequisites.

Sources opened: literature/stacks-project/varieties.tex, lemma-numerical-polynomial-from-euler
(Tag 0BEM, r=1 and F=O_X), lemma-hilbert-polynomial-H0 (08AE);
constructions.tex lemma-closed-in-projective-space (03GL); coherent.tex
lemma-recover-tail-graded-module (0AG7). These give respectively the all-integer Euler
polynomial, the eventual section comparison, the homogeneous ideal presentation, and
recovery of the tail for the actual quotient graded ring.

Edge checks before and after writing: n=0 is P^0; negative d remains an integer and never
passes through Int.toNat; d=0 is the structure-sheaf twist; arbitrary characteristic and
arbitrary fields are allowed. J=(1) gives the zero quotient and empty Proj, without requiring
that quotient to be a field or nontrivial ring. Other irrelevant/unsaturated ideals may also
have empty Proj with nonzero low-degree pieces: only eventual coordinate equality is claimed.
For the empty X the Euler function and resulting polynomial are zero; no explicit extra
empty-case conclusion is added. Distinct eventual bounds for candidate polynomials are
allowed. Uniqueness is explicitly from Euler values alone and, separately, from coordinate
values alone, rather than uniqueness only among polynomials satisfying all clauses.

Searches made with the prescribed msearch.py wrapper:

- LeanFinder: "A projective closed subscheme over a field has a unique numerical polynomial
  for all integer Euler characteristics, agreeing eventually with every homogeneous coordinate
  quotient dimension". Eight hits: basic Proj, its extensionality and properness; no match.
- Loogle: `"hilbertPoly"`. Twelve hits in Mathlib.RingTheory.Polynomial.HilbertPoly,
  including preHilbertPoly and hilbertPoly; these do not assert this projective-scheme theorem.
- LeanSearch: "A unique rational polynomial gives the Euler characteristic of every integer
  twist of a projective closed subscheme over a field". Eight hits, incidence-algebra Euler
  characteristic, cyclotomic polynomials, rational functions and elliptic curves; no match.
- Mathlib grep: `eulerChar|numericalPolynomial|HilbertPolynomial`, AlgebraicGeometry:
  zero hits.
- rg of lean/WeilConjectures and lean/Sheaf:
  `coordinate.*[Pp]olynomial|[Ff]ield.*[Ee]uler|exists.*hilbert|` followed by the item id.
  Found the recorded quotient/Euler theorem, twist/Euler uniqueness, and
  FlatProjectiveHilbertPolynomialLocality.projective_field_hilbert_polynomial. The last
  uses the base-change model and a different coordinate-polynomial predicate, adds degree
  and empty-locus conclusions, and does not supply this node's properness/coherence or
  explicit every-defining-ideal comparison. It is not an exact declaration for this node.
- rg of the item id in lean/WeilConjectures: no hits. rg of `projectiveClosedTwist` and
  `coordinateQuotientImmersion` in dag/lean_names_upstream.json: no upstream duplicate entry.
- Checked the new full theorem name in the source trees; no existing declaration found.

No mathematical statement correction, dependency-module repair or STATEMENT-DISPUTED issue
was needed. The H2 return is repaired by adding a definition node for already existing
quotient-map constructions. The item changes only lean and stmt_deps: add the existing Proj
twist definition and the new quotient-immersion definition. Its source statement, proof,
proof_deps and other fields are preserved, rebased on the current shared main node.

Validation: scompile.py compiled the actual module separately, both sandbox and library
names, cleanly (2.7 seconds each). No local/global build or direct repository edit was run.

## Second reading by NY

Dispatcher-worker rereading with both the original node and the delivered module open;
this is not a claim of an independent second worker. The prompt assigns independent review
to the maintainer and forbids starting other agents.

Checked the field and closed-immersion binders against the node; the target is the actual
polynomial Proj. Read the source of Proj.twist, tensorPullback, eulerChar, IsCoherent,
coordinateQuotientPiece and coordinateQuotientImmersion to check the objects, rather than
relying on their names. Confirmed the structure morphism used for properness is exactly the
one supplied to Euler characteristic. Both Euler equality clauses quantify over ℤ, both
coordinate eventuality clauses over ℕ. The numerical clause asserts existence of an integer
value, not integer coefficients. The ideal existence clause and the universal ideal clause
both require equality over the fixed ambient P. Both uniqueness conclusions have the
orientation R=Q and use only the values specified by the corresponding node clause.
No extra hypothesis, omitted clause, private definition, file-local notation, instance,
implicit variable or change of the node's mathematical statement was found. The mathematical statement required no change. The H2 rereading below repairs its dependency
classification. The precise module-mode compiler passed before delivery checks.

## New nodes

`def-sfb-coordinate-quotient-immersion` names the actual graded quotient homomorphism
`AlgebraicGeometry.coordinateQuotientGradedMap` and its induced Proj morphism
`AlgebraicGeometry.coordinateQuotientImmersion`. Source: Stacks constructions.tex Tag 01N0,
with the coordinate application at Tag 03GL and the quotient grading at Tag 00JL. The node
has `existing: true` and references Sheaf.AlgebraicGeometry.ProjectiveCoordinateRingEulerPolynomial;
there is no new module, copied declaration or construction. LeanSearch and LeanFinder return
general quotient/Proj/chart primitives. Mathlib grep finds no specialized name; upstream
grep finds none; Sheaf grep finds these two exact definitions; a full DAG declaration-owner
search finds only their theorem owner, not a definition node. blueprint_refs.py search finds
zero matching blueprint nodes and ancestor returns None, retained in the new node. Actual
search outputs are recorded in its mathlib_searches. The graded map is literally the quotient
ring map with `Submodule.mem_map_of_mem` supplying degree preservation. The Proj map uses
`GradedRingHom.irrelevant_le_map_of_surjective (Ideal.Quotient.mk_surjective)` for its domain
condition. No data is chosen from the Euler theorem; no saturation, proper-ideal or nonempty
condition is introduced. The new node cites exactly its field, quotient-grading, scheme and
Proj definitions, and is cited by the item.

## Returned delivery repair

H2 at immutable head 20932675af92: removed
`lem-sfb-projective-coordinate-ring-euler-polynomial` from the item's stmt_deps and added
`def-sfb-coordinate-quotient-immersion` in its place. The theorem remains in proof_deps and
in proof step 6. The new definition node has existing:true on the same landed module and
records both plain definitions, exactly as requested. The item's Lean file and Lean signature
are byte-identical to the returned version. The current shared main item has no lean record;
comparison with the retained returned item finds only lean and stmt_deps differ. This repair
rebuilds the item's metadata on that current main version, retaining only those authorized
deltas. deliver2.py performs the authorized refreshed-base delivery bookkeeping.

Advisory A1 considered: no mathematical correction is necessary. On the actual polynomial
Proj the source's O(d) is the already recorded Proj.twist; its degree-one chart basis has
transition (z_i/z_j)^d for every integer, exactly the chart definition in
`def-pc-projective-space-twist`. Original proof step 3 already explains this identification,
including d=0 and negative d, and the theorem docstring records it. The Proj twist definition
is explicitly retained in stmt_deps. We preserve the source statement and the Lean file as
the return permits; no silent change to either twist construction or Euler function is made.

Repair rereading by NY: opened the new node and both existing definition bodies. The node's
q_J is the same `Ideal.Quotient.mk J.toIdeal`, its A_m is coordinateQuotientPiece J, and its
j_J is the same `Proj.map` used by coordinateQuotientImmersion. The irrelevant-ideal proof
comes from quotient surjectivity, not the Euler-polynomial theorem. Its existing record
contains no file ownership, so the original module continues to belong to its original
node and no Lean declaration is duplicated. Checked that the item's theorem dependency
is absent from stmt_deps and present in proof_deps. All originally reviewed clause and edge
case correspondences remain unchanged. This is a dispatcher-worker rereading; independent
maintainer review is still required as in the original assignment.

Repair validation: the unchanged delivered Lean file compiled cleanly via scompile.py in
both sandbox and library modes (2.7 seconds each). Its SHA256 is
b06432120c893650817095950ba777d0bfaa2c3c70d3783c28d9fe4ce32d9c69.
