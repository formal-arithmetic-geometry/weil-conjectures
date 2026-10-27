## Worker report

The module `Sheaf.AlgebraicGeometry.LocalTorusSubgroupSpecialTrivial` states
`AlgebraicGeometry.isIso_unit_of_splitTorus_closed_specialFiber`, with one `sorry`
and no new definitions. The statement and accepted proof split are unchanged.
The module docstring and theorem docstring cite Conrad, Reductive group schemes,
Exercise 2.4.3(iii), printed p.76, and the torsion argument in Theorem B.3.2(2),
printed pp.289--290. The theorem docstring writes out all six accepted proof steps.

I read the node and each of its four statement dependencies, including their Lean
records, then the full signatures and docstrings in the recorded modules.
Conrad's online PDF was opened: Exercise 2.4.3(iii) explicitly considers possibly
non-flat finite K[n], proves all fibres trivial, and concludes the identity section
is an isomorphism. The node extracts this argument for any closed subgroup; the
accepted affine proof justifies that extraction without additional assumptions.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative Noetherian local ring is `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A]`. Mathlib's local-ring class includes
  nontriviality, as usual for a local ring with maximal ideal m.
- The base S is `Spec (.of A)`, using the recorded affine-spectrum declaration.
  The residue field k = A/m is `IsLocalRing.ResidueField A`, and its quotient map
  is `IsLocalRing.residue A`. The actual morphism Spec k -> Spec A is
  `Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))`.
- Every rank, including zero, is covered by `(r : ℕ)`.
- The specified Laurent torus is `RingGroupSchemes.splitTorus A r`. Its owning
  definition node `def-sfb-split-torus-over-ring` has already landed and is added
  to `stmt_deps`, with no new node. I read its source: the multiplicative factor is
  `Spec (LaurentPolynomial A)` with Mathlib's canonical Hopf group law; splitTorus
  is the iterated cartesian product, with the tensor unit for rank zero. In a
  product the coordinate algebra is the tensor product of the Laurent factors.
  Identifying each factor's z and z^-1 with x_i and y_i gives exactly the displayed
  quotient A[x_i,y_i]/(x_i*y_i-1). Each generator is group-like, has counit 1,
  and inverse z^-1. Conversely Laurent monomials give the inverse presentation
  map; thus this is precisely the specified torus with all three operations.
- An arbitrary S-group scheme, with all group-object diagrams, is
  `(K : Grp (Over (Spec (.of A))))`; this uses Mathlib's bundled group object,
  whose `GrpObj` instance carries multiplication, unit, inverse and their laws.
- The S-group homomorphism is `(j : K ⟶ RingGroupSchemes.splitTorus A r)`.
  Bundled morphisms in `Grp` preserve the group law, hence unit and inverse.
  Its underlying scheme morphism is `j.hom.hom.left`. Its closed-immersion
  hypothesis is `[IsClosedImmersion j.hom.hom.left]`, exactly the recorded
  declaration for `def-weil-closed-immersion`. No extra finiteness, flatness,
  separatedness, reducedness, or smoothness hypothesis on K is imposed.
- The group scheme K_k is `(Over.pullback (Spec.map
  (CommRingCat.ofHom (IsLocalRing.residue A)))).mapGrp.obj K`. `Over.pullback`
  uses the scheme fibre product; `mapGrp` equips that very pullback with its
  induced group law. Its `.X` is the resulting scheme over Spec k.
- The identity section Spec k -> K_k is `(η[(...mapGrp.obj K).X]).left`.
  Here the tensor unit in `Over (Spec k)` has underlying scheme Spec k.
  `hspecial : IsIso (...)` therefore states exactly the node's hypothesis on
  that actual section, and includes the scheme structure, not only points.
- The conclusion `IsIso (η[K.X]).left` asserts that the actual identity section
  S -> K is an isomorphism. It does not merely choose an unrelated isomorphism.
- Neither flatness nor completeness is assumed anywhere in the signature.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded
  scheme/morphism/section base-change conventions; its documentation explicitly
  directs consumers to `Over.pullback` for schemes, not `moduleBaseChange`.
  `CategoryTheory.Over.pullback` and its `mapGrp` implement the canonical
  base change here; the induced unit is its canonical identity section.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`:
  `AlgebraicGeometry.RingGroupSchemes.splitTorus` and its multiplicative factor.
- `Mathlib.RingTheory.LocalRing.ResidueField.Defs`: `IsLocalRing.residue`,
  `IsLocalRing.ResidueField`.
- The already available proof inputs are imported privately: affine-spectrum
  pullbacks, Nakayama, localization at primes, algebraic closures, the finitely
  generated abelian-group structure theorem, field-extension tensor injection,
  and module localization. Closed-immersion base change is in its public module.
  `lem-sfb-split-torus-subgroups-diagonalizable` currently has neither a usable
  Lean record nor Mathlib match and is a proof input only; no import is invented.

Edge cases checked before writing:

- r = 0: the existing definition is the trivial group; a closed subgroup with
  an identity section is trivial. The statement allows this rank without a
  positive-rank assumption.
- A a field: the quotient to its residue field is an isomorphism; the hypothesis
  is precisely triviality of the whole group, as required.
- A nonreduced Noetherian local ring is allowed; no domain or reducedness class
  occurs. No completeness or henselian hypothesis occurs either.
- Characteristic p is unrestricted. In particular mu_p over a characteristic-p
  field is not a false positive: it can have one geometric point, but its identity
  section is not an isomorphism, so it fails `hspecial`.
- The empty scheme cannot be a group scheme over the nonempty local spectrum:
  it lacks an identity section. This is intrinsic to `Grp`, not an added
  nonemptiness assumption on K. The zero ring is excluded by the usual local-ring
  definition already used by the node.
- The universe u is explicit and shared by A and its schemes. No independent
  smaller universe of test algebras is introduced, and no test-algebra hypothesis
  can become vacuous. All variables and universes are explicitly bound.

Searches actually run:

- `msearch.py`, LeanFinder: “A closed subgroup scheme of a split torus over a
  Noetherian local ring with trivial special fibre is trivial”. Eight hits,
  including `Scheme.default_asIdeal`, `Scheme.ker_toSpecΓ` and local cotangent
  space criteria; none states this theorem.
- `msearch.py`, Loogle: `GrpObj, IsLocalRing`. No hits; the service reports
  unknown identifier `GrpObj`, so this query provides no positive evidence.
- `msearch.py`, grep `splitTorus|torus.*subgroup|subgroup.*torus` in Mathlib
  AlgebraicGeometry: no hits.
- `msearch.py`, LeanSearch: “Closed subgroups of a split torus over a local ring
  are trivial when their special fibre is trivial”. Eight hits on topological
  `ClosedSubgroup` and `ClosedAddSubgroup`, not subgroup schemes.
- Project `rg` for torus/Torus/GroupScheme/group scheme/diagonalizable in
  `lean/WeilConjectures` and `lean/Sheaf`, followed by `def splitTorus`, found
  the existing field-only and arbitrary-ring definitions. I use the latter;
  the field-only `MultiplicativeType.splitTorus` would incorrectly restrict A.
- Project search for this item id found the parent theorem's proof docstring,
  not an existing statement. Name search for the chosen full declaration found
  no existing declaration in Mathlib, WeilConjectures or Sheaf.
- DAG definition-node search found `def-sfb-split-torus-over-ring`,
  `def-sfb-relative-split-torus`, and `def-sfb-ring-diagonalizable-group`; their
  source declarations were inspected. No new definition or dependency repair
  is needed. Only the owning ring split-torus node is added to `stmt_deps`.

Validation: `scompile.py` compiled this delivered module in required module mode,
against the published live build, with no errors or warnings (server library
compile 2.1 seconds). The only postponed theorem is the item's own theorem.
No statement correction or mathematical dispute was found.

## Second reading by Q29

Independent clause-by-clause reading of `AlgebraicGeometry.isIso_unit_of_splitTorus_closed_specialFiber`
against the node statement (written by the maintainer's reviewer, replacing the
earlier placeholder, which only said that no second worker had been started).

Node clauses and the Lean that renders each:

1. (A, m) is a commutative Noetherian local ring. This is `(A : Type u) [CommRing A]
   [IsNoetherianRing A] [IsLocalRing A]`. `IsNoetherianRing` is the recorded
   declaration of def-weil-pbc-noetherian-ring. Mathlib's local ring is nontrivial. Correct.
2. k = A/m and S = Spec A. These are `IsLocalRing.residue A` and `Spec (.of A)`, the
   recorded declaration of def-weil-affine-spectrum. Correct.
3. r ≥ 0. This is `(r : ℕ)`, and r = 0 is included. Correct.
4. T is Spec A[x_i,y_i]/(x_i y_i − 1) with group-like x_i, y_i, counit 1 and the
   inverse swapping x_i and y_i, and T = 1_S for r = 0. This is
   `RingGroupSchemes.splitTorus A r` (landed def-sfb-split-torus-over-ring). It is
   `Nat.rec (𝟙_ _) (multiplicative A ⊗ ·)`, the cartesian product in Over S of
   Spec (LaurentPolynomial A), with Mathlib's Hopf group law (T ↦ T⊗T, ε T = 1,
   S T = T⁻¹). The coordinate ring of the product is ⊗_A of the Laurent rings,
   which is A[x_i,y_i]/(x_i y_i − 1). For r = 0 it is the unit. The added stmt_dep
   def-sfb-split-torus-over-ring is landed and is the owner of this notion. Correct.
5. K is an S-group scheme. This is `K : Grp (Over (Spec (.of A)))`, which has all the
   group-object diagrams. Correct.
6. j : K → T is a homomorphism and a closed immersion. This is
   `j : K ⟶ splitTorus A r` in `Grp` together with `[IsClosedImmersion j.hom.hom.left]`,
   the recorded declaration of def-weil-closed-immersion. Correct.
7. Hypothesis: the identity section Spec k → K_k is an isomorphism. This is
   `IsIso (η[((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).mapGrp.obj K).X]).left`.
   Here Over.pullback is the scheme base change of def-pc-base-change (the
   BaseChangeConventions record points to Over.pullback), and mapGrp gives the
   induced group law. The source of η is 𝟙_(Over Spec k), whose `.left` is Spec k. So
   this is the actual unit section, as a scheme map. Correct.
8. Conclusion: the identity section S → K is an isomorphism. This is
   `IsIso (η[K.X]).left`. Correct, neither weaker nor stronger.
9. No flatness, completeness, finiteness or separatedness hypothesis appears. Correct.

Edge cases:
- r = 0: T is trivial, and the statement still holds.
- A a field: the hypothesis coincides with the conclusion.
- Nonreduced A and any residue characteristic are allowed. μ_p in characteristic p
  fails the hypothesis, so it is not a counterexample.
- There is a single universe u, and nothing is left unbound.
- The Noetherian hypothesis is unused by the proof but is part of the node, so it is
  kept.

Records: the item diff against live consists of the lean record and the added stmt_dep
def-sfb-split-torus-over-ring. The record statement equals the file signature
verbatim. The proof body is `sorry` only. The docstrings carry the source place,
`(blueprint: …)` and the six proof steps. No new definitions are introduced.

Searches: the side-live Sheaf/WeilConjectures trees contain no existing
declaration of this theorem. The parent CompleteLocalSplitTorusHomLift only cites
the item in its docstring.
