## Worker report

Item: `lemma-weil-pbc-chow-factorization`. Module:
`Sheaf.AlgebraicGeometry.ChowFactorization`; declaration:
`AlgebraicGeometry.exists_chow_factorization_of_isAffine`.
The module states one theorem with proof `sorry`, introduces no definitions, and
compiled cleanly on the server (1.7 seconds). The node statement is unchanged.

Clause-by-clause correspondence:

- Schemes `X`, `Y` and their named morphism `f` are the explicitly bound
  `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Properness of `f` is `[IsProper f]`; affineness of `Y` is `[IsAffine Y]`.
  There is no Noetherian or finite-presentation binder. Properness includes
  separatedness, universal closedness and locally finite type, as in the
  conventions node's Mathlib matches.
- The modification is the existential `T : Scheme.{u}` and its map is
  `π : T ⟶ X`. `IsProper π ∧ Surjective π` gives a proper surjection,
  where surjectivity is on the underlying topological spaces.
- The integer `n ≥ 0` is `n : ℕ`. The coordinate type is
  `ULift.{u} (Fin (n + 1))`, the finite set of n+1 homogeneous coordinates,
  so `ProjectiveSpace ... Y` is precisely the recorded definition of
  classical projective n-space over Y, not n-1-dimensional projective space.
- The existential `i : T ⟶ ProjectiveSpace ... Y` and
  `IsClosedImmersion i` give the required projective embedding.
- The structure morphism p is `ProjectiveSpace ... Y ↘ Y` (the first
  projection of the defining pullback). The equality is
  `π ≫ f = i ≫ ProjectiveSpace ... Y ↘ Y`; Lean composes left to right.
- The second conjunct quantifies over EVERY such choice T, n, π, i,
  its three properties, and its equation h, followed by an arbitrary
  `g : Y' ⟶ Y`. No affineness condition is imposed on Y'.
- `hx : IsPullback x f' f g` specifies any model X' of X ×_Y Y',
  with projection x and base-changed structure morphism f'.
  `ht : IsPullback t b (π ≫ f) g` specifies any model T' of T ×_Y Y',
  with projection t and structural morphism b. These are specifications
  of the pulled-back objects, not additional conditions on g or f.
  The standard `Limits.pullback` objects always give such squares.
- `hx.lift (t ≫ π) b ((Category.assoc t π f).trans ht.w)` is the canonical
  base change π' : T' → X'. Its two projections are t followed by π and b.
- `ProjectiveSpace.liftBaseChange b (t ≫ i) (...)` is the canonical map
  i' : T' → projective n-space over Y'. Its composites with
  `ProjectiveSpace.map ... g` and the structure morphism are t followed
  by i and b. This uses the recorded source's cartesian projective-space
  base-change interface. The equality argument is built entirely from
  ht.w, the original equation h, and associativity; no proof is postponed
  and no arbitrary map is substituted for the base-changed embedding.
- The final conjunction asserts `IsProper π'`, `Surjective π'`,
  `IsClosedImmersion i'`, and `π' ≫ f' = i' ≫ p'`. Thus the SAME n and
  pulled-back data meet all four required conditions.
- The final parenthetical sentence about a Noetherian base is a reference
  to the already recorded corollary, not an additional unconditional
  dense-open requirement in this node. The factorization here deliberately
  has no dense-open-isomorphism conclusion.

Dependencies read and used:

- `def-weil-pbc-scheme-conventions` is a convention-only record with no
  declaration. Its named Mathlib matches are used: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.IsAffine` (Mathlib.AlgebraicGeometry.AffineScheme),
  `AlgebraicGeometry.IsProper` (Mathlib.AlgebraicGeometry.Morphisms.Proper),
  `AlgebraicGeometry.Surjective` (Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap),
  and `AlgebraicGeometry.IsClosedImmersion`
  (Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion). Their defining
  signatures and docstrings were read in the pinned Mathlib source.
- `def-nagata-projective-space-base-change` records
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, declaration
  `AlgebraicGeometry.ProjectiveSpace`. Its full signature and docstring
  were read in slopmaster2. That module is imported; its canonical Over
  instance, `ProjectiveSpace.isPullback_map`, and
  `ProjectiveSpace.liftBaseChange` supply the structure and base-change maps.
- `cor-chow-lemma-proper` records
  `WeilConjectures.AlgebraicGeometry.ChowLemma`, declaration
  `AlgebraicGeometry.ChowModification.isClosedImmersion_toProjectiveSpace`.
  Its full signature and docstring were read: it is an instance with
  `[IsNoetherian S] [IsProper f]`, concerning the named Chow modification.
  It accounts for the node's parenthetical reference but cannot state the
  present theorem over an arbitrary affine base. Its module is not imported
  because no term of that declaration occurs in this signature.
- The canonical cartesian-square and lift interfaces are Mathlib's
  `CategoryTheory.IsPullback` and `CategoryTheory.IsPullback.lift`
  (Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs).
  Their signatures and the lift projection formulas were read.

Edge cases checked before writing:

- Empty X and empty Y are admitted; the modification may be empty.
  There is no nonempty-scheme or integral-scheme hypothesis.
- n = 0 means one homogeneous coordinate (`Fin 1`), hence the correct
  projective zero-space. It is not excluded. No empty coordinate index
  is forced even when X is empty.
- Non-Noetherian affine bases and proper morphisms not of finite
  presentation are admitted. Arbitrary base change may have non-affine
  Y', non-surjective g, or empty pullbacks; none is excluded.
- The original schemes and all diagrams live in one arbitrary universe u;
  `ULift.{u}` lifts the finite coordinate set to that universe. This
  places no restriction on the size of the base ring or schemes.
- IsAffine is the Mathlib condition that X → Spec Γ(X) is an isomorphism,
  equivalent to the convention's isomorphism to some affine spectrum.
- The canonical lifted maps are specified by both projections, so the
  stability clause does not accidentally allow a different embedding or
  a twist of its structural morphism over Y'.

Searches for an existing exact statement (2026-10-11):

- msearch.py, leanfinder: "Every proper morphism of schemes over an affine
  base admits a proper surjection from a scheme with a closed immersion
  into projective space". Eight hits: Proj properness/universal closedness,
  IsProper, isProper_iff, finite/proper equivalence, affine-space
  surjectivity. No Chow factorization statement.
- msearch.py, loogle: "AlgebraicGeometry.IsProper,
  AlgebraicGeometry.ProjectiveSpace". Zero hits; ProjectiveSpace is not
  known to the Mathlib search service.
- msearch.py, grep: `chow|Chow|chow_factorization` in AlgebraicGeometry.
  Zero Mathlib hits.
- msearch.py, leansearch: "A proper scheme over an affine base admits a
  proper surjection from a projective scheme without noetherian
  assumptions". Service unavailable (Internal Server Error); no verdict
  is inferred from this unavailable search.
- rg in WeilConjectures: `chow|Chow|chow_factorization` in ChowLemma.lean;
  read the Noetherian Chow modification declarations and their signatures.
  rg across WeilConjectures for
  `chow.*factor|factor.*chow|chow.*affine|projective.*proper.*surj` found
  ChowLemma/ClosedModel and the ProjectiveLine docstring explicitly naming
  this missing non-Noetherian factorization. Neither states this node.
- rg for the item's exact id, `chowFactorization|chow_factorization`, and
  the proposed declaration name across WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no existing declaration.
- rg for Chow/projective-space concepts in lean/Sheaf and enumeration of
  Chow/Factorization filenames found ChowRelativeAmple and ChowFiniteType.
  Read ChowFiniteType.lean in full: `exists_chow_finite_type` concerns
  separated finite-type maps over a qcqs base and concludes an IMMERSION,
  without this node's closed immersion or stability clause. It is related
  proof material but is not the same statement. ChowRelativeAmple concerns
  relative ampleness of an already supplied embedding.

No new definition nodes, dependency modules, statement correction, or
STATEMENT-DISPUTED issue is required. Every variable and universe is bound.

## Second reading by T1

I independently read the sandbox node and module, all three statement-dependency
nodes, the full upstream ProjectiveSpace module, the ChowModification signatures
and proper case in ChowLemma.lean, and Mathlib's property and pullback definitions.
The literature files are not populated in this clone. I read the local Stacks TeX
copies at /home/ubuntu/c1-stacks-review/limits.tex (section Variants of Chow's
Lemma, lemma-chow-finite-type and its proof) and morphisms.tex
(lemma-base-change-proper, lemma-base-change-closed-immersion, and
lemma-base-change-surjective). The approximation/envelope proof has only a qcqs
base and a separated finite-type morphism as hypotheses; the item's affine base
and proper morphism supply these. No global Noetherian assumption is inherited.

My checklist of the node, with its Lean counterpart and verdict:

1. Objects: schemes X, Y and named f : X → Y are `{X Y : Scheme.{u}}`
   and `(f : X ⟶ Y)`. Exact. There is no field, ring, characteristic or
   nonemptiness restriction.
2. Hypotheses: f proper and Y affine are `[IsProper f] [IsAffine Y]`.
   Exact. I read IsProper's separated/universally-closed/locally-finite-type
   fields; universal closedness supplies quasi-compactness, so this is the
   convention's finite-type properness. IsAffine uses the canonical map to
   Spec of global sections, equivalently being an affine spectrum.
3. Modification: `∃ (T : Scheme.{u}) ... (π : T ⟶ X)` introduces the
   required scheme and map; `IsProper π ∧ Surjective π` says exactly proper
   and surjective on underlying spaces. Exact.
4. Dimension: `n : ℕ` covers every integer n ≥ 0, and
   `ProjectiveSpace (ULift.{u} (Fin (n + 1))) Y` has n+1 homogeneous
   coordinates. I read the definition and its first-projection Over instance:
   this is Y times the integral Proj model over Spec Z, as the dependency
   specifies. Exact; no alternate projective-space notion is introduced.
5. Embedding: the existential `i : T ⟶ ProjectiveSpace ... Y` and
   `IsClosedImmersion i` give the required closed immersion. Mathlib's
   closed embedding plus surjective stalk maps is the intended notion. Exact.
6. Equality: `π ≫ f = i ≫ ProjectiveSpace ... Y ↘ Y` is f composed with π
   equal to p composed with i, with p the recorded first projection. Exact.
7. Absence of extra hypotheses: no Noetherian or finite-presentation binder,
   including on π, appears. Exact.
8. Stability: the second conjunct quantifies over all T,n,π,i with the three
   properties and their equation h, then arbitrary Y' and g : Y' → Y.
   `hx : IsPullback x f' f g` and `ht : IsPullback t b (π ≫ f) g`
   specify arbitrary models X' and T' of the two fibre products. These
   square hypotheses specify the pulled-back data, rather than restrict g;
   canonical pullbacks supply them for every g. Exact quantifier order.
9. Pulled-back maps: `hx.lift (t ≫ π) b ...` has projections t ≫ π and b,
   so is precisely π'. `ProjectiveSpace.liftBaseChange b (t ≫ i) ...`
   has projections t ≫ i and b to the original projective space and Y',
   by the upstream liftBaseChange_map/over signatures and isPullback_map.
   Its compatibility proof uses ht.w and h in the correct direction.
   Thus i' is the actual base change, even for nonseparated g. Exact.
10. Stability conclusion: `IsProper π' ∧ Surjective π' ∧
    IsClosedImmersion i' ∧ π' ≫ f' = i' ≫ p'` retains the same n and all
    four clauses. Exact. The final identity is a stated clause, as in the
    node, rather than a new conclusion.
11. The parenthetical Noetherian sentence points to cor-chow-lemma-proper;
    it is not an unconditional dense-open requirement here. I read its
    recorded `ChowModification.isClosedImmersion_toProjectiveSpace`, which
    assumes `[IsNoetherian S] [IsProper f]`, and the companion proper,
    surjective, over-identity and dense-open signatures. This special case
    cannot replace the present arbitrary-affine-base theorem. No extra
    dependency module is needed for this explanatory reference.

Edge cases: empty X, empty affine Y, zero-ring affine bases, and empty
pullbacks are allowed. There is no zero-object requirement on the category
of schemes. n = 0 gives Fin 1, not empty homogeneous coordinates; n < 0 is
outside the node. No characteristic is constrained. One arbitrary universe u
contains the whole finite diagram; ULift puts its finite coordinate index
in that universe. This includes arbitrary ring sizes and does not introduce
an independent small test-object universe. Arbitrary g need not be affine,
proper, surjective, or separated. In particular the upstream instance for a
closed-immersion lift along separated g is not being mistaken for the general
base-change assertion; that assertion is stated here using the cartesian
square of T'.

Independent searches with different wording:

- msearch leanfinder: "Chow lemma projective domination of a proper scheme
  over a ring": eight Proj/properness/construction results, no domination
  statement.
- msearch loogle: "AlgebraicGeometry.IsProper,
  AlgebraicGeometry.Surjective": zero hits.
- msearch grep: "dominated|domination|Chow|chow": unrelated domination
  results; direct rg restricted to Mathlib/AlgebraicGeometry found no Chow
  or projective-domination declaration.
- rg across WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `exists_chow_factorization|chowFactorization|chow_factorization|projective.*surject|surject.*projective`
  found only related material, not this declaration. I opened
  lean/Sheaf/AlgebraicGeometry/ChowFiniteType.lean: its theorem supplies an
  immersion over a qcqs base, not this closed-immersion theorem with its
  full stability conjunct. Upstream ChowLemma is restricted to a Noetherian
  base. These are usable proof dependencies, not an existing exact statement.

No mathematical or mechanical mismatch was found. I changed only this report,
leaving the correct Lean and node signature intact. There are no new nodes,
dependency modules, private copies, definitions with sorry data, or statement
corrections to review. The module and declaration docstrings give the source
and blueprint id; the declaration docstring follows all seven proof steps.
The sole theorem remains `by sorry`; its compatibility terms are structural
proofs, not additional proved declarations. Variables and universe u are bound,
imports are used, and no file-local notation or instances are introduced.
Server single-file compilation via scompile.py completed in 2.0 seconds with
exit code 0 and no warnings. The node's lean.statement matches the complete
signature in the module verbatim.
